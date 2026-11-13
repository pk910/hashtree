import Hashtree.Asm.Arm
import Hashtree.Asm.ArmRun

/-!
# Depth-1 call layer for the AArch64 wrapper streams

The AArch64 instruction model has two ways of leaving a function: `bTail` (a tail call: the
callee returns to the caller's caller) and `ret` (return to the address in `x30`).  The Go
facing wrappers call the kernels with `BL`, which does not appear in the kernel models.

This module adds the missing step *outside* `Instr`, so the kernel instruction set and every
existing proof are unchanged:

* `WInstr` is either a kernel instruction or a call site;
* `execW` executes a call site by leaving the return pc in `x30` and the callee's name in
  `tail` (exactly the state `BL` leaves behind);
* `runW` is the fetch-execute loop over `WInstr`;
* `runCall` follows the callee chain (including the `neon_x4 -> neon_x1` tail), then resumes
  the wrapper at the return pc recorded in `x30` when the callee executes `ret`.

The wrapper stream of upstream #79 (`wrapper_arm64.s`) is `neonPath` / `shaniPath` below:
only the NEON path moves `SP` by 2048; the `sha_x1` path runs at the unmoved `SP` and its
32-byte below-`SP` write is deliberate.
-/

namespace Hashtree.Asm.ArmCall
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun

/-- A wrapper instruction: a kernel instruction or a `BL` call site. -/
inductive WInstr where
  | ins (i : Instr)
  | call (ret : Nat) (name : String)
  deriving DecidableEq, Repr, Inhabited

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- The state a `BL` leaves behind: the return pc in `x30` (region `rRet`). -/
def setRet (s : State α γ) (ret : Nat) : State α γ :=
  s.setG 30 (.ptr ⟨rRet, Ctl.ofInt (ret : Int)⟩)

/-- One wrapper step.  A call site halts the wrapper with the callee's name in `tail`; the
callee's own `ret` is what brings control back (see `runCall`). -/
def execW (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : WInstr)
    (s : State α γ) : State α γ :=
  if s.halted then s
  else match i with
    | .ins i => Arm.exec ro mem0 orc i s
    | .call ret name => { setRet s ret with halted := true, tail := some name }

/-- Fetch-execute `n` wrapper steps. -/
def runW (prog : Array WInstr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    Nat → State α γ → State α γ
  | 0, s => s
  | n + 1, s =>
    if s.halted then s
    else match prog[s.pc]? with
      | some i => runW prog ro mem0 orc n (execW ro mem0 orc i s)
      | none => s.fail "pc out of program"

theorem runW_zero (prog : Array WInstr) (ro : Region) (mem0 : Addr γ → Cell α γ)
    (orc : Nat → Bool) (s : State α γ) : runW prog ro mem0 orc 0 s = s := rfl

theorem runW_succ (prog : Array WInstr) (ro : Region) (mem0 : Addr γ → Cell α γ)
    (orc : Nat → Bool) (n : Nat) (s : State α γ) (i : WInstr)
    (h : s.halted = false) (hp : prog[s.pc]? = some i) :
    runW prog ro mem0 orc (n + 1) s = runW prog ro mem0 orc n (execW ro mem0 orc i s) := by
  simp [runW, h, hp]

theorem execW_call_tail (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (ret : Nat) (name : String) (s : State α γ) (h : s.halted = false) :
    (execW ro mem0 orc (.call ret name) s).tail = some name := by
  simp [execW, h]

theorem execW_call_halted (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (ret : Nat) (name : String) (s : State α γ) (h : s.halted = false) :
    (execW ro mem0 orc (.call ret name) s).halted = true := by
  simp [execW, h]

end

/-! ## The shipped #79 wrapper streams -/

/-- NEON path: `ADD $2048, RSP; BL hashtree_sha256_neon_x4; SUB $2048, RSP; RET`. -/
def neonPath : Array WInstr :=
  #[.ins (.addi 31 31 2048), .call 2 "hashtree_sha256_neon_x4",
    .ins (.subi 31 31 2048), .ins .ret]

/-- shani path: `BL hashtree_sha256_sha_x1; RET`, at the unmoved `SP`. -/
def shaniPath : Array WInstr :=
  #[.call 1 "hashtree_sha256_sha_x1", .ins .ret]

theorem neonPath_0 : neonPath[0]? = some (.ins (.addi 31 31 2048)) := by decide
theorem neonPath_1 : neonPath[1]? = some (.call 2 "hashtree_sha256_neon_x4") := by decide
theorem neonPath_2 : neonPath[2]? = some (.ins (.subi 31 31 2048)) := by decide
theorem neonPath_3 : neonPath[3]? = some (.ins .ret) := by decide
theorem neonPath_size : neonPath.size = 4 := by decide

theorem shaniPath_0 : shaniPath[0]? = some (.call 1 "hashtree_sha256_sha_x1") := by decide
theorem shaniPath_1 : shaniPath[1]? = some (.ins .ret) := by decide
theorem shaniPath_size : shaniPath.size = 2 := by decide

/-- The wrapper run with at most one call in flight: run the wrapper, and when it stops at a
call site, follow the callee chain (including the `neon_x4 -> neon_x1` tail), then resume the
wrapper at the return pc the callee's `ret` found in `x30`.  A wrapper `ret` (or an error)
ends the run. -/
def runCall (progs : List Prog) (wp : Array WInstr) (ro : Region)
    (m0 : Addr Int → Cell W32 Int) (fuel hops : Nat) : Nat → CS → CS
  | 0, s => s
  | n + 1, s =>
    let s1 := runW wp ro m0 (fun _ => false) 1 s
    if s1.halted && s1.err == none && s1.tail.isSome then
      let name := s1.tail.getD ""
      let (sc, _) := runChain progs m0 fuel hops name
        { s1 with pc := 0, halted := false, tail := none }
      (match sc.getG 30 with
      | .ptr a =>
        if sc.err == none && sc.halted && sc.tail == none && a.region == rRet then
          runCall progs wp ro m0 fuel hops n
            { sc with pc := a.off.toNat, halted := false, tail := none }
        else sc
      | .num _ _ => sc)
    else
      runCall progs wp ro m0 fuel hops n s1


/-! ## Local `gpr` length obligations -/

theorem getD_set_self {b : Type} (l : List b) (i : Nat) (v d : b) (h : i < l.length) :
    (l.set i v).getD i d = v := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < l.length := by simpa using h
      simpa [List.set, List.getD] using ih i h'

theorem getD_set_of_ne {b : Type} (l : List b) (i j : Nat) (v d : b) (h : i ≠ j) :
    (l.set i v).getD j d = l.getD j d := by
  induction l generalizing i j with
  | nil => rfl
  | cons a t ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ j => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        have h' : i ≠ j := fun he => h (by rw [he])
        simpa [List.set, List.getD] using ih i j h'

theorem setG_getG_self {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (s : State α γ) (i : Nat) (v : Val α γ) (h : i < s.gpr.length) :
    (s.setG i v).getG i = v :=
  getD_set_self s.gpr i v _ h

theorem setG_getG_ne {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (s : State α γ) (i j : Nat) (v : Val α γ) (h : i ≠ j) :
    (s.setG i v).getG j = s.getG j :=
  getD_set_of_ne s.gpr i j v _ h

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

theorem next_getG (s : State α γ) (i : Nat) : s.next.getG i = s.getG i := rfl

theorem exec_addi_sp (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (s : State α γ) (a : Addr γ) (k : Nat) (h : s.halted = false)
    (hs : s.getG 31 = .ptr a) (h31 : 31 < s.gpr.length) :
    (Arm.exec ro mem0 orc (.addi 31 31 k) s).getG 31 = .ptr (a.plusI (k : Int)) := by
  have hg : getC s 31 = .ok a := by
    simp only [getC, hs]
    rfl
  have hstep : Arm.exec ro mem0 orc (.addi 31 31 k) s
      = (s.setG 31 (.ptr (a.plusI (k : Int)))).next := by
    simp only [Arm.exec, h, hg, okOr]
    rfl
  rw [hstep, next_getG]
  exact setG_getG_self s 31 _ h31

theorem exec_subi_sp (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (s : State α γ) (a : Addr γ) (k : Nat) (h : s.halted = false)
    (hs : s.getG 31 = .ptr a) (h31 : 31 < s.gpr.length) :
    (Arm.exec ro mem0 orc (.subi 31 31 k) s).getG 31 = .ptr (a.plusI (-(k : Int))) := by
  have hg : getC s 31 = .ok a := by
    simp only [getC, hs]
    rfl
  have hstep : Arm.exec ro mem0 orc (.subi 31 31 k) s
      = (s.setG 31 (.ptr (a.plusI (-(k : Int))))).next := by
    simp only [Arm.exec, h, hg, okOr]
    rfl
  rw [hstep, next_getG]
  exact setG_getG_self s 31 _ h31

/-! ## General instruction steps

The write itself does not need the register file length; reading the written value back does
(`exec_addi_sp` / `exec_subi_sp`). -/

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

theorem exec_addi_eq (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (s : State α γ) (a : Addr γ) (d n k : Nat) (h : s.halted = false)
    (hs : s.getG n = .ptr a) :
    Arm.exec ro mem0 orc (.addi d n k) s = (s.setG d (.ptr (a.plusI (k : Int)))).next := by
  have hg : getC s n = .ok a := by
    simp only [getC, hs]
    rfl
  simp only [Arm.exec, h, hg, okOr]
  rfl

theorem exec_subi_eq (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (s : State α γ) (a : Addr γ) (d n k : Nat) (h : s.halted = false)
    (hs : s.getG n = .ptr a) :
    Arm.exec ro mem0 orc (.subi d n k) s = (s.setG d (.ptr (a.plusI (-(k : Int))))).next := by
  have hg : getC s n = .ok a := by
    simp only [getC, hs]
    rfl
  simp only [Arm.exec, h, hg, okOr]
  rfl

theorem exec_ret_halt (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (s : State α γ) (c : γ) (h : s.halted = false) (h30 : s.getG 30 = .ptr ⟨rRet, c⟩) :
    Arm.exec ro mem0 orc .ret s = { s with halted := true } := by
  simp only [Arm.exec, h, h30, halt, okOr]
  rfl

end

end


/-! ## Entry state of the wrapper and the address arithmetic -/

theorem addr_plusI_int (r : Region) (o n : Int) :
    (⟨r, o⟩ : Addr Int).plusI n = ⟨r, o + n⟩ := rfl

theorem entry_halted (count : Nat) (sp0 : Int) : (entry count sp0).halted = false := by
  simp [entry]

theorem entry_pc (count : Nat) (sp0 : Int) : (entry count sp0).pc = 0 := by
  simp [entry]

theorem entry_err (count : Nat) (sp0 : Int) : (entry count sp0).err = none := by
  simp [entry]

theorem entry_tail (count : Nat) (sp0 : Int) : (entry count sp0).tail = none := by
  simp [entry]

theorem entry_gpr_length (count : Nat) (sp0 : Int) : (entry count sp0).gpr.length = 32 := by
  simp [entry, List.length_set, List.length_map, List.length_range]

theorem entry_getG31 (count : Nat) (sp0 : Int) :
    (entry count sp0).getG 31 = .ptr ⟨rStack, sp0⟩ := by
  simp only [entry, State.getG, List.length_set, List.length_map, List.length_range]
  exact getD_set_self _ 31 _ _ (by simp)

theorem exec_addi_entry (m0 : Addr Int → Cell W32 Int) (count : Nat) (sp0 : Int) :
    Arm.exec rNum m0 (fun _ => false) (.addi 31 31 2048) (entry count sp0)
      = (State.setG (entry count sp0) 31 (.ptr ⟨rStack, sp0 + 2048⟩)).next := by
  have hcast : sp0 + ((2048 : Nat) : Int) = sp0 + 2048 := rfl
  have h := exec_addi_eq rNum m0 (fun _ => false) (entry count sp0) ⟨rStack, sp0⟩ 31 31 2048
    (entry_halted count sp0) (entry_getG31 count sp0)
  rw [addr_plusI_int, hcast] at h
  exact h


/-! ## Wrapper #79: the shipped stream, premises-first -/

/-- The state the wrapper hands `hashtree_sha256_neon_x4`: the `ADD $2048` has run and `x30`
holds the return pc 2.  `SP = sp0 + 2048` (the wrapper's own 2048 bytes are below it). -/
def neonEntry (count : Nat) (sp0 : Int) : CS :=
  { setRet ((State.setG (entry count sp0) 31 (.ptr ⟨rStack, sp0 + 2048⟩)).next) 2
    with pc := 0, halted := false, tail := none }

/-- The state the wrapper hands `hashtree_sha256_sha_x1`: `SP` is unmoved (the kernel's 32-byte
below-`SP` use is inside its own frame) and `x30` holds the return pc 1. -/
def shaEntry (count : Nat) (sp0 : Int) : CS :=
  { setRet (entry count sp0) 1 with pc := 0, halted := false, tail := none }

theorem runW_one (prog : Array WInstr) (ro : Region) (m0 : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (s : CS) (i : WInstr) (h : s.halted = false)
    (hp : prog[s.pc]? = some i) :
    runW prog ro m0 orc 1 s = execW ro m0 orc i s := by
  have h1 := runW_succ prog ro m0 orc 0 s i h hp
  simpa only [runW_zero] using h1

/-- One unfolding of `runCall` (definitional). -/
theorem runCall_succ (progs : List Prog) (wp : Array WInstr) (ro : Region)
    (m0 : Addr Int → Cell W32 Int) (fuel hops n : Nat) (s : CS) :
    runCall progs wp ro m0 fuel hops (n + 1) s =
      (let s1 := runW wp ro m0 (fun _ => false) 1 s
       if s1.halted && s1.err == none && s1.tail.isSome then
         let name := s1.tail.getD ""
         let (sc, _) := runChain progs m0 fuel hops name
           { s1 with pc := 0, halted := false, tail := none }
         (match sc.getG 30 with
         | .ptr a =>
           if sc.err == none && sc.halted && sc.tail == none && a.region == rRet then
             runCall progs wp ro m0 fuel hops n
               { sc with pc := a.off.toNat, halted := false, tail := none }
           else sc
         | .num _ _ => sc)
       else
         runCall progs wp ro m0 fuel hops n s1) := rfl

/-- The NEON path of the shipped wrapper, with the two kernel legs as hypotheses.

`hsc` is the `neon_x4 -> neon_x1` tail contract: `hashtree_sha256_neon_x4` run from
`neonEntry` (i.e. `SP` already 2048 above the wrapper's entry `SP`, `x30 = <rRet, 2>`) tails
into `hashtree_sha256_sha_x1` and its `ret` leaves `x30 = <rRet, 2>`; the run must finish with
no error, `halted`, no pending tail, and `SP` back at `sp0 + 2048` (each kernel's own frame is
balanced).  The wrapper then executes exactly `SUB $2048; RET`. -/
theorem wrapper_neon (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel hops : Nat)
    (count : Nat) (sp0 : Int) (sc : CS) (path : List String)
    (hsc : runChain progs m0 fuel hops "hashtree_sha256_neon_x4" (neonEntry count sp0)
      = (sc, path))
    (herr : sc.err = none) (hHalt : sc.halted = true) (hTail : sc.tail = none)
    (h30 : sc.getG 30 = .ptr ⟨rRet, (2 : Int)⟩)
    (h31 : sc.getG 31 = .ptr ⟨rStack, sp0 + 2048⟩)
    (hgl : 31 < sc.gpr.length) :
    ∃ sf, runCall progs neonPath rNum m0 fuel hops 4 (entry count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ := by
  let E : CS := entry count sp0
  let A : CS := (State.setG E 31 (.ptr ⟨rStack, sp0 + 2048⟩)).next
  let C : CS := { setRet A 2 with halted := true, tail := some "hashtree_sha256_neon_x4" }
  let D : CS := { sc with pc := 2, halted := false, tail := none }
  let a31 : Addr Int := ⟨rStack, sp0 + 2048⟩
  let F : CS := (State.setG D 31 (.ptr (a31.plusI (-((2048 : Nat) : Int))))).next
  let G : CS := { F with halted := true }
  have hE : runW neonPath rNum m0 (fun _ => false) 1 E = A := by
    rw [runW_one neonPath rNum m0 (fun _ => false) E (.ins (.addi 31 31 2048))
      (by rfl) neonPath_0]
    simp only [execW, show E.halted = false from rfl, if_false]
    exact exec_addi_entry m0 count sp0
  have hA : runW neonPath rNum m0 (fun _ => false) 1 A = C := by
    rw [runW_one neonPath rNum m0 (fun _ => false) A (.call 2 "hashtree_sha256_neon_x4")
      (by rfl) neonPath_1]
    simp only [execW, show A.halted = false from rfl, if_false]
    rfl
  have hD31 : D.getG 31 = .ptr a31 := by
    show sc.getG 31 = .ptr a31
    exact h31
  have hDgl : 31 < D.gpr.length := by
    show 31 < sc.gpr.length
    exact hgl
  have hD : runW neonPath rNum m0 (fun _ => false) 1 D = F := by
    rw [runW_one neonPath rNum m0 (fun _ => false) D (.ins (.subi 31 31 2048))
      (by rfl) neonPath_2]
    simp only [execW, show D.halted = false from rfl, if_false]
    exact exec_subi_eq rNum m0 (fun _ => false) D a31 31 31 2048 (by rfl) hD31
  have hF30 : F.getG 30 = .ptr ⟨rRet, (2 : Int)⟩ := by
    have hne : (31 : Nat) ≠ 30 := by decide
    show (State.setG D 31 (.ptr (a31.plusI (-((2048 : Nat) : Int))))).next.getG 30
      = .ptr ⟨rRet, (2 : Int)⟩
    rw [next_getG, setG_getG_ne _ 31 30 _ hne]
    exact h30
  have hG : runW neonPath rNum m0 (fun _ => false) 1 F = G := by
    rw [runW_one neonPath rNum m0 (fun _ => false) F (.ins .ret) (by rfl) neonPath_3]
    simp only [execW, show F.halted = false from rfl, if_false]
    exact exec_ret_halt rNum m0 (fun _ => false) F (2 : Int) (by rfl) hF30
  have step1 : runCall progs neonPath rNum m0 fuel hops 4 E
      = runCall progs neonPath rNum m0 fuel hops 3 A := by
    change runCall progs neonPath rNum m0 fuel hops (3 + 1) E
      = runCall progs neonPath rNum m0 fuel hops 3 A
    rw [runCall_succ (n := 3), hE]
    have hc : (A.halted && A.err == none && A.tail.isSome) = false := by rfl
    simp only [hc, Bool.false_eq_true, if_false]
  have hneon : ({ C with pc := 0, halted := false, tail := none } : CS)
      = neonEntry count sp0 := rfl
  have step2 : runCall progs neonPath rNum m0 fuel hops 3 A
      = runCall progs neonPath rNum m0 fuel hops 2 D := by
    change runCall progs neonPath rNum m0 fuel hops (2 + 1) A
      = runCall progs neonPath rNum m0 fuel hops 2 D
    rw [runCall_succ (n := 2), hA]
    have hc : (C.halted && C.err == none && C.tail.isSome) = true := by rfl
    simp only [hc, if_true]
    rw [hneon]
    simp only [C, setRet, Option.getD_some]
    rw [hsc]
    simp only [Prod.fst, h30]
    rw [herr, hHalt, hTail]
    have hc2 : ((none : Option String) == none && true && (none : Option String) == none
        && (⟨rRet, (2 : Int)⟩ : Addr Int).region == rRet) = true := by decide
    simp only [hc2, if_true]
    have h2 : ((⟨rRet, (2 : Int)⟩ : Addr Int).off).toNat = 2 := rfl
    rw [h2]
    simp [D, herr]
  have step3 : runCall progs neonPath rNum m0 fuel hops 2 D
      = runCall progs neonPath rNum m0 fuel hops 1 F := by
    change runCall progs neonPath rNum m0 fuel hops (1 + 1) D
      = runCall progs neonPath rNum m0 fuel hops 1 F
    rw [runCall_succ (n := 1), hD]
    have hc : (F.halted && F.err == none && F.tail.isSome) = false := by rfl
    simp only [hc, Bool.false_eq_true, if_false]
  have step4 : runCall progs neonPath rNum m0 fuel hops 1 F
      = runCall progs neonPath rNum m0 fuel hops 0 G := by
    change runCall progs neonPath rNum m0 fuel hops (0 + 1) F
      = runCall progs neonPath rNum m0 fuel hops 0 G
    rw [runCall_succ (n := 0), hG]
    have hc : (G.halted && G.err == none && G.tail.isSome) = false := by
      rw [show G.halted = true from rfl, show G.tail = none from rfl]
      simp only [Bool.true_and, Option.isSome_none, Bool.and_false]
    simp only [hc, Bool.false_eq_true, if_false]
  have hF31 : F.getG 31 = .ptr (a31.plusI (-((2048 : Nat) : Int))) := by
    show (State.setG D 31 (.ptr (a31.plusI (-((2048 : Nat) : Int))))).next.getG 31
      = .ptr (a31.plusI (-((2048 : Nat) : Int)))
    rw [next_getG]
    exact setG_getG_self D 31 _ (by simpa using hDgl)
  have haddr : a31.plusI (-((2048 : Nat) : Int)) = ⟨rStack, sp0⟩ := by
    show (⟨rStack, sp0 + 2048⟩ : Addr Int).plusI (-((2048 : Nat) : Int)) = ⟨rStack, sp0⟩
    rw [addr_plusI_int]
    congr 1
    omega
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step1, step2, step3, step4]
    rfl
  · exact herr
  · rfl
  · rfl
  · show F.getG 31 = .ptr ⟨rStack, sp0⟩
    rw [hF31, haddr]


/-- The `sha_x1` path of the shipped wrapper, with the kernel leg as hypothesis.

`hsc` is the `sha_x1` contract: the kernel runs at the wrapper's own `SP` (its 32-byte
below-`SP` use is inside its frame), and its `ret` leaves `x30 = <rRet, 1>` and `SP` unchanged.
The wrapper then executes only `RET`. -/
theorem wrapper_sha (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel hops : Nat)
    (count : Nat) (sp0 : Int) (sc : CS) (path : List String)
    (hsc : runChain progs m0 fuel hops "hashtree_sha256_sha_x1" (shaEntry count sp0)
      = (sc, path))
    (herr : sc.err = none) (hHalt : sc.halted = true) (hTail : sc.tail = none)
    (h30 : sc.getG 30 = .ptr ⟨rRet, (1 : Int)⟩)
    (h31 : sc.getG 31 = .ptr ⟨rStack, sp0⟩) :
    ∃ sf, runCall progs shaniPath rNum m0 fuel hops 2 (entry count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ := by
  let E : CS := entry count sp0
  let C : CS := { setRet E 1 with halted := true, tail := some "hashtree_sha256_sha_x1" }
  let D : CS := { sc with pc := 1, halted := false, tail := none }
  let G : CS := { D with halted := true }
  have hE : runW shaniPath rNum m0 (fun _ => false) 1 E = C := by
    rw [runW_one shaniPath rNum m0 (fun _ => false) E (.call 1 "hashtree_sha256_sha_x1")
      (by rfl) shaniPath_0]
    simp only [execW, show E.halted = false from rfl]
    rfl
  have hsha : ({ C with pc := 0, halted := false, tail := none } : CS) = shaEntry count sp0 := rfl
  have step1 : runCall progs shaniPath rNum m0 fuel hops 2 E
      = runCall progs shaniPath rNum m0 fuel hops 1 D := by
    change runCall progs shaniPath rNum m0 fuel hops (1 + 1) E
      = runCall progs shaniPath rNum m0 fuel hops 1 D
    rw [runCall_succ (n := 1), hE]
    have hc : (C.halted && C.err == none && C.tail.isSome) = true := by rfl
    simp only [hc, if_true]
    rw [hsha]
    simp only [C, setRet, Option.getD_some]
    rw [hsc]
    simp only [Prod.fst, h30]
    rw [herr, hHalt, hTail]
    have hc2 : ((none : Option String) == none && true && (none : Option String) == none
        && (⟨rRet, (1 : Int)⟩ : Addr Int).region == rRet) = true := by decide
    simp only [hc2, if_true]
    have h1 : ((⟨rRet, (1 : Int)⟩ : Addr Int).off).toNat = 1 := rfl
    rw [h1]
    simp [D, herr]
  have hD30 : D.getG 30 = .ptr ⟨rRet, (1 : Int)⟩ := by
    show sc.getG 30 = .ptr ⟨rRet, (1 : Int)⟩
    exact h30
  have hD : runW shaniPath rNum m0 (fun _ => false) 1 D = G := by
    rw [runW_one shaniPath rNum m0 (fun _ => false) D (.ins .ret) (by rfl) shaniPath_1]
    simp only [execW, show D.halted = false from rfl]
    exact exec_ret_halt rNum m0 (fun _ => false) D (1 : Int) (by rfl) hD30
  have step2 : runCall progs shaniPath rNum m0 fuel hops 1 D
      = runCall progs shaniPath rNum m0 fuel hops 0 G := by
    change runCall progs shaniPath rNum m0 fuel hops (0 + 1) D
      = runCall progs shaniPath rNum m0 fuel hops 0 G
    rw [runCall_succ (n := 0), hD]
    have hc : (G.halted && G.err == none && G.tail.isSome) = false := by
      rw [show G.halted = true from rfl, show G.tail = none from rfl]
      simp only [Bool.true_and, Option.isSome_none, Bool.and_false]
    simp only [hc, Bool.false_eq_true, if_false]
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step1, step2]
    rfl
  · exact herr
  · rfl
  · rfl
  · show sc.getG 31 = .ptr ⟨rStack, sp0⟩
    exact h31

/-! ## Chain contracts: the x4 tail cut and the x1 exit cut -/

/-- One hop of `runChain`: when the program's own `run` ends with a tail call to `t` and no
error, the chain continues in `t` from the tail-entry state, with the program's name prepended
to the path.  This is the glue that turns a per-kernel exit cut into a chain premise. -/
theorem runChain_tail (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel hops : Nat) (name t : String) (p : Prog) (s scut : CS)
    (hf : progs.find? (·.name = name) = some p)
    (hrun : run p.code p.ro m0 (fun _ => false) fuel s = scut)
    (htail : scut.tail = some t) (herr : scut.err = none) :
    runChain progs m0 fuel (hops + 1) name s
      = ((runChain progs m0 fuel hops t
            { scut with pc := 0, halted := false, tail := none }).1,
         name :: (runChain progs m0 fuel hops t
            { scut with pc := 0, halted := false, tail := none }).2) := by
  simp only [runChain, hf, hrun, htail, herr]

/-- A chain of one hop: a program that returns (no pending tail) finishes its own chain. -/
theorem runChain_single (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel : Nat)
    (name : String) (p : Prog) (s sc : CS)
    (hf : progs.find? (·.name = name) = some p)
    (hrun : run p.code p.ro m0 (fun _ => false) fuel s = sc)
    (htail : sc.tail = none) :
    runChain progs m0 fuel 1 name s = (sc, [name]) := by
  simp only [runChain, hf, hrun, htail]

/-- The exit cut of `hashtree_sha256_neon_x4`: the state its `bTail hashtree_sha256_neon_x1`
leaves behind.  The x4 frame is balanced before the branch (the `ADD $1024` at the exit), so
the newly entered `neon_x1` sees the same `SP` the wrapper handed `neon_x4` (`sp0 + 2048`), and
`x30` still holds the wrapper's return marker. -/
structure NeonX4Cut (sp0 : Int) (scut : CS) : Prop where
  halted : scut.halted = true
  /-- the x4 leaves itself for the x1 kernel -/
  tail : scut.tail = some "hashtree_sha256_neon_x1"
  err : scut.err = none
  /-- the x4 frame is balanced at the cut: `SP` is the x4 entry `SP` -/
  sp : scut.getG 31 = .ptr ⟨rStack, sp0 + 2048⟩

/-- The exit cut of the `neon_x1` leg entered from the x4 cut: the NEON chain finished cleanly
with the wrapper's return marker and `SP` back at the moved (x4 entry) `SP`. -/
structure NeonChainExit (sp0 : Int) (sc : CS) : Prop where
  err : sc.err = none
  halted : sc.halted = true
  tail : sc.tail = none
  ret : sc.getG 30 = .ptr ⟨rRet, (2 : Int)⟩
  sp : sc.getG 31 = .ptr ⟨rStack, sp0 + 2048⟩
  frame : 31 < sc.gpr.length

/-- The x4-tail contract: the `neon_x4` chain splits at its tail cut into the `neon_x1` chain
run from that cut.  This is the `neon_x4 -> neon_x1` composition, with the cut state supplied
by the x4 stream proof and the x1 tree instantiated from the fixed cut. -/
theorem neon_x4_chain_of_cut (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel hops : Nat) (count : Nat) (sp0 : Int) (x4 : Prog) (scut sc : CS) (path : List String)
    (hf : progs.find? (·.name = "hashtree_sha256_neon_x4") = some x4)
    (hrun : run x4.code x4.ro m0 (fun _ => false) fuel (neonEntry count sp0) = scut)
    (hcut : NeonX4Cut sp0 scut)
    (hx1 : runChain progs m0 fuel hops "hashtree_sha256_neon_x1"
             { scut with pc := 0, halted := false, tail := none } = (sc, path)) :
    runChain progs m0 fuel (hops + 1) "hashtree_sha256_neon_x4" (neonEntry count sp0)
      = (sc, "hashtree_sha256_neon_x4" :: path) := by
  rw [runChain_tail progs m0 fuel hops "hashtree_sha256_neon_x4"
    "hashtree_sha256_neon_x1" x4 (neonEntry count sp0) scut hf hrun hcut.tail hcut.err, hx1]

/-- The NEON path of #79 with the chain split at the kernels' cut.  Premises: the x4 stream runs
from `neonEntry` to its exit cut (frame balanced at `sp0 + 2048`), and the `neon_x1` leg runs
from that cut to the clean chain exit.  Conclusion: the shipped wrapper completes with `SP`
restored to `sp0` by its own `SUB $2048`. -/
theorem wrapper_neon_of_cut (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel hops : Nat) (count : Nat) (sp0 : Int) (x4 : Prog) (scut sc : CS)
    (path : List String)
    (hf : progs.find? (·.name = "hashtree_sha256_neon_x4") = some x4)
    (hrun : run x4.code x4.ro m0 (fun _ => false) fuel (neonEntry count sp0) = scut)
    (hcut : NeonX4Cut sp0 scut)
    (hx1 : runChain progs m0 fuel hops "hashtree_sha256_neon_x1"
             { scut with pc := 0, halted := false, tail := none } = (sc, path))
    (hexit : NeonChainExit sp0 sc) :
    ∃ sf, runCall progs neonPath rNum m0 fuel (hops + 1) 4 (entry count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ :=
  wrapper_neon progs m0 fuel (hops + 1) count sp0 sc
    ("hashtree_sha256_neon_x4" :: path)
    (neon_x4_chain_of_cut progs m0 fuel hops count sp0 x4 scut sc path hf hrun hcut hx1)
    hexit.err hexit.halted hexit.tail hexit.ret hexit.sp hexit.frame

/-- The exit cut of the `sha_x1` leg: a clean single-leg finish at the unmoved `SP`, with the
wrapper's return marker 1 in `x30`. -/
structure ShaX1Exit (sp0 : Int) (sc : CS) : Prop where
  err : sc.err = none
  halted : sc.halted = true
  tail : sc.tail = none
  ret : sc.getG 30 = .ptr ⟨rRet, (1 : Int)⟩
  sp : sc.getG 31 = .ptr ⟨rStack, sp0⟩

/-- The `sha_x1` path of #79 with the kernel leg as a run to its exit cut. -/
theorem wrapper_sha_of_run (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel : Nat) (count : Nat) (sp0 : Int) (sha : Prog) (sc : CS)
    (hf : progs.find? (·.name = "hashtree_sha256_sha_x1") = some sha)
    (hrun : run sha.code sha.ro m0 (fun _ => false) fuel (shaEntry count sp0) = sc)
    (hfin : ShaX1Exit sp0 sc) :
    ∃ sf, runCall progs shaniPath rNum m0 fuel 1 2 (entry count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ :=
  wrapper_sha progs m0 fuel 1 count sp0 sc ["hashtree_sha256_sha_x1"]
    (runChain_single progs m0 fuel "hashtree_sha256_sha_x1" sha (shaEntry count sp0) sc
      hf hrun hfin.tail)
    hfin.err hfin.halted hfin.tail hfin.ret hfin.sp

end Hashtree.Asm.ArmCall
