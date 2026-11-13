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

end Hashtree.Asm.ArmCall
