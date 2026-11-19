import Hashtree.Asm.X86
import Hashtree.Asm.Hom
import Hashtree.Asm.X86Sym

/-!
# R5: the Windows x64 (Microsoft/COFF) calling convention, and register renaming

This file is part of the windows/amd64 workstream.  It has two parts.

## 1. The Win64 ABI, as a state model

`WinABI sp D` describes what a Windows kernel may assume and must preserve, stated over the
concrete machine model (`State W32 Int`):

* the return address is at `[rsp, rsp+8)`, and the caller has provided 32 bytes of shadow space
  at `[rsp+8, rsp+40)` (the kernel never reads it; it is dead memory that the contract leaves
  unconstrained, but which no kernel may require to hold anything);
* `rbx, rbp, rdi, rsi, r12-r15` (`winCalleeGpr`) and `xmm6-xmm15` (`winCalleeVec`) are
  callee-saved;
* the stack below the return address, down to `rsp - D`, is the kernel's frame: it may be written
  and is dead on return, and nothing else in memory may be written except the caller's output.

`ClobbersXmm6_15` is the observation **U6**: `avx512_x16` (windows) contains no save/restore of
xmm6-xmm15 at all, so for `count ≥ 16` it destroys six of the ten callee-saved vector registers.
`WinAvx512.lean` proves this against the model and gives a concrete witness.

## 2. Register renaming

The windows instruction streams are the linux ones under a *register permutation* (proved on the
models; see `notes/R5.md`).  `renSt F G` is the state-level permutation (general register `F j`
holds what register `j` held).  `rlI F` relabels an instruction, and `exec_ren`/`run_ren` show
that relabelled programs compute relabelled results.  This is the transfer engine: a functional
contract proved for a linux kernel becomes a windows contract by applying `run_ren` to the
linux Gen certificate.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Hashtree.Asm.X86
open Hashtree.Asm

/-! ## The Win64 frame and callee-saved sets -/

/-- Windows x64 callee-saved general registers: rbx, rbp, rdi, rsi, r12-r15. -/
def winCalleeGpr : List Nat := [3, 5, 7, 6, 12, 13, 14, 15]

/-- Windows x64 callee-saved vector registers: xmm6-xmm15 (lane registers 6..15). -/
def winCalleeVec : List Nat := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The shadow space: `[rsp+8, rsp+40)` on entry (the return address is at `[rsp, rsp+8)`). -/
def shadowLo : Int := 8
def shadowHi : Int := 40

/-- A windows kernel's frame: it may write stack bytes in `(sp - D, sp + 40)` below its entry
stack pointer `sp` (its own frame plus the caller's shadow space); nothing else. -/
def WinFrame (sp : Int) (D : Nat) (a : Addr Int) : Prop :=
  a.region = rStack ∧ sp - (D : Int) < a.off ∧ a.off < sp + shadowHi

/-- The callee-saved registers hold their entry values. -/
def WinCalleeSaved (s0 s : State W32 Int) : Prop :=
  (∀ g ∈ winCalleeGpr, s.getG g = s0.getG g) ∧ (∀ v ∈ winCalleeVec, s.getV v = s0.getV v)

/-- The registers a return address may name. -/
def IsRet (v : Val W32 Int) : Prop := ∃ o, v = .ptr ⟨rRet, o⟩

/-! ## Register renaming of states -/

section Ren
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
variable {ro : Region} {mem0 : Addr γ → Cell α γ} {orc : Nat → Bool}

/-- `renSt F G s`: the general registers of `s` permuted so that register `F j` holds what
register `j` held.  `F : linux → windows`, `G` its inverse on the registers in use; both are the
identity outside `0..15`.  Vector registers, flags, memory, pc and all other control state are
unchanged. -/
def renSt (F G : Nat → Nat) (s : State α γ) : State α γ :=
  { s with gpr := (List.range 16).map (fun j => s.getG (G j)) }

@[simp] theorem renSt_gpr_len (F G : Nat → Nat) (s : State α γ) : (renSt F G s).gpr.length = 16 := by
  simp [renSt]

@[simp] theorem renSt_vr (F G : Nat → Nat) (s : State α γ) : (renSt F G s).vr = s.vr := rfl
@[simp] theorem renSt_flags (F G : Nat → Nat) (s : State α γ) : (renSt F G s).flags = s.flags := rfl
@[simp] theorem renSt_mem (F G : Nat → Nat) (s : State α γ) : (renSt F G s).mem = s.mem := rfl
@[simp] theorem renSt_pc (F G : Nat → Nat) (s : State α γ) : (renSt F G s).pc = s.pc := rfl
@[simp] theorem renSt_halted (F G : Nat → Nat) (s : State α γ) : (renSt F G s).halted = s.halted := rfl
@[simp] theorem renSt_tail (F G : Nat → Nat) (s : State α γ) : (renSt F G s).tail = s.tail := rfl
@[simp] theorem renSt_err (F G : Nat → Nat) (s : State α γ) : (renSt F G s).err = s.err := rfl
@[simp] theorem renSt_assume (F G : Nat → Nat) (s : State α γ) : (renSt F G s).assume = s.assume := rfl

theorem renSt_getV (F G : Nat → Nat) (s : State α γ) (i : Nat) : (renSt F G s).getV i = s.getV i := rfl

theorem renSt_setV (F G : Nat → Nat) (s : State α γ) (i : Nat) (v : List α) :
    (renSt F G s).setV i v = renSt F G (s.setV i v) := rfl

theorem renSt_setVec (F G : Nat → Nat) (s : State α γ) (vex : Bool) (w d : Nat) (v : List α) :
    setVec (renSt F G s) vex w d v = renSt F G (setVec s vex w d v) := by
  simp only [setVec, renSt_setV, renSt_getV, renSt]
  rfl

theorem renSt_next (F G : Nat → Nat) (s : State α γ) : (renSt F G s).next = renSt F G s.next := rfl

theorem renSt_clearFlags (F G : Nat → Nat) (s : State α γ) :
    renSt F G (clearFlags s) = clearFlags (renSt F G s) := rfl

theorem renSt_setFlags (F G : Nat → Nat) (s : State α γ) (a b : γ) :
    renSt F G (setFlags s a b) = setFlags (renSt F G s) a b := rfl

theorem renSt_halt (F G : Nat → Nat) (s : State α γ) : renSt F G (halt s) = halt (renSt F G s) := by
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  rfl

theorem renSt_fail (F G : Nat → Nat) (s : State α γ) (m : String) :
    renSt F G (s.fail m) = (renSt F G s).fail m := by
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  cases err <;> rfl

theorem renSt_branch (F G : Nat → Nat) (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    renSt F G (s.branch orc c t) = (renSt F G s).branch orc c t := by
  unfold State.branch
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  cases hcd : c.decideC <;> (simp only [hcd, Option.isNone_none, Option.isNone_some, ite_true, ite_false, State.next, State.getG, renSt]; split <;> rfl)

/-- The list-level core of `renSt_setG`, stated separately so the permutation arithmetic is in
one place. -/
theorem renSt_gpr_set_aux (F G : Nat → Nat) (s : State α γ) (j : Nat) (hj : j < 16) (hF : F j < 16)
    (hGF : G (F j) = j) (hFG : ∀ k, k < 16 → F (G k) = k) (hlen : s.gpr.length = 16) (v : Val α γ) :
    ((List.range 16).map (fun k => s.getG (G k))).set (F j) v
      = (List.range 16).map (fun k => (s.setG j v).getG (G k)) := by
  apply List.ext_getElem?
  intro i
  simp only [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_set,
    List.length_map, List.length_range, Option.map_some]
  by_cases hi : i < 16
  · rw [List.getElem?_range hi]
    by_cases hk : F j = i
    · subst hk
      rw [if_pos rfl, if_pos hF, if_pos (by simpa [List.length_set, hlen] using hj)]
      rw [Option.map_some, Option.some.injEq, hGF]
      simp
    · have hGi : j ≠ G i := fun h => hk (by rw [h, hFG i hi])
      rw [if_neg hk, Option.map_some, Option.map_some, if_neg hGi]
  · have hle : i ≥ (List.range 16).length := by simpa using Nat.le_of_not_lt hi
    rw [List.getElem?_eq_none hle]
    by_cases hk : F j = i
    · exact absurd (hk ▸ hF) (by simpa using hle)
    · rw [if_neg hk]
      rfl

theorem renSt_setG (F G : Nat → Nat) (s : State α γ) (j : Nat) (hlen : s.gpr.length = 16)
    (hj : j < 16) (hF : F j < 16) (hGF : G (F j) = j) (hFG : ∀ k, k < 16 → F (G k) = k) (v : Val α γ) :
    (renSt F G s).setG (F j) v = renSt F G (s.setG j v) := by
  simp only [State.setG, renSt]
  congr 1
  have := renSt_gpr_set_aux F G s j hj hF hGF hFG hlen v
  simpa only [State.getG, State.setG] using this

theorem renSt_getG (F G : Nat → Nat) (s : State α γ) (j : Nat) (hF : F j < 16) (hGF : G (F j) = j) :
    (renSt F G s).getG (F j) = s.getG j := by
  simp only [State.getG, renSt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_range hF, Option.map_some, hGF]
  rfl

end Ren

/-! ## Relabelling memory operands and instructions -/

/-- The memory operand with its base/index registers relabelled. -/
def rlMem (F : Nat → Nat) (m : MemRef) : MemRef :=
  { m with base := m.base.map F, index := m.index.map F }

def rlGSrc (F : Nat → Nat) : GSrc → GSrc
  | .reg i => .reg (F i)
  | .imm v => .imm v
  | .mem m => .mem (rlMem F m)

def rlVSrc (F : Nat → Nat) : VSrc → VSrc
  | .reg i => .reg i
  | .mem m => .mem (rlMem F m)

/-- Relabel an instruction's general-register operands by `F`.  Vector registers are unchanged
(the linux and windows streams use the same zmm numbering); branch targets are unchanged. -/
def rlI (F : Nat → Nat) : Instr → Instr
  | .nop => .nop
  | .vop op vex w d s1 s2 => .vop op vex w d s1 (rlVSrc F s2)
  | .vshift k vex w d src n => .vshift k vex w d src n
  | .vshiftq vex w d src n => .vshiftq vex w d src n
  | .vror w d src n => .vror w d src n
  | .vtern w d s1 s2 imm => .vtern w d s1 s2 imm
  | .vload vex w d src => .vload vex w d (rlVSrc F src)
  | .vstore w m src => .vstore w (rlMem F m) src
  | .pshufd vex d src imm => .pshufd vex d src imm
  | .pshufb vex w d src mask => .pshufb vex w d src mask
  | .palignr vex d s1 s2 imm => .palignr vex d s1 s2 imm
  | .pblendw d src imm => .pblendw d src imm
  | .shufps w d s1 s2 imm => .shufps w d s1 s2 imm
  | .perm2f128 d s1 s2 imm => .perm2f128 d s1 s2 imm
  | .inserti128 d s1 m imm => .inserti128 d s1 (rlMem F m) imm
  | .inserti64x4 d s1 m imm => .inserti64x4 d s1 (rlMem F m) imm
  | .permi2d d s1 s2 => .permi2d d s1 s2
  | .permi2q d s1 s2 => .permi2q d s1 s2
  | .sha256rnds2 d src => .sha256rnds2 d src
  | .sha256msg1 d src => .sha256msg1 d src
  | .sha256msg2 d src => .sha256msg2 d src
  | .mov w d src => .mov w (F d) (rlGSrc F src)
  | .movst w m src => .movst w (rlMem F m) (F src)
  | .alu op w d src => .alu op w (F d) (rlGSrc F src)
  | .sub w d src => .sub w (F d) (rlGSrc F src)
  | .lea d m => .lea (F d) (rlMem F m)
  | .ror w d n => .ror w (F d) n
  | .shld w d src n => .shld w (F d) (F src) n
  | .shl w d n => .shl w (F d) n
  | .bswap w d => .bswap w (F d)
  | .push r => .push (F r)
  | .pop r => .pop (F r)
  | .cmp w a b => .cmp w (F a) (rlGSrc F b)
  | .test w a b => .test w (F a) (F b)
  | .jcc c t => .jcc c t
  | .jmp t => .jmp t
  | .jccTail c name => .jccTail c name
  | .jmpTail name => .jmpTail name
  | .ret => .ret

/-- The general-register indices an instruction mentions are below 16.  `okI` is the only
hypothesis the instruction-level simulation needs; every shipped kernel satisfies it (checked
with `decide` on the model). -/
def memOk (m : MemRef) : Prop :=
  (∀ b ∈ m.base, b < 16) ∧ (∀ i ∈ m.index, i < 16)

def gsrcOk : GSrc → Prop
  | .reg i => i < 16
  | .imm _ => True
  | .mem m => memOk m

def vsrcOk : VSrc → Prop
  | .reg _ => True
  | .mem m => memOk m

def okI : Instr → Prop
  | .nop => True
  | .vop _ _ _ _ _ s2 => vsrcOk s2
  | .vshift _ _ _ _ _ _ => True
  | .vshiftq _ _ _ _ _ => True
  | .vror _ _ _ _ => True
  | .vtern _ _ _ _ _ => True
  | .vload _ _ _ src => vsrcOk src
  | .vstore _ m _ => memOk m
  | .pshufd _ _ _ _ => True
  | .pshufb _ _ _ _ _ => True
  | .palignr _ _ _ _ _ => True
  | .pblendw _ _ _ => True
  | .shufps _ _ _ _ _ => True
  | .perm2f128 _ _ _ _ => True
  | .inserti128 _ _ m _ => memOk m
  | .inserti64x4 _ _ m _ => memOk m
  | .permi2d _ _ _ => True
  | .permi2q _ _ _ => True
  | .sha256rnds2 _ _ => True
  | .sha256msg1 _ _ => True
  | .sha256msg2 _ _ => True
  | .mov _ d src => d < 16 ∧ gsrcOk src
  | .movst _ m src => memOk m ∧ src < 16
  | .alu _ _ d src => d < 16 ∧ gsrcOk src
  | .sub _ d src => d < 16 ∧ gsrcOk src
  | .lea d m => d < 16 ∧ memOk m
  | .ror _ d _ => d < 16
  | .shld _ d src _ => d < 16 ∧ src < 16
  | .shl _ d _ => d < 16
  | .bswap _ d => d < 16
  | .push r => r < 16
  | .pop r => r < 16
  | .cmp _ a b => a < 16 ∧ gsrcOk b
  | .test _ a b => a < 16 ∧ b < 16
  | .jcc _ _ => True
  | .jmp _ => True
  | .jccTail _ _ => True
  | .jmpTail _ => True
  | .ret => True


/-! ## Renaming lemmas for memory operands, addressing and general operands

These are the local steps of the instruction simulation below: every operand read of the
renamed state is the corresponding read of the original state, and every state write of the
renamed state is the rename of the original write.  They hold for any register permutation that
fixes `rsp` and is injective on `0..15` (`RenPerm`). -/

/-- A register permutation of `0..15` as used by the windows transfer: `F` sends linux register
indices to windows ones, `G` is its inverse on the registers in use, and `rsp` is fixed. -/
structure RenPerm (F G : Nat → Nat) : Prop where
  lt : ∀ j, j < 16 → F j < 16
  gf : ∀ j, j < 16 → G (F j) = j
  fg : ∀ k, k < 16 → F (G k) = k
  fix_rsp : F (Hashtree.Asm.X86.rsp) = Hashtree.Asm.X86.rsp

section RenOps
variable {F G : Nat → Nat}
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int}

@[simp] theorem rlMem_ro (m : MemRef) : (rlMem F m).ro = m.ro := rfl
@[simp] theorem rlMem_base (m : MemRef) : (rlMem F m).base = m.base.map F := rfl
@[simp] theorem rlMem_index (m : MemRef) : (rlMem F m).index = m.index.map F := rfl
@[simp] theorem rlMem_scale (m : MemRef) : (rlMem F m).scale = m.scale := rfl
@[simp] theorem rlMem_disp (m : MemRef) : (rlMem F m).disp = m.disp := rfl

namespace RenPerm

theorem getG (h : RenPerm F G) (s : State W32 Int) (j : Nat) (hj : j < 16) :
    (renSt F G s).getG (F j) = s.getG j :=
  renSt_getG F G s j (h.lt j hj) (h.gf j hj)

theorem setG (h : RenPerm F G) (s : State W32 Int) (hlen : s.gpr.length = 16) (j : Nat)
    (hj : j < 16) (v : Val W32 Int) :
    (renSt F G s).setG (F j) v = renSt F G (s.setG j v) :=
  renSt_setG F G s j hlen hj (h.lt j hj) (h.gf j hj) h.fg v

theorem getG_rsp (h : RenPerm F G) (s : State W32 Int) :
    (renSt F G s).getG rsp = s.getG rsp := by
  calc (renSt F G s).getG rsp = (renSt F G s).getG (F rsp) := by rw [h.fix_rsp]
    _ = s.getG rsp := renSt_getG F G s rsp (h.lt rsp (by decide)) (h.gf rsp (by decide))

theorem setG_rsp (h : RenPerm F G) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (v : Val W32 Int) :
    (renSt F G s).setG rsp v = renSt F G (s.setG rsp v) :=
  calc (renSt F G s).setG rsp v = (renSt F G s).setG (F rsp) v := by rw [h.fix_rsp]
    _ = renSt F G (s.setG rsp v) :=
      renSt_setG F G s rsp hlen (by decide) (h.lt rsp (by decide)) (h.gf rsp (by decide)) h.fg v

theorem regPtr_ren (h : RenPerm F G) (s : State W32 Int) (r : Nat) (hr : r < 16) :
    regPtr (renSt F G s) (F r) = regPtr s r := by
  simp only [regPtr, h.getG s r hr]

theorem baseAddr_ren (h : RenPerm F G) (s : State W32 Int) (m : MemRef) (hok : memOk m) :
    baseAddr ro (renSt F G s) (rlMem F m) = baseAddr ro s m := by
  obtain ⟨hb, _⟩ := hok
  simp only [baseAddr, rlMem_ro, rlMem_base]
  cases hro : m.ro with
  | some o => rfl
  | none =>
    cases hb' : m.base with
    | none => rfl
    | some b =>
      have h16 : b < 16 := hb b (by simp [hb'])
      simp only [Option.map_some]
      exact regPtr_ren h s b h16

theorem effAddr_ren (h : RenPerm F G) (s : State W32 Int) (m : MemRef) (hok : memOk m) :
    effAddr ro (renSt F G s) (rlMem F m) = effAddr ro s m := by
  obtain ⟨hb, hi⟩ := hok
  simp only [effAddr, rlMem_index, rlMem_disp, rlMem_scale]
  rw [baseAddr_ren h s m ⟨hb, hi⟩]
  cases ha : baseAddr ro s m with
  | error e => rfl
  | ok b =>
    cases hidx : m.index with
    | none => rfl
    | some i =>
      have h16 : i < 16 := hi i (by simp [hidx])
      simp only [Option.map_some, h.getG s i h16]

theorem readCell_ren (s : State W32 Int) (a : Addr Int) :
    readCell mem0 (renSt F G s) a = readCell mem0 s a := by
  simp only [readCell, renSt_mem]

theorem loadLane_ren (s : State W32 Int) (a : Addr Int) :
    loadLane mem0 (renSt F G s) a = loadLane mem0 s a := by
  simp only [loadLane, readCell_ren]

theorem loadLanes_ren : ∀ (s : State W32 Int) (a : Addr Int) (n : Nat),
    loadLanes mem0 (renSt F G s) a n = loadLanes mem0 s a n
  | s, a, 0 => rfl
  | s, a, n + 1 => by
    simp only [loadLanes]
    rw [loadLane_ren, loadLanes_ren s (a.plusI 4) n]

theorem storeLane_ren (s : State W32 Int) (a : Addr Int) (x : W32) :
    storeLane (renSt F G s) a x = renSt F G (storeLane s a x) := rfl

theorem storeLanes_ren : ∀ (s : State W32 Int) (a : Addr Int) (v : List W32),
    storeLanes (renSt F G s) a v = renSt F G (storeLanes s a v)
  | _, _, [] => rfl
  | s, a, x :: xs => by
    simp only [storeLanes]
    rw [storeLane_ren, storeLanes_ren (storeLane s a x) (a.plusI 4) xs]

theorem pbRest_ren : ∀ (s : State W32 Int) (p a : Addr Int) (n k : Nat),
    pbRest mem0 (renSt F G s) p a n k = pbRest mem0 s p a n k
  | _, _, _, 0, _ => rfl
  | s, p, a, n + 1, k => by
    simp only [pbRest, readCell_ren, pbRest_ren s p a n (k + 1)]

theorem loadVal_ren (s : State W32 Int) (a : Addr Int) :
    loadVal mem0 (renSt F G s) a = loadVal mem0 s a := by
  simp only [loadVal, readCell_ren, pbRest_ren, loadLane_ren]

theorem storeVal_ren (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    storeVal (renSt F G s) a v = renSt F G (storeVal s a v) := by
  cases v with
  | num lo hi => simp only [storeVal, storeLane_ren]
  | ptr p => rfl

theorem readVSrc_ren (h : RenPerm F G) (s : State W32 Int) (w : Nat) (src : VSrc)
    (hok : vsrcOk src) :
    readVSrc ro mem0 (renSt F G s) w (rlVSrc F src) = readVSrc ro mem0 s w src := by
  cases src with
  | reg i => simp only [rlVSrc, readVSrc, renSt_getV]
  | mem m =>
    obtain ⟨hb, hi⟩ := hok
    simp only [rlVSrc, readVSrc, effAddr_ren h s m ⟨hb, hi⟩, loadLanes_ren]

theorem gCtl_ren (h : RenPerm F G) (s : State W32 Int) (src : GSrc) (hok : gsrcOk src) :
    gCtl (renSt F G s) (rlGSrc F src) = gCtl s src := by
  cases src with
  | reg i => simp only [rlGSrc, gCtl, h.getG s i hok]
  | imm v => rfl
  | mem m => rfl

theorem gData32_ren (h : RenPerm F G) (s : State W32 Int) (src : GSrc) (hok : gsrcOk src) :
    gData32 ro mem0 (renSt F G s) (rlGSrc F src) = gData32 ro mem0 s src := by
  cases src with
  | reg i => simp only [rlGSrc, gData32, h.getG s i hok]
  | imm v => rfl
  | mem m =>
    obtain ⟨hb, hi⟩ := hok
    simp only [rlGSrc, gData32, effAddr_ren h s m ⟨hb, hi⟩, loadLane_ren]

theorem setData32_ren (h : RenPerm F G) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (d : Nat) (hd : d < 16) (x : W32) :
    setData32 (renSt F G s) (F d) x = renSt F G (setData32 s d x) := by
  simp only [setData32]
  exact h.setG s hlen d hd (.num x (Lane.const 0))

theorem clearFlags_ren (s : State W32 Int) :
    clearFlags (renSt F G s) = renSt F G (clearFlags s) := (renSt_clearFlags F G s).symm

theorem setFlags_ren (s : State W32 Int) (a b : Int) :
    setFlags (renSt F G s) a b = renSt F G (setFlags s a b) := (renSt_setFlags F G s a b).symm

theorem halt_ren (s : State W32 Int) : halt (renSt F G s) = renSt F G (halt s) :=
  (renSt_halt F G s).symm

theorem fail_ren (s : State W32 Int) (m : String) :
    (renSt F G s).fail m = renSt F G (s.fail m) := (renSt_fail F G s m).symm

end RenPerm

end RenOps


/-! ### Operand renaming equations -/

variable {F G : Nat → Nat} {ro : Region} {mem0 : Addr Int → Cell W32 Int}

@[simp] theorem rlGSrc_reg (r : Nat) : rlGSrc F (.reg r) = .reg (F r) := rfl
@[simp] theorem rlGSrc_imm (v : Int) : rlGSrc F (.imm v) = .imm v := rfl
@[simp] theorem rlGSrc_mem (m : MemRef) : rlGSrc F (.mem m) = .mem (rlMem F m) := rfl
@[simp] theorem rlVSrc_reg (i : Nat) : rlVSrc F (.reg i) = .reg i := rfl
@[simp] theorem rlVSrc_mem (m : MemRef) : rlVSrc F (.mem m) = .mem (rlMem F m) := rfl

/-- `gCtl` on a renamed plain register. -/
theorem gCtl_ren_reg {F G : Nat → Nat} (h : RenPerm F G) (s : State W32 Int) (d : Nat)
    (hd : d < 16) : gCtl (renSt F G s) (.reg (F d)) = gCtl s (.reg d) := by
  simpa only [rlGSrc] using RenPerm.gCtl_ren h s (.reg d) hd

/-- `gData32` on a renamed plain register. -/
theorem gData32_ren_reg {F G : Nat → Nat} (h : RenPerm F G) (s : State W32 Int) (d : Nat)
    (hd : d < 16) :
    gData32 ro mem0 (renSt F G s) (.reg (F d)) = gData32 ro mem0 s (.reg d) := by
  simpa only [rlGSrc] using RenPerm.gData32_ren h s (.reg d) hd

/-! ## The instruction and program simulation -/

section ExecRen
variable {F G : Nat → Nat}
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- If the renamed general-register source is the renamed register itself, the source was that
register: the permutation is injective on the register file. -/
theorem rlGSrc_eq_reg (h : RenPerm F G) (d : Nat) (hd : d < 16) {src : GSrc}
    (hs : gsrcOk src) (he : rlGSrc F src = .reg (F d)) : src = .reg d := by
  cases src with
  | reg r =>
    have hr : r < 16 := hs
    have he' : (.reg (F r) : GSrc) = .reg (F d) := he
    injection he' with hfd
    have hrd : r = d := by rw [← h.gf r hr, ← h.gf d hd, hfd]
    rw [hrd]
  | imm v =>
    have he' : (.imm v : GSrc) = .reg (F d) := he
    cases he'
  | mem m =>
    have he' : (.mem (rlMem F m) : GSrc) = .reg (F d) := he
    cases he'

theorem okOr_ok (s : State W32 Int) (t : State W32 Int) : okOr s (.ok t) = t := rfl
theorem okOr_error (s : State W32 Int) (e : String) : okOr s (.error e) = s.fail e := rfl
theorem okOr_pure (s : State W32 Int) (t : State W32 Int) : okOr s (pure t) = t := rfl

theorem bind_ok_eq {β δ : Type} (b : β) (k : β → Except String δ) :
    ((Except.ok b : Except String β) >>= k) = k b := rfl

theorem bind_error_eq {β δ : Type} (e : String) (k : β → Except String δ) :
    ((Except.error e : Except String β) >>= k) = .error e := rfl

/-! ### The register file keeps its length -/

@[simp] theorem gpr_len_setG (s : State W32 Int) (i : Nat) (v : Val W32 Int) :
    (s.setG i v).gpr.length = s.gpr.length := by simp [State.setG]
@[simp] theorem gpr_len_setV (s : State W32 Int) (i : Nat) (v : List W32) :
    (s.setV i v).gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_next (s : State W32 Int) : s.next.gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_branch (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    (s.branch orc c t).gpr.length = s.gpr.length := by
  unfold State.branch
  dsimp only
  repeat (first | rfl | split)
@[simp] theorem gpr_len_clearFlags (s : State W32 Int) :
    (clearFlags s).gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_setFlags (s : State W32 Int) (a b : Int) :
    (setFlags s a b).gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_halt (s : State W32 Int) : (halt s).gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_fail (s : State W32 Int) (m : String) :
    (s.fail m).gpr.length = s.gpr.length := by simp only [State.fail]; split <;> rfl
@[simp] theorem gpr_len_setVec (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) :
    (setVec s vex w d v).gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_setData32 (s : State W32 Int) (d : Nat) (x : W32) :
    (setData32 s d x).gpr.length = s.gpr.length := by simp [setData32]
@[simp] theorem gpr_len_storeLane (s : State W32 Int) (a : Addr Int) (x : W32) :
    (storeLane s a x).gpr.length = s.gpr.length := rfl
@[simp] theorem gpr_len_storeLanes : ∀ (v : List W32) (s : State W32 Int) (a : Addr Int),
    (storeLanes s a v).gpr.length = s.gpr.length
  | [], s, a => rfl
  | x :: xs, s, a => by
    simp only [storeLanes]
    exact gpr_len_storeLanes xs (storeLane s a x) (a.plusI 4)
@[simp] theorem gpr_len_storeVal (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    (storeVal s a v).gpr.length = s.gpr.length := by
  cases v with
  | num lo hi => simp [storeVal]
  | ptr p => simp [storeVal]

theorem okOr_len (s : State W32 Int) (r : Except String (State W32 Int))
    (h : EP (fun t : State W32 Int => t.gpr.length = s.gpr.length) r) :
    (okOr s r).gpr.length = s.gpr.length := by
  cases r with
  | ok t => exact h t rfl
  | error e => simp only [okOr_error, gpr_len_fail]

local macro "len_tac" : tactic => `(tactic| (
  repeat (first
    | apply EP_bind; intro _
    | apply EP_throw
    | apply EP_ite <;> intro _
    | (apply EP_pure; simp)
    | split)))

/-- An instruction's execution keeps the register-list length. -/
theorem exec_gpr_len (i : Instr) (s : State W32 Int) :
    (exec ro mem0 orc i s).gpr.length = s.gpr.length := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [hh, ite_true]
  simp only [hh, Bool.false_eq_true, ite_false]
  cases i <;> dsimp only
  all_goals first
    | rfl
    | (apply okOr_len; len_tac)

/-! ### Renaming commutes with evaluation -/

theorem okOr_pure_ren (s : State W32 Int) (X : State W32 Int) :
    okOr (renSt F G s) (pure (renSt F G X)) = renSt F G (okOr s (pure X)) := by
  rw [okOr_pure, okOr_pure]

theorem okOr_bind_ren {β : Type} (s : State W32 Int) (m : Except String β)
    (f : β → State W32 Int) :
    okOr (renSt F G s) (m >>= fun b => pure (renSt F G (f b)))
      = renSt F G (okOr s (m >>= fun b => pure (f b))) := by
  cases hm : m with
  | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
  | ok b => simp only [bind_ok_eq, okOr_pure]

theorem okOr_bind2_ren {β δ : Type} (s : State W32 Int) (m : Except String β)
    (n : β → Except String δ) (f : β → δ → State W32 Int) :
    okOr (renSt F G s) (m >>= fun a => n a >>= fun b => pure (renSt F G (f a b)))
      = renSt F G (okOr s (m >>= fun a => n a >>= fun b => pure (f a b))) := by
  cases hm : m with
  | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
  | ok a =>
    simp only [bind_ok_eq]
    exact okOr_bind_ren s (n a) (f a)

theorem okOr_bind_err {β : Type} (s : State W32 Int) (m : Except String β) (e : String) :
    okOr (renSt F G s) (m >>= fun _ => (Except.error e : Except String (State W32 Int)))
      = renSt F G (okOr s (m >>= fun _ => (Except.error e))) := by
  cases hm : m with
  | error e' => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
  | ok b => simp only [bind_ok_eq, okOr_error, RenPerm.fail_ren]

theorem okOr_bind2_err {β δ : Type} (s : State W32 Int) (m : Except String β)
    (n : β → Except String δ) (e : String) :
    okOr (renSt F G s)
        (m >>= fun a => n a >>= fun _ => (Except.error e : Except String (State W32 Int)))
      = renSt F G (okOr s (m >>= fun a => n a >>= fun _ => (Except.error e))) := by
  cases hm : m with
  | error e' => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
  | ok a =>
    simp only [bind_ok_eq]
    exact okOr_bind_err s (n a) e

/-- A throw commutes with the renaming. -/
theorem okOr_throw_ren (s : State W32 Int) (msg : String) :
    okOr (renSt F G s) (throw msg) = renSt F G (okOr s (throw msg)) := by
  show okOr (renSt F G s) (.error msg) = renSt F G (okOr s (.error msg))
  simp only [okOr_error, RenPerm.fail_ren]

/-- An instruction's execution is equivariant under the register renaming. -/
theorem exec_ren (h : RenPerm F G) (i : Instr) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (hok : okI i) :
    exec ro mem0 orc (rlI F i) (renSt F G s) = renSt F G (exec ro mem0 orc i s) := by
  cases hs : s.halted with
  | true => simp only [exec, hs, ite_true, renSt_halted]
  | false =>
  simp only [exec, hs, renSt_halted, Bool.false_eq_true, ite_false]
  cases i with
  | nop => simp only [rlI, renSt_next]
  | vop op vex w d s1 s2 =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    rw [RenPerm.readVSrc_ren h s w s2 hok]
    exact okOr_bind_ren s _ _
  | vshift k vex w d src n =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | vshiftq vex w d src n =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | vror w d src n =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | vtern w d s1 s2 imm =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | vload vex w d src =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    rw [RenPerm.readVSrc_ren h s w src hok]
    exact okOr_bind_ren s _ _
  | vstore w m src =>
    obtain ⟨hb, hi⟩ : memOk m := hok
    simp only [rlI, renSt_getV, renSt_next,
      RenPerm.effAddr_ren h s m ⟨hb, hi⟩, RenPerm.storeLanes_ren]
    exact okOr_bind_ren s _ _
  | pshufd vex d src imm =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | pshufb vex w d src mask =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_bind_ren s _ _
  | palignr vex d s1 s2 imm =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | pblendw d src imm =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | shufps w d s1 s2 imm =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | perm2f128 d s1 s2 imm =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | inserti128 d s1 m imm =>
    obtain ⟨hb, hi⟩ : memOk m := hok
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next,
      RenPerm.effAddr_ren h s m ⟨hb, hi⟩, RenPerm.loadLanes_ren]
    exact okOr_bind2_ren s _ _ _
  | inserti64x4 d s1 m imm =>
    obtain ⟨hb, hi⟩ : memOk m := hok
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next,
      RenPerm.effAddr_ren h s m ⟨hb, hi⟩, RenPerm.loadLanes_ren]
    exact okOr_bind2_ren s _ _ _
  | permi2d d s1 s2 =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_bind_ren s _ _
  | permi2q d s1 s2 =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_bind_ren s _ _
  | sha256rnds2 d src =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | sha256msg1 d src =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | sha256msg2 d src =>
    simp only [rlI, renSt_getV, renSt_setVec, renSt_next]
    exact okOr_pure_ren s _
  | mov w d src =>
    obtain ⟨hd, hsok⟩ : d < 16 ∧ gsrcOk src := hok
    simp only [rlI]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases src with
      | reg r =>
        have hr : r < 16 := hsok
        simp only [rlI, rlGSrc_reg, renSt_next, h.getG s r hr, h.setG s hlen d hd]
        exact okOr_pure_ren s _
      | imm v =>
        simp only [rlI, rlGSrc_imm, renSt_next, h.setG s hlen d hd]
        exact okOr_pure_ren s _
      | mem m =>
        obtain ⟨hb, hi⟩ : memOk m := hsok
        simp only [rlI, rlGSrc_mem, renSt_next, RenPerm.effAddr_ren h s m ⟨hb, hi⟩,
          RenPerm.loadVal_ren, h.setG s hlen d hd]
        exact okOr_bind2_ren s _ _ _
    · simp only [if_neg hw]
      simp only [rlI, RenPerm.gData32_ren h s src hsok, renSt_next,
        RenPerm.setData32_ren h s hlen d hd, renSt_next]
      exact okOr_bind_ren s _ _
  | movst w m src =>
    obtain ⟨hm, hsrc⟩ : memOk m ∧ src < 16 := hok
    simp only [rlI, renSt_next, RenPerm.effAddr_ren h s m hm]
    by_cases hw : w = 64
    · simp only [if_pos hw, h.getG s src hsrc, RenPerm.storeVal_ren, renSt_next]
      exact okOr_bind_ren s _ _
    · simp only [if_neg hw, h.getG s src hsrc]
      cases hg : s.getG src with
      | num lo hi =>
        simp only [renSt_next, RenPerm.storeLane_ren]
        exact okOr_bind_ren s _ _
      | ptr p =>
        exact okOr_bind_err s _ _
  | alu op w d src =>
    obtain ⟨hd, hsok⟩ : d < 16 ∧ gsrcOk src := hok
    simp only [rlI]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      by_cases hz : op = .xor ∧ src = .reg d
      · have hx : op = .xor := hz.1
        have hsd : src = .reg d := hz.2
        simp only [if_pos hz]
        simp only [if_pos (show op = .xor ∧ (rlGSrc F src : GSrc) = .reg (F d) from
          ⟨hx, by rw [hsd]; rfl⟩)]
        simp only [renSt_next, RenPerm.clearFlags_ren, RenPerm.setG h s hlen d hd]
        exact okOr_pure_ren s _
      · simp only [if_neg hz]
        simp only [if_neg (show ¬(op = .xor ∧ (rlGSrc F src : GSrc) = .reg (F d)) from
          fun hc => hz ⟨hc.1, rlGSrc_eq_reg h d hd hsok hc.2⟩)]
        simp only [gCtl_ren_reg h s d hd, RenPerm.gCtl_ren h s src hsok]
        cases ha : gCtl s (.reg d) with
        | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
        | ok a =>
          cases hb : gCtl s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, RenPerm.fail_ren]
          | ok b =>
            simp only [bind_ok_eq]
            cases op with
            | add =>
              dsimp only
              by_cases hc : b.region = rNum ∨ a.region = rNum
              · simp only [if_pos hc]
                simp only [renSt_next, RenPerm.setFlags_ren, RenPerm.setG h s hlen d hd]
                exact okOr_pure_ren s _
              · simp only [if_neg hc]
                exact okOr_throw_ren s _
            | xor =>
              dsimp only
              exact okOr_throw_ren s _
            | and =>
              dsimp only
              cases hx2 : Ctl.asInt a.off with
              | none => exact okOr_throw_ren s _
              | some x =>
                cases hy2 : Ctl.asInt b.off with
                | none => exact okOr_throw_ren s _
                | some y =>
                  dsimp only
                  cases hr2 : andInt x y with
                  | none => exact okOr_throw_ren s _
                  | some r =>
                    by_cases hc : b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0))
                    · simp only [if_pos hc]
                      simp only [renSt_next, RenPerm.clearFlags_ren, RenPerm.setG h s hlen d hd]
                      exact okOr_pure_ren s _
                    · simp only [if_neg hc]
                      exact okOr_throw_ren s _
            | or =>
              dsimp only
              exact okOr_throw_ren s _
    · simp only [if_neg hw]
      by_cases hz : op = .xor ∧ src = .reg d
      · have hx : op = .xor := hz.1
        have hsd : src = .reg d := hz.2
        simp only [if_pos hz]
        simp only [if_pos (show op = .xor ∧ (rlGSrc F src : GSrc) = .reg (F d) from
          ⟨hx, by rw [hsd]; rfl⟩)]
        simp only [renSt_next, RenPerm.clearFlags_ren, RenPerm.setData32_ren h s hlen d hd]
        exact okOr_pure_ren s _
      · simp only [if_neg hz]
        simp only [if_neg (show ¬(op = .xor ∧ (rlGSrc F src : GSrc) = .reg (F d)) from
          fun hc => hz ⟨hc.1, rlGSrc_eq_reg h d hd hsok hc.2⟩)]
        simp only [gData32_ren_reg h s d hd, RenPerm.gData32_ren h s src hsok]
        cases ha : gData32 ro mem0 s (.reg d) with
        | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
        | ok a =>
          cases hb : gData32 ro mem0 s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, RenPerm.fail_ren]
          | ok b =>
            simp only [bind_ok_eq, renSt_next, RenPerm.clearFlags_ren,
              RenPerm.setData32_ren h s hlen d hd]
            exact okOr_pure_ren s _
  | sub w d src =>
    obtain ⟨hd, hsok⟩ : d < 16 ∧ gsrcOk src := hok
    simp only [rlI]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_ren_reg h s d hd, RenPerm.gCtl_ren h s src hsok]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, RenPerm.fail_ren]
        | ok b =>
          simp only [bind_ok_eq]
          by_cases hc : b.region = rNum
          · simp only [if_pos hc]
            simp only [renSt_next, RenPerm.setFlags_ren, RenPerm.setG h s hlen d hd]
            exact okOr_pure_ren s _
          · simp only [if_neg hc]
            exact okOr_throw_ren s _
    · simp only [if_neg hw]
      exact okOr_throw_ren s _
  | lea d m =>
    obtain ⟨hd, hm⟩ : d < 16 ∧ memOk m := hok
    simp only [rlI, renSt_next, RenPerm.effAddr_ren h s m hm, RenPerm.setG h s hlen d hd]
    exact okOr_bind_ren s _ _
  | ror w d n =>
    have hd : d < 16 := hok
    simp only [rlI]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_ren_reg h s d hd]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok a =>
        simp only [bind_ok_eq, renSt_next, RenPerm.clearFlags_ren,
          RenPerm.setData32_ren h s hlen d hd]
        exact okOr_pure_ren s _
    · simp only [if_neg hw]
      exact okOr_throw_ren s _
  | shld w d src n =>
    obtain ⟨hd, hs⟩ : d < 16 ∧ src < 16 := hok
    simp only [rlI]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_ren_reg h s d hd, gData32_ren_reg h s src hs]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok a =>
        cases hb : gData32 ro mem0 s (.reg src) with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, RenPerm.fail_ren]
        | ok b =>
          simp only [bind_ok_eq, renSt_next, RenPerm.clearFlags_ren,
            RenPerm.setData32_ren h s hlen d hd]
          exact okOr_pure_ren s _
    · simp only [if_neg hw]
      exact okOr_throw_ren s _
  | shl w d n =>
    have hd : d < 16 := hok
    simp only [rlI]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_ren_reg h s d hd]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok a =>
        simp only [bind_ok_eq]
        by_cases hr : a.region = rNum
        · simp only [if_pos hr]
          simp only [renSt_next, RenPerm.clearFlags_ren, RenPerm.setG h s hlen d hd]
          exact okOr_pure_ren s _
        · simp only [if_neg hr]
          exact okOr_throw_ren s _
    · simp only [if_neg hw]
      simp only [gData32_ren_reg h s d hd]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok a =>
        simp only [bind_ok_eq, renSt_next, RenPerm.clearFlags_ren,
          RenPerm.setData32_ren h s hlen d hd]
        exact okOr_pure_ren s _
  | bswap w d =>
    have hd : d < 16 := hok
    simp only [rlI]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_ren_reg h s d hd]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok a =>
        simp only [bind_ok_eq, renSt_next, RenPerm.setData32_ren h s hlen d hd]
        exact okOr_pure_ren s _
    · simp only [if_neg hw]
      exact okOr_throw_ren s _
  | push r =>
    have hr : r < 16 := hok
    simp only [rlI, RenPerm.getG_rsp h s]
    cases hs2 : s.getG rsp with
    | num lo hi => exact okOr_throw_ren s _
    | ptr sp =>
      simp only [h.getG s r hr, RenPerm.storeVal_ren, renSt_next,
        RenPerm.setG_rsp h (storeVal s (sp.plusI (-8)) (s.getG r)) (by simp [hlen])]
      exact okOr_pure_ren s _
  | pop r =>
    have hr : r < 16 := hok
    simp only [rlI, RenPerm.getG_rsp h s]
    cases hs2 : s.getG rsp with
    | num lo hi => exact okOr_throw_ren s _
    | ptr sp =>
      simp only [RenPerm.loadVal_ren]
      cases hv : loadVal mem0 s sp with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok v =>
        simp only [bind_ok_eq, renSt_next, RenPerm.setG h s hlen r hr,
          RenPerm.setG_rsp h (s.setG r v) (by simp [hlen])]
        exact okOr_pure_ren s _
  | cmp w a b =>
    obtain ⟨ha, hsok⟩ : a < 16 ∧ gsrcOk b := hok
    simp only [rlI]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_ren_reg h s a ha, RenPerm.gCtl_ren h s b hsok]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok x =>
        cases hy : gCtl s b with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, RenPerm.fail_ren]
        | ok y =>
          simp only [bind_ok_eq]
          by_cases hc : y.region = rNum ∨ y.region = x.region
          · simp only [if_pos hc]
            simp only [renSt_next, RenPerm.setFlags_ren]
            exact okOr_pure_ren s _
          · simp only [if_neg hc]
            exact okOr_throw_ren s _
    · simp only [if_neg hw]
      exact okOr_throw_ren s _
  | test w a b =>
    obtain ⟨ha, hb⟩ : a < 16 ∧ b < 16 := hok
    simp only [rlI]
    by_cases hc : w = 64 ∧ a = b
    · have hw : w = 64 := hc.1
      have hab : a = b := hc.2
      simp only [if_pos hc]
      simp only [if_pos (show w = 64 ∧ (F a) = (F b) from ⟨hw, by rw [hab]⟩)]
      simp only [gCtl_ren_reg h s a ha]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok x =>
        simp only [bind_ok_eq]
        by_cases hr : x.region = rNum
        · simp only [if_pos hr]
          simp only [renSt_next, RenPerm.setFlags_ren]
          exact okOr_pure_ren s _
        · simp only [if_neg hr]
          exact okOr_throw_ren s _
    · simp only [if_neg (show ¬(w = 64 ∧ (F a) = (F b)) from fun hc' => hc ⟨hc'.1, by
        have hg2 : G (F a) = G (F b) := by rw [hc'.2]
        rwa [h.gf a ha, h.gf b hb] at hg2⟩)]
      simp only [if_neg hc]
      exact okOr_throw_ren s _
  | jcc c t =>
    simp only [rlI, renSt_flags]
    cases hf : s.flags with
    | none => exact okOr_throw_ren s _
    | some p =>
      obtain ⟨a, b⟩ := p
      simp only [okOr_pure]
      exact (renSt_branch F G s orc (ccCond c a b) t).symm
  | jmp t => rfl
  | jccTail c name =>
    simp only [rlI, renSt_flags]
    cases hf : s.flags with
    | none => exact okOr_throw_ren s _
    | some p =>
      obtain ⟨a, b⟩ := p
      have hbr : (renSt F G s).branch orc (ccCond c a b) 1000000000
          = renSt F G (s.branch orc (ccCond c a b) 1000000000) :=
        (renSt_branch F G s orc (ccCond c a b) 1000000000).symm
      simp only [hbr, renSt_pc, okOr_pure]
      by_cases hpc : (s.branch orc (ccCond c a b) 1000000000).pc = 1000000000
      · simp only [if_pos hpc]
        rfl
      · simp only [if_neg hpc]
        exact okOr_pure_ren s _
  | jmpTail name => rfl
  | ret =>
    simp only [rlI, RenPerm.getG_rsp h s]
    cases hs2 : s.getG rsp with
    | num lo hi => exact okOr_throw_ren s _
    | ptr sp =>
      simp only [RenPerm.loadVal_ren]
      cases hv : loadVal mem0 s sp with
      | error e => simp only [bind_error_eq, okOr_error, RenPerm.fail_ren]
      | ok v =>
        simp only [bind_ok_eq]
        cases v with
        | num lo hi => exact okOr_throw_ren s _
        | ptr p =>
          obtain ⟨reg, off⟩ := p
          split
          · simp only [renSt_next, RenPerm.halt_ren, RenPerm.setG_rsp h s hlen]
            exact okOr_pure_ren s _
          · exact okOr_throw_ren s _

section RunRen
variable {F G : Nat → Nat} {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

theorem run_gpr_len (prog : Array Instr) (n : Nat) (s : State W32 Int) :
    (run prog ro mem0 orc n s).gpr.length = s.gpr.length := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hh : s.halted = true
    · rw [run_halted prog ro mem0 orc (n+1) s hh]
    · have hf : s.halted = false := by simpa using hh
      simp only [run, hf, Bool.false_eq_true, ite_false]
      cases hi : prog[s.pc]? with
      | none => simp only [State.fail]; split <;> rfl
      | some i =>
          show (run prog ro mem0 orc n (exec ro mem0 orc i s)).gpr.length = s.gpr.length
          rw [ih (exec ro mem0 orc i s), exec_gpr_len]

theorem run_ren_upto (h : RenPerm F G) (prog winProg : Array Instr)
    (hmap : ∀ j, j < prog.size → winProg[j]? = (prog[j]?).map (rlI F))
    (hok : ∀ (pc : Nat) (x : Instr), prog[pc]? = some x → okI x) :
    ∀ (n : Nat) (s : State W32 Int), s.gpr.length = 16 →
      (∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨ (run prog ro mem0 orc k s).pc < prog.size) →
      run winProg ro mem0 orc n (renSt F G s) = renSt F G (run prog ro mem0 orc n s) := by
  intro n
  induction n with
  | zero => intro s _ _; rfl
  | succ n ih =>
    intro s hlen hcond
    by_cases hh : s.halted = true
    · have hren : (renSt F G s).halted = true := by simp [hh]
      rw [run_halted prog ro mem0 orc (n+1) s hh,
          run_halted winProg ro mem0 orc (n+1) (renSt F G s) hren]
    · have hf : s.halted = false := by simpa using hh
      have h0 : s.halted = true ∨ s.pc < prog.size := by
        have h := hcond 0 (Nat.zero_lt_succ n)
        simpa only [run] using h
      have hpc : s.pc < prog.size := by
        rcases h0 with h' | h'
        · simp [hf] at h'
        · exact h'
      have hx : prog[s.pc]? = some prog[s.pc] := Array.getElem?_eq_getElem hpc
      have hwx : winProg[s.pc]? = some (rlI F prog[s.pc]) := by
        rw [hmap s.pc hpc, hx]; rfl
      have hrenf : (renSt F G s).halted = false := by simp [hf]
      have e1 : run winProg ro mem0 orc (n+1) (renSt F G s)
          = run winProg ro mem0 orc n (exec ro mem0 orc (rlI F prog[s.pc]) (renSt F G s)) := by
        simp only [run, renSt_pc, hrenf, Bool.false_eq_true, ite_false, hwx]
      have step : ∀ m, run prog ro mem0 orc (m+1) s
          = run prog ro mem0 orc m (exec ro mem0 orc prog[s.pc] s) := by
        intro m; simp only [run, hf, Bool.false_eq_true, ite_false, hx]
      rw [e1, step n, exec_ren h prog[s.pc] s hlen (hok _ _ hx)]
      exact ih (exec ro mem0 orc prog[s.pc] s) (by simp [exec_gpr_len, hlen])
        (fun k hk => by
          have := hcond (k+1) (Nat.succ_lt_succ hk)
          rwa [step k] at this)

end RunRen

section Inv
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

theorem run_nofail (prog : Array Instr) :
    ∀ (n : Nat) (s : State W32 Int), s.err = none → (run prog ro mem0 orc n s).err = none →
      ∀ k, k ≤ n → (run prog ro mem0 orc k s).halted = true ∨ (run prog ro mem0 orc k s).err = none
  | 0, s, hs, _, k, hk => by
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      exact Or.inr (by simp only [run]; exact hs)
  | n+1, s, hs, hf, k, hk => by
      by_cases hh : s.halted = true
      · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          exact Or.inl (by rw [run_halted prog ro mem0 orc 0 s hh]; exact hh)
        · exact Or.inl (by rw [run_halted prog ro mem0 orc k s hh]; exact hh)
      · have hh' : s.halted = false := by simpa using hh
        have hstep : run prog ro mem0 orc (n+1) s
            = match prog[s.pc]? with
              | some i => run prog ro mem0 orc n (exec ro mem0 orc i s)
              | none => s.fail "pc out of program" := by
          simp only [run, hh', Bool.false_eq_true, ite_false]
          rfl
        rw [hstep] at hf
        cases hi : prog[s.pc]? with
        | none =>
            simp only [hi] at hf
            simp [State.fail, hs] at hf
        | some i =>
            simp only [hi] at hf
            rcases exec_keeps ro mem0 orc i s hs with ⟨he, _⟩ | ⟨e, he⟩
            · have he' : (exec ro mem0 orc i s).err = none := he.trans hs
              rcases Nat.eq_zero_or_pos k with hk0 | hkpos
              · subst hk0
                exact Or.inr (by simp only [run]; exact hs)
              · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
                have hj : j ≤ n := by omega
                have hst : run prog ro mem0 orc (j+1) s
                    = run prog ro mem0 orc j (exec ro mem0 orc i s) := by
                  simp only [run, hh', Bool.false_eq_true, ite_false, hi]
                rw [hst]
                exact run_nofail prog n (exec ro mem0 orc i s) he' hf j hj
            · rw [he] at hf
              rw [run_halted prog ro mem0 orc n (s.fail e) (fail_facts s e hs).1] at hf
              simp [State.fail, hs] at hf

theorem run_pc_upto (prog : Array Instr) (n : Nat) (s : State W32 Int)
    (hs : s.err = none) (hf : (run prog ro mem0 orc n s).err = none) :
    ∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨ (run prog ro mem0 orc k s).pc < prog.size := by
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt hk
  rcases run_nofail prog n s hs hf k hkn with hhalt | herr
  · exact Or.inl hhalt
  · by_cases hh : (run prog ro mem0 orc k s).halted = true
    · exact Or.inl hh
    · right
      generalize ht : run prog ro mem0 orc k s = t
      have hnh : t.halted = false := by rw [← ht]; simpa using hh
      by_cases hsize : t.pc < prog.size
      · exact hsize
      · exfalso
        have hge : prog.size ≤ t.pc := Nat.le_of_not_lt hsize
        have hnone : prog[t.pc]? = none := Array.getElem?_eq_none hge
        have hstep : run prog ro mem0 orc (k+1) s = t.fail "pc out of program" := by
          rw [run_add prog ro mem0 orc k 1 s, ht]
          simp only [run, hnh, Bool.false_eq_true, ite_false, hnone]
        have hsplit : n = (k + 1) + (n - (k + 1)) := by omega
        have hfin : run prog ro mem0 orc n s
            = run prog ro mem0 orc (n - (k+1)) (run prog ro mem0 orc (k+1) s) := by
          have h := run_add prog ro mem0 orc (k+1) (n - (k+1)) s
          rw [← hsplit] at h
          exact h
        rw [hfin, hstep] at hf
        have herr' : t.err = none := by rw [← ht]; exact herr
        have hfail : (t.fail "pc out of program").err = some "pc out of program" := by
          simp [State.fail, herr']
        rw [run_halted prog ro mem0 orc (n - (k+1)) (t.fail "pc out of program") (by simp [State.fail, herr'])] at hf
        rw [hfail] at hf
        simp at hf

end Inv

end ExecRen

end Hashtree.Asm.X86
