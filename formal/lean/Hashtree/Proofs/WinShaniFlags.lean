import Hashtree.Proofs.WinShaniFront
import Hashtree.Proofs.WinNs

/-!
# R5: flags-insensitivity of the `shani_x2` body entry

The windows and linux prologues of `shani_x2` set *different* flags:

```
linux   : sub rsp, 88    -- flags := some (entry_rsp, 88)
windows : sub rsp, 248   -- flags := some (entry_rsp, 248)
```

`exec` reads the flags in exactly two places (`jcc` and `jccTail`); every other instruction
leaves them untouched.  The body entry is therefore insensitive to the prologue difference: the
first four body instructions

```
pc 11 : vload 4 xmm8, [ro + 256]     -- straight line
pc 12 : lea  rax,     [ro + 0]       -- straight line
pc 13 : lea  r9,      [ro + 304]     -- straight line
pc 14 : cmp  r8, 2                   -- overwrites the flags
```

contain no branch before the `cmp`, and the `cmp` writes the flags from registers only, so the
state after four steps is *identical* whether one starts with the linux flags or the windows
ones.  From there on the difference cannot resurface.

This is what lets the composition of `formal/notes/R5.md` section 6 apply the linux body
certificate (whose body-entry flags are those of `sub rsp, 88`) to the shipped windows body
(whose entry flags are those of `sub rsp, 248`).
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinShaniFront
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinShaniFlags

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

/-! ## `exec` formulas for the three straight-line forms -/

theorem exec_vload_ok {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (vex : Bool) (w d : Nat) (src : VSrc) (v : List W32)
    (hh : s.halted = false) (hv : readVSrc ro mem0 s w src = .ok v) :
    exec ro mem0 orc (.vload vex w d src) s = (setVec s vex w d v).next := by
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [hv, Hashtree.Asm.X86.bind_ok_eq, Hashtree.Proofs.WinShaniFront.okOr_pure]

theorem exec_lea_ok {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (d : Nat) (m : MemRef) (a : Addr Int)
    (hh : s.halted = false) (he : effAddr ro s m = .ok a) :
    exec ro mem0 orc (.lea d m) s = (s.setG d (.ptr a)).next := by
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [he, Hashtree.Asm.X86.bind_ok_eq, Hashtree.Proofs.WinShaniFront.okOr_pure]

theorem exec_cmp64_ok {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (a : Nat) (b : GSrc) (x y : Addr Int)
    (hh : s.halted = false) (hx : gCtl s (.reg a) = .ok x) (hy : gCtl s b = .ok y)
    (hr : y.region = rNum ∨ y.region = x.region) :
    exec ro mem0 orc (.cmp 64 a b) s = (setFlags s x.off y.off).next := by
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [ite_eq_left trivial]
  rw [hx, Hashtree.Asm.X86.bind_ok_eq, hy, Hashtree.Asm.X86.bind_ok_eq, ite_eq_left hr,
    Hashtree.Proofs.WinShaniFront.okOr_pure]

/-- A `rip`-relative (rodata) memory operand: the effective address does not depend on the state. -/
theorem effAddr_ro (ro : Region) (s : State W32 Int) (o : Int) (d : Int) :
    effAddr ro s { base := none, index := none, scale := 1, disp := d, ro := some o }
      = .ok ((⟨ro, Ctl.ofInt o⟩ : Addr Int).plusI d) := by
  simp only [effAddr, baseAddr]

/-! ## The four concrete body-entry instructions of the shipped stream -/

abbrev m256 : VSrc := .mem { base := none, index := none, scale := 1, disp := 0, ro := some 256 }

/-- The `vload 4 xmm8, [ro+256]` at pc 11. -/
abbrev i11 : Instr := .vload false 4 8 m256

/-- The `lea rax, [ro+0]` at pc 12. -/
abbrev i12 : Instr := .lea 0 { base := none, index := none, scale := 1, disp := 0, ro := some 0 }

/-- The `lea r9, [ro+304]` at pc 13. -/
abbrev i13 : Instr := .lea 9 { base := none, index := none, scale := 1, disp := 0, ro := some 304 }

/-- The `cmp r8, 2` at pc 14 that overwrites the prologue flags. -/
abbrev i14 : Instr := .cmp 64 8 (.imm 2)

theorem lookup11 : winProg[11]? = some i11 := by decide +kernel
theorem lookup12 : winProg[12]? = some i12 := by decide +kernel
theorem lookup13 : winProg[13]? = some i13 := by decide +kernel
theorem lookup14 : winProg[14]? = some i14 := by decide +kernel

/-- The rodata pointer loaded by the `lea` at pc 12. -/
abbrev p0 (ro : Region) : Addr Int := (⟨ro, Ctl.ofInt (0 : Int)⟩ : Addr Int).plusI 0

/-- The rodata pointer loaded by the `lea` at pc 13. -/
abbrev p304 (ro : Region) : Addr Int := (⟨ro, Ctl.ofInt (304 : Int)⟩ : Addr Int).plusI 0

/-- The comparison operand of `cmp r8, 2`. -/
abbrev yImm : Addr Int := (⟨rNum, Ctl.ofInt (2 : Int)⟩ : Addr Int)

/-- `effAddr` of the pc-12 `lea` operand, in `p0` form. -/
theorem effAddr_i12 (ro : Region) (s : State W32 Int) :
    effAddr ro s { base := none, index := none, scale := 1, disp := 0, ro := some 0 }
      = .ok (p0 ro) :=
  effAddr_ro ro s 0 0

/-- `effAddr` of the pc-13 `lea` operand, in `p304` form. -/
theorem effAddr_i13 (ro : Region) (s : State W32 Int) :
    effAddr ro s { base := none, index := none, scale := 1, disp := 0, ro := some 304 }
      = .ok (p304 ro) :=
  effAddr_ro ro s 304 0

/-- Reading register 8 of a state written through register 0. -/
theorem getG_setG_zero (s : State W32 Int) (v : Val W32 Int) :
    (s.setG 0 v).getG 8 = s.getG 8 :=
  Hashtree.Asm.X86.getG_setG_ne' s 0 8 v (by decide)

/-- Reading register 8 of a state written through register 9. -/
theorem getG_setG_nine (s : State W32 Int) (v : Val W32 Int) :
    (s.setG 9 v).getG 8 = s.getG 8 :=
  Hashtree.Asm.X86.getG_setG_ne' s 9 8 v (by decide)

/-! ## Four steps do not depend on the entry flags -/

/-- One `run` step at a known instruction (`Proofs.WinShaniFront.run_succ_step`). -/
theorem run_one {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (n : Nat) (s t : State W32 Int) (i : Instr) (hh : s.halted = false)
    (hp : winProg[s.pc]? = some i) (he : exec ro mem0 orc i s = t) :
    run winProg ro mem0 orc (n + 1) s = run winProg ro mem0 orc n t := by
  rw [run_succ_step winProg ro mem0 orc n s i hh hp, he]

/-- The straight-line block at the body entry: the state after four steps is the same from the
linux-flags entry state and from the windows-flags entry state. -/
theorem run_four_flags {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (f : Option (Int × Int)) (v : List W32)
    (x : Addr Int) (hh : st.halted = false)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x) :
    run winProg ro mem0 orc 4 (saveSt st a 10)
      = run winProg ro mem0 orc 4 ({ saveSt st a 10 with flags := f }) := by
  let W : State W32 Int := saveSt st a 10
  let W' : State W32 Int := { saveSt st a 10 with flags := f }
  let A1 : State W32 Int := (setVec W false 4 8 v).next
  let A1' : State W32 Int := (setVec W' false 4 8 v).next
  let A2 : State W32 Int := (A1.setG 0 (.ptr (p0 ro))).next
  let A2' : State W32 Int := (A1'.setG 0 (.ptr (p0 ro))).next
  let A3 : State W32 Int := (A2.setG 9 (.ptr (p304 ro))).next
  let A3' : State W32 Int := (A2'.setG 9 (.ptr (p304 ro))).next
  let A4 : State W32 Int := (setFlags A3 x.off yImm.off).next
  -- the entry flags do not enter any of the four steps
  have e1 : exec ro mem0 orc i11 W = A1 := exec_vload_ok W false 4 8 m256 v hh hv
  have e1' : exec ro mem0 orc i11 W' = A1' := exec_vload_ok W' false 4 8 m256 v hh hv
  have e2 : exec ro mem0 orc i12 A1 = A2 :=
    exec_lea_ok A1 0 _ (p0 ro) hh (effAddr_i12 ro A1)
  have e2' : exec ro mem0 orc i12 A1' = A2' :=
    exec_lea_ok A1' 0 _ (p0 ro) hh (effAddr_i12 ro A1')
  have e3 : exec ro mem0 orc i13 A2 = A3 :=
    exec_lea_ok A2 9 _ (p304 ro) hh (effAddr_i13 ro A2)
  have e3' : exec ro mem0 orc i13 A2' = A3' :=
    exec_lea_ok A2' 9 _ (p304 ro) hh (effAddr_i13 ro A2')
  have hx3 : gCtl A3 (.reg 8) = .ok x := by
    simp only [A3, A2, A1, W, gCtl]
    rw [Hashtree.Asm.X86.getG_next, getG_setG_nine, Hashtree.Asm.X86.getG_next,
      getG_setG_zero, Hashtree.Asm.X86.getG_next, Hashtree.Asm.X86.getG_setVec]
    exact hx
  have hx3' : gCtl A3' (.reg 8) = .ok x := by
    simp only [A3', A2', A1', W', gCtl]
    rw [Hashtree.Asm.X86.getG_next, getG_setG_nine, Hashtree.Asm.X86.getG_next,
      getG_setG_zero, Hashtree.Asm.X86.getG_next, Hashtree.Asm.X86.getG_setVec]
    rw [show ({ saveSt st a 10 with flags := f } : State W32 Int).getG 8 = (saveSt st a 10).getG 8
      from rfl]
    exact hx
  have e4 : exec ro mem0 orc i14 A3 = A4 :=
    exec_cmp64_ok A3 8 (.imm 2) x yImm hh hx3 (gCtl_imm A3 2) (Or.inl rfl)
  have e4' : exec ro mem0 orc i14 A3' = (setFlags A3' x.off yImm.off).next :=
    exec_cmp64_ok A3' 8 (.imm 2) x yImm hh hx3' (gCtl_imm A3' 2) (Or.inl rfl)
  have hA1' : A1' = { A1 with flags := f } := rfl
  have hA2' : A2' = { A2 with flags := f } := rfl
  have hA3' : A3' = { A3 with flags := f } := rfl
  have hfin : (setFlags A3' x.off yImm.off).next = A4 := by
    rw [hA3']; rfl
  have lhs : run winProg ro mem0 orc 4 W = A4 := by
    calc run winProg ro mem0 orc 4 W
        = run winProg ro mem0 orc (3 + 1) W := rfl
      _ = run winProg ro mem0 orc 3 (exec ro mem0 orc i11 W) :=
          run_succ_step winProg ro mem0 orc 3 W i11 hh lookup11
      _ = run winProg ro mem0 orc 3 A1 := by rw [e1]
      _ = run winProg ro mem0 orc (2 + 1) A1 := rfl
      _ = run winProg ro mem0 orc 2 (exec ro mem0 orc i12 A1) :=
          run_succ_step winProg ro mem0 orc 2 A1 i12 hh lookup12
      _ = run winProg ro mem0 orc 2 A2 := by rw [e2]
      _ = run winProg ro mem0 orc (1 + 1) A2 := rfl
      _ = run winProg ro mem0 orc 1 (exec ro mem0 orc i13 A2) :=
          run_succ_step winProg ro mem0 orc 1 A2 i13 hh lookup13
      _ = run winProg ro mem0 orc 1 A3 := by rw [e3]
      _ = run winProg ro mem0 orc (0 + 1) A3 := rfl
      _ = run winProg ro mem0 orc 0 (exec ro mem0 orc i14 A3) :=
          run_succ_step winProg ro mem0 orc 0 A3 i14 hh lookup14
      _ = run winProg ro mem0 orc 0 A4 := by rw [e4]
      _ = A4 := rfl
  have rhs : run winProg ro mem0 orc 4 W' = A4 := by
    calc run winProg ro mem0 orc 4 W'
        = run winProg ro mem0 orc (3 + 1) W' := rfl
      _ = run winProg ro mem0 orc 3 (exec ro mem0 orc i11 W') :=
          run_succ_step winProg ro mem0 orc 3 W' i11 hh lookup11
      _ = run winProg ro mem0 orc 3 A1' := by rw [e1']
      _ = run winProg ro mem0 orc (2 + 1) A1' := rfl
      _ = run winProg ro mem0 orc 2 (exec ro mem0 orc i12 A1') :=
          run_succ_step winProg ro mem0 orc 2 A1' i12 hh lookup12
      _ = run winProg ro mem0 orc 2 A2' := by rw [e2']
      _ = run winProg ro mem0 orc (1 + 1) A2' := rfl
      _ = run winProg ro mem0 orc 1 (exec ro mem0 orc i13 A2') :=
          run_succ_step winProg ro mem0 orc 1 A2' i13 hh lookup13
      _ = run winProg ro mem0 orc 1 A3' := by rw [e3']
      _ = run winProg ro mem0 orc (0 + 1) A3' := rfl
      _ = run winProg ro mem0 orc 0 (exec ro mem0 orc i14 A3') :=
          run_succ_step winProg ro mem0 orc 0 A3' i14 hh lookup14
      _ = run winProg ro mem0 orc 0 A4 := by rw [e4', hfin]
      _ = A4 := rfl
  exact lhs.trans rhs.symm

/-- **The flags-insensitivity of the `shani_x2` body.**  Any run of the body that lasts at least
four steps gives the same state from the linux-flags entry state and from the windows-flags entry
state: the first four body instructions are straight-line and the fourth one (`cmp r8, 2`)
overwrites the flags before the first branch. -/
theorem run_flags {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (f : Option (Int × Int)) (v : List W32)
    (x : Addr Int) (hh : st.halted = false)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x) :
    ∀ (n : Nat), 4 ≤ n →
      run winProg ro mem0 orc n (saveSt st a 10)
        = run winProg ro mem0 orc n ({ saveSt st a 10 with flags := f }) := by
  intro n hn
  rw [show n = 4 + (n - 4) from by omega]
  rw [run_add (a := 4) (b := n - 4), run_add (a := 4) (b := n - 4),
    run_four_flags st a f v x hh hv hx]

end Hashtree.Proofs.WinShaniFlags
