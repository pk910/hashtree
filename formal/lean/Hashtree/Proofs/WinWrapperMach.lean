import Hashtree.Proofs.WinWrapperPre

/-!
# R5: windows wrapper machine lemmas (alignment, call marker, epilogue)

Symbolic/concrete `exec` lemmas for `Kernels/X86Win/WrapperWindows`:
`align_homW_*` (`ANDQ $-32, SP` on the prefix's end state), `push_homW` (`CALL`: the
pushed return marker gives the windows kernel entry state), the marker and saved-`rbp`
lookup facts, and `post_runW` (the five-instruction epilogue for frame `F`).
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace Hashtree.Proofs.WinWrapper
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Proofs.WrapperAmd64 (m0W l10 l10_eval sAt_eval getG_of pushRet
  lkIs lkIs_sound readCell_eqm pbRest_eqm loadVal_eqm loadVal_ptr run_step
  getG_setG_self getG_setG_ne)

/-- `ANDQ $-32, SP` on the prefix's end state. -/
def alignStep (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CState) : CState :=
  exec 4 m orc alignI s

theorem align_homW_shipped (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool)
    (hA : σ 10 + 8 = (σ 9 + 1016) - (σ 9 + 1016) % 32) :
    alignStep m orc (mapState env σ (KpreW shippedFrame)) = mapState env σ (KalW shippedFrame) := by
  have hsp : (mapState env σ (KpreW shippedFrame)).getG 4 = .ptr ⟨rStack, σ 9 + 1016⟩ := by
    rw [getG_hom, getG_of _ _ _ KpreW_shipped_rsp]
    simp only [mapVal, mapAddr, aW, sAt_eval, shippedFrame]; congr 2; omega
  have hh : (mapState env σ (KpreW shippedFrame)).halted = false := by
    simp only [mapState, KpreW_shipped_halted]
  simp only [alignStep, exec, alignI, hh, Bool.false_eq_true, ite_false]
  simp [okOr, gCtl, hsp, andInt, Ctl.asInt, Ctl.ofInt, bind, Except.bind, pure, Except.pure]
  simp only [mapState, KalW, clearFlags, State.setG, State.next, KpreW_shipped_pc, List.map_set,
    mapVal, mapAddr, l10_eval]
  congr 4
  omega

theorem align_homW_fixed (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    alignStep m orc (mapState env σ (KpreW fixedFrame)) = mapState env σ (KalW fixedFrame) := by
  have hsp : (mapState env σ (KpreW fixedFrame)).getG 4 = .ptr ⟨rStack, σ 9 - 8⟩ := by
    rw [getG_hom, getG_of _ _ _ KpreW_fixed_rsp]
    simp only [mapVal, mapAddr, aW, sAt_eval, fixedFrame]; congr 2; omega
  have hh : (mapState env σ (KpreW fixedFrame)).halted = false := by
    simp only [mapState, KpreW_fixed_halted]
  simp only [alignStep, exec, alignI, hh, Bool.false_eq_true, ite_false]
  simp [okOr, gCtl, hsp, andInt, Ctl.asInt, Ctl.ofInt, bind, Except.bind, pure, Except.pure]
  simp only [mapState, KalW, clearFlags, State.setG, State.next, KpreW_fixed_pc, List.map_set,
    mapVal, mapAddr, l10_eval]
  congr 4
  omega

/-- `CALL`: the pushed return marker gives the windows kernel entry state `KCW F`. -/
theorem push_homW (F : Int) (env : Key → W32) (σ : Nat → Int)
    (hlen : (KpreW F).gpr.length = 16) :
    { pushRet (mapState env σ (KalW F)) with pc := 0 } = mapState env σ (KCW F) := by
  have h4 : (mapState env σ (KalW F)).getG 4 = .ptr (mapAddr σ aKW) := by
    rw [getG_hom]
    have : (KalW F).getG 4 = .ptr aKW := by
      simp only [KalW, State.getG, aKW]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; decide)]; rfl
    rw [this]; rfl
  simp only [pushRet, h4, KCW]
  rw [← mapAddr_plusI, show (Val.ptr (⟨rRet, 0⟩ : Addr Int) : Val W32 Int) =
      mapVal env σ (.ptr ⟨rRet, Lin.ofInt 0⟩) from by
    simp [mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC], ← storeVal_hom,
    show (Val.ptr (mapAddr σ (aKW.plusI (-8))) : Val W32 Int) = mapVal env σ (.ptr (aKW.plusI (-8))) from rfl,
    ← setG_hom]
  rfl

/-! ## The call's log: the return marker over the saved `rbp` -/

theorem KCW_mem_split_shipped : (KCW shippedFrame).mem = (KCW shippedFrame).mem.take 8 ++
    (KpreW shippedFrame).mem := by decide +kernel
theorem KCW_mem_split_fixed : (KCW fixedFrame).mem = (KCW fixedFrame).mem.take 8 ++
    (KpreW fixedFrame).mem := by decide +kernel

theorem markerW_facts_shipped : ∀ p ∈ (KCW shippedFrame).mem.take 8, p.1.region = rStack ∧
    p.1.off.c = List.replicate 10 0 ++ [1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 8 := by decide +kernel
theorem markerW_facts_fixed : ∀ p ∈ (KCW fixedFrame).mem.take 8, p.1.region = rStack ∧
    p.1.off.c = List.replicate 10 0 ++ [1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 8 := by decide +kernel

theorem markerW_lk_shipped : ∀ k : Nat, k < 8 →
    lkIs ⟨rStack, l10 k⟩ (KCW shippedFrame).mem (.pb ⟨rRet, Lin.ofInt 0⟩ k) = true := by
  decide +kernel
theorem markerW_lk_fixed : ∀ k : Nat, k < 8 →
    lkIs ⟨rStack, l10 k⟩ (KCW fixedFrame).mem (.pb ⟨rRet, Lin.ofInt 0⟩ k) = true := by
  decide +kernel

theorem bpW_facts_shipped : ∀ p ∈ (KpreW shippedFrame).mem, p.1.region = rStack ∧
    p.1.off.c = stkC ∧ -8 ≤ p.1.off.k ∧ p.1.off.k < 0 := by decide +kernel
theorem bpW_facts_fixed : ∀ p ∈ (KpreW fixedFrame).mem, p.1.region = rStack ∧
    p.1.off.c = stkC ∧ -8 ≤ p.1.off.k ∧ p.1.off.k < 0 := by decide +kernel

theorem bpW_lk_shipped : ∀ k : Nat, k < 8 →
    lkIs ⟨rStack, sAt (-8 + k)⟩ (KpreW shippedFrame).mem (.pb ⟨rStack, Lin.sym 6⟩ k) = true := by
  decide +kernel
theorem bpW_lk_fixed : ∀ k : Nat, k < 8 →
    lkIs ⟨rStack, sAt (-8 + k)⟩ (KpreW fixedFrame).mem (.pb ⟨rStack, Lin.sym 6⟩ k) = true := by
  decide +kernel

/-! ## The epilogue (`MOVQ BX, SP ; MOVQ R12, R8 ; ADDQ $F, SP ; POPQ BP ; RET`) -/

/-- The windows epilogue for frame `F`: from `pc = 0` with `rbx` = frame base `x`, it
restores `rsp` (to `x + F + 16`), `rbp` from `[x + F]`, `r8` from `r12`, returns by `RET`
reading `[x + F + 8]`, and leaves the memory alone. -/
theorem post_runW (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CState) (x : Int) (F : Int)
    (bp : Addr Int) (r8v : Val W32 Int)
    (hpc : s.pc = 0) (hh : s.halted = false) (hl : 12 < s.gpr.length)
    (h3 : s.getG 3 = .ptr ⟨rStack, x⟩) (h12 : s.getG 12 = r8v)
    (hbp : ∀ k : Nat, k < 8 → readCell m s ((⟨rStack, x + F⟩ : Addr Int).plusI k) = .ok (.pb bp k))
    (hret : ∀ k : Nat, k < 8 → readCell m s ((⟨rStack, x + F + 8⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rRet, 0⟩ k)) :
    (run (post F) 4 m orc 5 s).halted = true ∧ (run (post F) 4 m orc 5 s).err = s.err ∧
      (run (post F) 4 m orc 5 s).tail = s.tail ∧ (run (post F) 4 m orc 5 s).mem = s.mem ∧
      (run (post F) 4 m orc 5 s).getG 4 = .ptr ⟨rStack, x + F + 8 + 8⟩ ∧
      (run (post F) 4 m orc 5 s).getG 5 = .ptr bp ∧
      (run (post F) 4 m orc 5 s).getG 8 = r8v := by
  have hlen : ∀ (t : CState) (i : Nat) (v : Val W32 Int), (t.setG i v).gpr.length = t.gpr.length := by
    intro t i v; simp [State.setG]
  -- MOVQ BX, SP
  have e1 : exec 4 m orc (.mov 64 4 (.reg 3)) s = (s.setG 4 (s.getG 3)).next := by
    simp [exec, hh, okOr, pure, Except.pure]
  let s1 := (s.setG 4 (s.getG 3)).next
  have g1 : s1.getG 4 = .ptr ⟨rStack, x⟩ := by
    show (s.setG 4 (s.getG 3)).getG 4 = _
    rw [getG_setG_self _ _ _ (by omega), h3]
  -- MOVQ R12, R8
  have hh1 : s1.halted = false := hh
  have e2 : exec 4 m orc (.mov 64 8 (.reg 12)) s1 = (s1.setG 8 (s1.getG 12)).next := by
    simp [exec, hh1, okOr, pure, Except.pure]
  let s2 := (s1.setG 8 (s1.getG 12)).next
  have g2 : s2.getG 8 = r8v := by
    show (s1.setG 8 (s1.getG 12)).getG 8 = _
    rw [getG_setG_self _ _ _ (by simp [s1, State.next, State.setG]; omega)]
    show (s.setG 4 (s.getG 3)).getG 12 = _
    rw [getG_setG_ne _ 12 4 _ (by decide)]
    exact h12
  -- ADDQ $F, SP
  let s3 := (setFlags (s2.setG 4 (.ptr ⟨rStack, x + F⟩)) (x + F) 0).next
  have hh2 : s2.halted = false := hh
  have e3 : exec 4 m orc (.alu .add 64 4 (.imm F)) s2 = s3 := by
    have g2' : s2.getG 4 = .ptr ⟨rStack, x⟩ := by
      show (s1.setG 8 _).getG 4 = _
      rw [getG_setG_ne _ 4 8 _ (by decide)]
      exact g1
    simp [exec, hh2, okOr, gCtl, g2', bind, Except.bind, pure, Except.pure, Ctl.add, Ctl.ofInt,
      rNum, rStack]
    rfl
  -- POPQ BP
  have g3 : s3.getG 4 = .ptr ⟨rStack, x + F⟩ := by
    show (s2.setG 4 _).getG 4 = _
    rw [getG_setG_self _ _ _ (by simp [s2, s1, State.next, State.setG]; omega)]
  have lv3 : loadVal m s3 ⟨rStack, x + F⟩ = .ok (.ptr bp) := by
    rw [loadVal_eqm m s s3 rfl]
    exact loadVal_ptr m s _ bp hbp
  let s4 := ((s3.setG 5 (.ptr bp)).setG 4 (.ptr ((⟨rStack, x + F⟩ : Addr Int).plusI 8))).next
  have hh3 : s3.halted = false := hh
  have e4 : exec 4 m orc (.pop 5) s3 = s4 := by
    simp [exec, hh3, okOr, g3, lv3, bind, Except.bind, pure, Except.pure, rsp]
    rfl
  -- RET
  have g4 : s4.getG 4 = .ptr ⟨rStack, x + F + 8⟩ := by
    show ((s3.setG 5 _).setG 4 _).getG 4 = _
    rw [getG_setG_self _ _ _ (by simp [s3, s2, s1, State.next, State.setG, setFlags]; omega)]
    simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
  have lv4 : loadVal m s4 ⟨rStack, x + F + 8⟩ = .ok (.ptr ⟨rRet, 0⟩) := by
    rw [loadVal_eqm m s s4 rfl]
    exact loadVal_ptr m s _ _ hret
  let s5 := halt (s4.setG 4 (.ptr ((⟨rStack, x + F + 8⟩ : Addr Int).plusI 8)))
  have hh4 : s4.halted = false := hh
  have e5 : exec 4 m orc .ret s4 = s5 := by
    simp [exec, hh4, okOr, g4, lv4, bind, Except.bind, pure, Except.pure, rsp, rRet]
    rfl
  have p1 : s1.pc = 1 := by show s.pc + 1 = 1; omega
  have p2 : s2.pc = 2 := by show s1.pc + 1 = 2; omega
  have p3 : s3.pc = 3 := by show s2.pc + 1 = 3; omega
  have p4 : s4.pc = 4 := by show s3.pc + 1 = 4; omega
  have r : run (post F) 4 m orc 5 s = s5 := by
    rw [run_step (post F) m orc 4 s (.mov 64 4 (.reg 3)) hh (by rw [hpc]; rfl), e1]
    rw [run_step (post F) m orc 3 s1 (.mov 64 8 (.reg 12)) hh (by rw [p1]; rfl), e2]
    rw [run_step (post F) m orc 2 s2 (.alu .add 64 4 (.imm F)) hh (by rw [p2]; rfl), e3]
    rw [run_step (post F) m orc 1 s3 (.pop 5) hh (by rw [p3]; rfl), e4]
    rw [run_step (post F) m orc 0 s4 .ret hh (by rw [p4]; rfl), e5]
    rfl
  rw [r]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show (s4.setG 4 _).getG 4 = _
    rw [getG_setG_self _ _ _ (by simp [s4, s3, s2, s1, State.next, State.setG, setFlags]; omega)]
    simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
  · show (s4.setG 4 _).getG 5 = _
    rw [getG_setG_ne _ 5 4 _ (by decide)]
    show (((s3.setG 5 _).setG 4 _)).getG 5 = _
    rw [getG_setG_ne _ 5 4 _ (by decide),
      getG_setG_self _ _ _ (by simp [s3, s2, s1, State.next, State.setG, setFlags]; omega)]
  · show (s4.setG 4 _).getG 8 = _
    rw [getG_setG_ne _ 8 4 _ (by decide)]
    show (((s3.setG 5 _).setG 4 _)).getG 8 = _
    rw [getG_setG_ne _ 8 4 _ (by decide), getG_setG_ne _ 8 5 _ (by decide)]
    show (s2.setG 4 (Val.ptr { region := rStack, off := x + F })).getG 8 = _
    rw [getG_setG_ne _ 8 4 _ (by decide)]
    exact g2

end Hashtree.Proofs.WinWrapper
