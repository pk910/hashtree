import Hashtree.Proofs.WrapperEntry
import Hashtree.Asm.X86Loop

/-! The wrapper's prefix and the kernel call state (symbolic facts, decided). -/

set_option maxRecDepth 20000

namespace Hashtree.Proofs.WrapperAmd64
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.WrapperLinux

/-! ## The wrapper's semantics -/

/-- `ANDQ $-32, SP`. -/
def alignStep (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CState) : CState := exec 4 m orc alignI s

/-- `CALL kernel`: push a return marker, run the kernel `N` steps (it returns via `RET`, which pops the
marker), and continue the caller at the start of `post`. -/
def pushRet (s : CState) : CState :=
  match s.getG 4 with
  | .ptr sp => (storeVal s (sp.plusI (-8)) (.ptr ⟨rRet, 0⟩)).setG 4 (.ptr (sp.plusI (-8)))
  | _ => s.fail "call: rsp not a pointer"

def callK (kprog : Array Instr) (N : Nat) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CState) : CState :=
  let r := run kprog 4 m orc N { pushRet s with pc := 0 }
  { r with pc := 0, halted := false }

/-- The whole call for a given kernel. -/
def wrapRun (kprog : Array Instr) (N : Nat) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CState) : CState :=
  run post 4 m orc 4 (callK kprog N m orc (alignStep m orc (run pre 4 m orc 9 s)))

/-! ## The prefix (symbolic) -/

def Kpre : State E Lin := abstract (run pre 4 m0W (fun _ => false) 9 wEntry)

theorem slicePre : sliceCheck pre 4 m0W (fun _ => false) 9 wEntry Kpre [] = true := by decide +kernel

theorem Kpre_assume : Kpre.assume = [] := by decide +kernel

def l10 (k : Int) : Lin := ⟨k, List.replicate 10 0 ++ [1]⟩

/-- After the alignment: rsp = `s10 + 8` (symbol 10 names the kernel's entry rsp, `A - 8`). -/
def Kal : State E Lin := { Kpre with gpr := Kpre.gpr.set 4 (.ptr ⟨rStack, l10 8⟩), flags := none, pc := 10 }

def aK : Addr Lin := ⟨rStack, l10 8⟩

/-- The kernel's entry state. -/
def KC : State E Lin :=
  { (storeVal Kal (aK.plusI (-8)) (.ptr ⟨rRet, Lin.ofInt 0⟩)).setG 4 (.ptr (aK.plusI (-8))) with pc := 0 }

/-- Kernel symbols in terms of the wrapper's: input, output, count, -, -, rbx = `SPe - 2056`,
rbp = `SPe - 8`, r12 = `SPe - 0x788`, g, rsp = symbol 10. -/
def tauC : List Lin := [Lin.sym 0, Lin.sym 1, Lin.sym 2, Lin.sym 3, Lin.sym 4, sAt (-2056), sAt (-8), sAt (-1928),
  Lin.sym 8, l10 0]

theorem KC_shape : { KC with mem := [], assume := [] } = entryW.substL tauC := by decide +kernel

theorem Kpre_rsp : Kpre.gpr[4]? = some (.ptr ⟨rStack, sAt (-8)⟩) := by decide +kernel
theorem Kpre_pc : Kpre.pc = 9 := by decide +kernel
theorem Kpre_halted : Kpre.halted = false := by decide +kernel
theorem Kpre_err : Kpre.err = none := by decide +kernel
theorem Kpre_len : Kpre.gpr.length = 16 := by decide +kernel
theorem entryW_nOnly : entryW.nOnly = true := by decide +kernel


theorem l10_eval (σ : Nat → Int) (k : Int) : (l10 k).eval σ = k + σ 10 := by
  simp [l10, Lin.eval, dotC, List.replicate]

theorem sAt_eval (σ : Nat → Int) (k : Int) : (sAt k).eval σ = k + σ 9 := by
  simp [sAt, stkC, Lin.eval, dotC, List.replicate]

theorem getG_of {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) (v : Val α γ) (h : s.gpr[i]? = some v) :
    s.getG i = v := by
  simp [State.getG, List.getD_eq_getElem?_getD, h]

/-- `ANDQ $-32, SP` on the prefix's end state: rsp := `s10 + 8` when `σ 10 + 8` is `SPe - 8` rounded down. -/
theorem align_hom (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    alignStep m orc (mapState env σ Kpre) = mapState env σ Kal := by
  have hsp : (mapState env σ Kpre).getG 4 = .ptr ⟨rStack, σ 9 - 8⟩ := by
    rw [getG_hom, getG_of _ _ _ Kpre_rsp]
    simp only [mapVal, mapAddr, sAt_eval]; congr 2; omega
  have hh : (mapState env σ Kpre).halted = false := by simp only [mapState, Kpre_halted]
  simp only [alignStep, exec, alignI, hh, Bool.false_eq_true, ite_false]
  simp [okOr, gCtl, hsp, andInt, Ctl.asInt, Ctl.ofInt, bind, Except.bind, pure, Except.pure]
  simp only [mapState, Kal, clearFlags, State.setG, State.next, Kpre_pc, List.map_set, mapVal, mapAddr, l10_eval]
  congr 4
  omega

/-- `CALL`: the pushed return marker gives the kernel's entry state `KC`. -/
theorem push_hom (env : Key → W32) (σ : Nat → Int) :
    { pushRet (mapState env σ Kal) with pc := 0 } = mapState env σ KC := by
  have h4 : (mapState env σ Kal).getG 4 = .ptr (mapAddr σ aK) := by
    rw [getG_hom]
    have : Kal.getG 4 = .ptr aK := by
      simp only [Kal, State.getG, aK]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [Kpre_len]; decide)]; rfl
    rw [this]; rfl
  simp only [pushRet, h4, KC]
  rw [← mapAddr_plusI, show (Val.ptr (⟨rRet, 0⟩ : Addr Int) : Val W32 Int) = mapVal env σ (.ptr ⟨rRet, Lin.ofInt 0⟩) from by
    simp [mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC], ← storeVal_hom,
    show (Val.ptr (mapAddr σ (aK.plusI (-8))) : Val W32 Int) = mapVal env σ (.ptr (aK.plusI (-8))) from rfl, ← setG_hom]
  rfl


/-! ## The kernel call's log: the return marker over the saved rbp -/

theorem KC_mem_split : KC.mem = KC.mem.take 8 ++ Kpre.mem := by decide +kernel

theorem marker_facts : ∀ p ∈ KC.mem.take 8, p.1.region = rStack ∧ p.1.off.c = List.replicate 10 0 ++ [1] ∧
    0 ≤ p.1.off.k ∧ p.1.off.k < 8 := by decide +kernel

def lkIs (a : Addr Lin) (L : List (Addr Lin × Cell E Lin)) (c : Cell E Lin) : Bool :=
  match lookup a L with
  | .ok (some c') => c' == c
  | _ => false

theorem lkIs_sound (a : Addr Lin) (L : List (Addr Lin × Cell E Lin)) (c : Cell E Lin) (h : lkIs a L c = true) :
    lookup a L = .ok (some c) := by
  simp only [lkIs] at h
  split at h
  · rename_i c' hl; simp only [beq_iff_eq] at h; rw [hl, h]
  · cases h

theorem marker_lk : ∀ k : Nat, k < 8 → lkIs ⟨rStack, l10 k⟩ KC.mem (.pb ⟨rRet, Lin.ofInt 0⟩ k) = true := by
  decide +kernel

theorem bp_facts : ∀ p ∈ Kpre.mem, p.1.region = rStack ∧ p.1.off.c = stkC ∧ -8 ≤ p.1.off.k ∧ p.1.off.k < 0 := by
  decide +kernel

theorem bp_lk : ∀ k : Nat, k < 8 → lkIs ⟨rStack, sAt (-8 + k)⟩ Kpre.mem (.pb ⟨rStack, Lin.sym 6⟩ k) = true := by
  decide +kernel

/-! ## The epilogue (concrete) -/

theorem readCell_eqm (m : Addr Int → Cell W32 Int) (s s' : CState) (h : s'.mem = s.mem) (a : Addr Int) :
    readCell m s' a = readCell m s a := by simp only [readCell, h]

theorem pbRest_eqm (m : Addr Int → Cell W32 Int) (s s' : CState) (h : s'.mem = s.mem) (p a : Addr Int) :
    ∀ n k, pbRest m s' p a n k = pbRest m s p a n k
  | 0, _ => rfl
  | n + 1, k => by simp only [pbRest, readCell_eqm m s s' h, pbRest_eqm m s s' h p a n]

theorem loadVal_eqm (m : Addr Int → Cell W32 Int) (s s' : CState) (h : s'.mem = s.mem) (a : Addr Int) :
    loadVal m s' a = loadVal m s a := by
  simp only [loadVal, readCell_eqm m s s' h, pbRest_eqm m s s' h, loadLane, readCell_eqm m s s' h]

/-- Eight cells holding the bytes of pointer `p` load as `p`. -/
theorem loadVal_ptr (m : Addr Int → Cell W32 Int) (s : CState) (a p : Addr Int)
    (h : ∀ k : Nat, k < 8 → readCell m s (a.plusI k) = .ok (.pb p k)) : loadVal m s a = .ok (.ptr p) := by
  have h0 : readCell m s a = .ok (.pb p 0) := by
    have := h 0 (by decide)
    have e : a.plusI ((0 : Nat) : Int) = a := by
      obtain ⟨r, o⟩ := a; simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
    rwa [e] at this
  have hs : AddrEq.same p p = some true := by simp [AddrEq.same]
  simp only [loadVal, h0, bind, Except.bind]
  simp only [pbRest, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), isPb, hs, bind, Except.bind, pure, Except.pure]
  rfl

theorem run_step (prog : Array Instr) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (n : Nat) (s : CState)
    (i : Instr) (hh : s.halted = false) (hi : prog[s.pc]? = some i) :
    run prog 4 m orc (n + 1) s = run prog 4 m orc n (exec 4 m orc i s) := by
  simp [run, hh, hi]

theorem getG_setG_self {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) (v : Val α γ) (h : i < s.gpr.length) :
    (s.setG i v).getG i = v := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem getG_setG_ne {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i j : Nat) (v : Val α γ) (h : i ≠ j) :
    (s.setG j v).getG i = s.getG i := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem post_run (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CState) (x : Int) (bp : Addr Int)
    (hpc : s.pc = 0) (hh : s.halted = false) (hl : 5 < s.gpr.length) (h3 : s.getG 3 = .ptr ⟨rStack, x⟩)
    (hbp : ∀ k : Nat, k < 8 → readCell m s ((⟨rStack, x + 2048⟩ : Addr Int).plusI k) = .ok (.pb bp k))
    (hret : ∀ k : Nat, k < 8 → readCell m s ((⟨rStack, x + 2048 + 8⟩ : Addr Int).plusI k) = .ok (.pb ⟨rRet, 0⟩ k)) :
    (run post 4 m orc 4 s).halted = true ∧ (run post 4 m orc 4 s).err = s.err ∧
      (run post 4 m orc 4 s).tail = s.tail ∧ (run post 4 m orc 4 s).mem = s.mem ∧
      (run post 4 m orc 4 s).getG 4 = .ptr ⟨rStack, x + 2048 + 8 + 8⟩ ∧ (run post 4 m orc 4 s).getG 5 = .ptr bp := by
  have hl' : ∀ (t : CState) (i : Nat) (v : Val W32 Int), (t.setG i v).gpr.length = t.gpr.length := by
    intro t i v; simp [State.setG]
  -- MOVQ BX, SP
  have e1 : exec 4 m orc (.mov 64 4 (.reg 3)) s = (s.setG 4 (s.getG 3)).next := by
    simp [exec, hh, okOr, pure, Except.pure]
  -- ADDQ $0x800, SP
  let s1 := (s.setG 4 (s.getG 3)).next
  have g1 : s1.getG 4 = .ptr ⟨rStack, x⟩ := by
    show (s.setG 4 (s.getG 3)).getG 4 = _
    rw [getG_setG_self _ _ _ (by omega), h3]
  let s2 := (setFlags (s1.setG 4 (.ptr ⟨rStack, x + 2048⟩)) (x + 2048) 0).next
  have e2 : exec 4 m orc (.alu .add 64 4 (.imm 0x800)) s1 = s2 := by
    have hh1 : s1.halted = false := hh
    simp [exec, hh1, okOr, gCtl, g1, bind, Except.bind, pure, Except.pure, Ctl.add, Ctl.ofInt, rNum, rStack, s2]
  -- POPQ BP
  have g2 : s2.getG 4 = .ptr ⟨rStack, x + 2048⟩ := by
    show (s1.setG 4 _).getG 4 = _
    rw [getG_setG_self _ _ _ (by simp only [s1, State.next, hl' s 4]; omega)]
  have lv2 : loadVal m s2 ⟨rStack, x + 2048⟩ = .ok (.ptr bp) := by
    rw [loadVal_eqm m s s2 rfl]; exact loadVal_ptr m s _ bp hbp
  let s3 := ((s2.setG 5 (.ptr bp)).setG 4 (.ptr ((⟨rStack, x + 2048⟩ : Addr Int).plusI 8))).next
  have e3 : exec 4 m orc (.pop 5) s2 = s3 := by
    have hh2 : s2.halted = false := hh
    simp [exec, hh2, okOr, g2, lv2, bind, Except.bind, pure, Except.pure, rsp, s3]
  -- RET
  have g3 : s3.getG 4 = .ptr ⟨rStack, x + 2048 + 8⟩ := by
    show ((s2.setG 5 _).setG 4 _).getG 4 = _
    rw [getG_setG_self _ _ _ (by simp only [hl', s2, s1, State.next, setFlags]; omega)]
    simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
  have lv3 : loadVal m s3 ⟨rStack, x + 2048 + 8⟩ = .ok (.ptr ⟨rRet, 0⟩) := by
    rw [loadVal_eqm m s s3 rfl]; exact loadVal_ptr m s _ _ hret
  let s4 := halt (s3.setG 4 (.ptr ((⟨rStack, x + 2048 + 8⟩ : Addr Int).plusI 8)))
  have e4 : exec 4 m orc .ret s3 = s4 := by
    have hh3 : s3.halted = false := hh
    simp [exec, hh3, okOr, g3, lv3, bind, Except.bind, pure, Except.pure, rsp, s4, rRet]
  have p1 : s1.pc = 1 := by show s.pc + 1 = 1; omega
  have p2 : s2.pc = 2 := by show s1.pc + 1 = 2; omega
  have p3 : s3.pc = 3 := by show s2.pc + 1 = 3; omega
  have r : run post 4 m orc 4 s = s4 := by
    rw [run_step post m orc 3 s (.mov 64 4 (.reg 3)) hh (by rw [hpc]; rfl), e1]
    rw [run_step post m orc 2 s1 (.alu .add 64 4 (.imm 0x800)) hh (by rw [p1]; rfl), e2]
    rw [run_step post m orc 1 s2 (.pop 5) hh (by rw [p2]; rfl), e3]
    rw [run_step post m orc 0 s3 .ret hh (by rw [p3]; rfl), e4]
    rfl
  rw [r]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (s3.setG 4 _).getG 4 = _
    rw [getG_setG_self _ _ _ (by simp only [hl', s3, s2, s1, State.next, setFlags]; omega)]
    simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
  · show (s3.setG 4 _).getG 5 = _
    rw [getG_setG_ne _ 5 4 _ (by decide)]
    show (((s2.setG 5 _).setG 4 _)).getG 5 = _
    rw [getG_setG_ne _ 5 4 _ (by decide), getG_setG_self _ _ _ (by simp only [hl', s2, s1, State.next, setFlags]; omega)]

end Hashtree.Proofs.WrapperAmd64
