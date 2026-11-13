import Hashtree.Asm.ArmRun
import Hashtree.Asm.ArmRename

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# Return-offset relabeling

`x30` holds the address `ret` goes to, and the model's `ret` tests only the *region* of that
address (`rRet`), never the offset: the offset is where the caller resumes, which no kernel
instruction reads.  This module proves that replacing the offset of `x30` (keeping the region)
commutes with a run of an instruction stream that never uses general register 30, so a run proved
from one entry shape (e.g. the symbolic entry cut, whose `x30` offset is the constant 0) is a run
from every other entry shape with the same registers otherwise (e.g. the wrapper's call site,
whose return pc is 1).

The stream hypothesis is the computable predicate `NoTouch`; the scans of the three ARM kernel
streams are `decide` lemmas in the drivers.
-/

namespace Hashtree.Asm.ArmRet
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmRename

/-- `s` with `x30` pointing to `rRet + k`; the region (all `ret` tests) is unchanged. -/
def retOff (k : Int) (s : CS) : CS := s.setG 30 (.ptr ⟨rRet, k⟩)

/-- The post-index register of a memory instruction, when it is a general register. -/
def IdxOk : Idx → Prop
  | .off _ => True
  | .pre _ => True
  | .post _ => True
  | .postR m => m ≠ 30

/-- The instruction touches no general register 30 (as source, destination or writeback base):
then relabeling `x30` is invisible to it. -/
def NoTouch : Instr → Prop
  | .nop => True
  | .movz d _ => d ≠ 30
  | .addi d n _ => d ≠ 30 ∧ n ≠ 30
  | .subi d n _ => d ≠ 30 ∧ n ≠ 30
  | .addr d n m _ => d ≠ 30 ∧ n ≠ 30 ∧ m ≠ 30
  | .adrp d _ => d ≠ 30
  | .addLo12 d n _ => d ≠ 30 ∧ n ≠ 30
  | .wop _ d n m => d ≠ 30 ∧ n ≠ 30 ∧ m ≠ 30
  | .rorw d n _ => d ≠ 30 ∧ n ≠ 30
  | .rev32x d n => d ≠ 30 ∧ n ≠ 30
  | .cmpr n m => n ≠ 30 ∧ m ≠ 30
  | .cmpi n _ => n ≠ 30
  | .bcc _ _ => True
  | .b _ => True
  | .bTail _ => True
  | .ret => True
  | .ldr _ t n i => t ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .str _ t n i => t ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .ldp _ t1 t2 n i => t1 ≠ 30 ∧ t2 ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .stp _ t1 t2 n i => t1 ≠ 30 ∧ t2 ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .ld1 t _ n i => t ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .st1 t _ n i => t ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .ld4s t _ n i => t ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .st4s t _ n i => t ≠ 30 ∧ n ≠ 30 ∧ IdxOk i
  | .vop _ _ _ _ => True
  | .movi _ _ => True
  | .shl _ _ _ _ => True
  | .ushr _ _ _ _ => True
  | .ext _ _ _ _ => True
  | .zip1 _ _ _ => True
  | .zip2 _ _ _ => True
  | .uzp1 _ _ _ => True
  | .xtn _ _ => True
  | .rev32 _ _ => True
  | .sha256h _ _ _ => True
  | .sha256h2 _ _ _ => True
  | .sha256su0 _ _ => True
  | .sha256su1 _ _ _ => True

/-- `IdxOk` is decidable by computation. -/
instance decidableIdxOk : DecidablePred IdxOk := fun i => by
  cases i <;> dsimp only [IdxOk] <;> infer_instance

/-- `NoTouch` is decidable by computation (it is a conjunction of `≠` tests). -/
instance decidablePredNoTouch : DecidablePred NoTouch := fun i => by
  cases i <;> dsimp only [NoTouch] <;> infer_instance

section
variable (k : Int)

/-! ## `retOff` and the state accessors -/

@[simp] theorem retOff_gpr (s : CS) : (retOff k s).gpr = s.gpr.set 30 (.ptr ⟨rRet, k⟩) := rfl
@[simp] theorem retOff_vr (s : CS) : (retOff k s).vr = s.vr := rfl
@[simp] theorem retOff_flags (s : CS) : (retOff k s).flags = s.flags := rfl
@[simp] theorem retOff_mem (s : CS) : (retOff k s).mem = s.mem := rfl
@[simp] theorem retOff_pc (s : CS) : (retOff k s).pc = s.pc := rfl
@[simp] theorem retOff_halted (s : CS) : (retOff k s).halted = s.halted := rfl
@[simp] theorem retOff_tail (s : CS) : (retOff k s).tail = s.tail := rfl
@[simp] theorem retOff_err (s : CS) : (retOff k s).err = s.err := rfl
@[simp] theorem retOff_assume (s : CS) : (retOff k s).assume = s.assume := rfl

@[simp] theorem retOff_getG (s : CS) (i : Nat) (h : i ≠ 30) :
    (retOff k s).getG i = s.getG i := by
  simp only [retOff, State.setG, State.getG, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm h)]

@[simp] theorem retOff_getV (s : CS) (i : Nat) : (retOff k s).getV i = s.getV i := rfl
@[simp] theorem retOff_getQ (s : CS) (i : Nat) : getQ (retOff k s) i = getQ s i := rfl
@[simp] theorem retOff_getD (s : CS) (i : Nat) : getD (retOff k s) i = getD s i := rfl

theorem retOff_retOff (k' : Int) (s : CS) : retOff k' (retOff k s) = retOff k' s := by
  unfold retOff State.setG
  rw [List.set_set]

theorem getG_setG_ne (s : CS) (i j : Nat) (v : Val W32 Int) (h : i ≠ j) :
    (s.setG i v).getG j = s.getG j := by
  simp only [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getG_retOff_self (s : CS) (h : 30 < s.gpr.length) :
    (retOff k s).getG 30 = .ptr ⟨rRet, k⟩ := by
  simp only [retOff, State.setG, State.getG, List.getD_eq_getElem?_getD,
    List.getElem?_set_self h, Option.getD_some]

/-- The offset of `x30` is a pointer, so the register list is long enough to hold index 30:
the fact that lets us read the relabeled `x30` without a separate length invariant. -/
theorem getG_ptr_lt_length {s : CS} {o : Int} (hs30 : s.getG 30 = .ptr ⟨rRet, o⟩) :
    30 < s.gpr.length := by
  by_cases hle : s.gpr.length ≤ 30
  · have hnone : s.gpr[30]? = none := List.getElem?_eq_none hle
    have hnum : s.getG 30 = .num (Lane.const 0) (Lane.const 0) := by
      simp only [State.getG, List.getD_eq_getElem?_getD, hnone]
      rfl
    rw [hs30] at hnum
    nomatch hnum
  · exact Nat.lt_of_not_le hle

/-- Read the relabeled `x30` when the old value is a pointer to `rRet`. -/
theorem getG_retOff_self' (s : CS) {o : Int} (hs30 : s.getG 30 = .ptr ⟨rRet, o⟩) :
    (retOff k s).getG 30 = .ptr ⟨rRet, k⟩ :=
  getG_retOff_self k s (getG_ptr_lt_length hs30)

theorem retOff_setG (s : CS) (i : Nat) (v : Val W32 Int) (h : i ≠ 30) :
    retOff k (s.setG i v) = (retOff k s).setG i v := by
  unfold retOff State.setG
  rw [List.set_comm v (.ptr ⟨rRet, k⟩) h]

theorem setG_retOff (s : CS) (i : Nat) (v : Val W32 Int) (h : i ≠ 30) :
    (retOff k s).setG i v = retOff k (s.setG i v) :=
  (retOff_setG k s i v h).symm

@[simp] theorem retOff_setV (s : CS) (d : Nat) (v : List W32) :
    retOff k (s.setV d v) = (retOff k s).setV d v := rfl

@[simp] theorem retOff_setW (s : CS) (d : Nat) (x : W32) (h : d ≠ 30) :
    retOff k (setW s d x) = setW (retOff k s) d x := by
  simp only [setW]
  exact retOff_setG k s d _ h

@[simp] theorem retOff_setQ (s : CS) (d : Nat) (v : List W32) :
    retOff k (setQ s d v) = setQ (retOff k s) d v := rfl

@[simp] theorem retOff_setD (s : CS) (d : Nat) (v : List W32) :
    retOff k (setD s d v) = setD (retOff k s) d v := rfl

@[simp] theorem retOff_next (s : CS) : retOff k s.next = (retOff k s).next := rfl

@[simp] theorem retOff_halt (s : CS) : retOff k (halt s) = halt (retOff k s) := rfl

@[simp] theorem retOff_setFlags (s : CS) (a b : Int) :
    retOff k (setFlags s a b) = setFlags (retOff k s) a b := rfl

@[simp] theorem retOff_storeLane (s : CS) (a : Addr Int) (x : W32) :
    retOff k (storeLane s a x) = storeLane (retOff k s) a x := rfl

@[simp] theorem retOff_storeLanes (s : CS) (a : Addr Int) (xs : List W32) :
    retOff k (storeLanes s a xs) = storeLanes (retOff k s) a xs := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih =>
    simp only [storeLanes]
    rw [ih, retOff_storeLane k]

@[simp] theorem retOff_storeVal (s : CS) (a : Addr Int) (v : Val W32 Int) :
    retOff k (storeVal s a v) = storeVal (retOff k s) a v := by
  cases v with
  | num lo hi => simp [storeVal, retOff_storeLane]
  | ptr p => simp [storeVal, retOff, State.setG]

@[simp] theorem retOff_fail (s : CS) (msg : String) :
    retOff k (s.fail msg) = (retOff k s).fail msg := by
  unfold State.fail
  by_cases h : s.err.isSome <;> simp [h, retOff, State.setG]

@[simp] theorem retOff_branch (s : CS) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    retOff k (s.branch orc c t) = (retOff k s).branch orc c t := by
  unfold State.branch
  cases hc : c.decideC with
  | none =>
    by_cases ho : orc s.pc
    · simp [hc, ho, retOff, State.setG]
    · simp [hc, ho, retOff, State.setG, State.next]
  | some b =>
    by_cases hb : b
    · simp [hc, hb, retOff, State.setG]
    · simp [hc, hb, retOff, State.setG, State.next]

theorem retOff_writeBack (s : CS) (n : Nat) (a : Option (Addr Int)) (h : n ≠ 30) :
    retOff k (writeBack s n a) = writeBack (retOff k s) n a := by
  cases a with
  | none => rfl
  | some a => simp only [writeBack]; exact retOff_setG k s n (.ptr a) h

/-! ## Helper reads and writes are blind to `x30` when they do not name it -/

@[simp] theorem readCell_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) :
    readCell mem0 (retOff k s) a = readCell mem0 s a := rfl

@[simp] theorem loadLane_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) :
    loadLane mem0 (retOff k s) a = loadLane mem0 s a := rfl

@[simp] theorem loadLanes_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) (n : Nat) :
    loadLanes mem0 (retOff k s) a n = loadLanes mem0 s a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [loadLanes, ih]

theorem pbRest_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (p a : Addr Int) :
    ∀ (n b : Nat), pbRest mem0 (retOff k s) p a n b = pbRest mem0 s p a n b
  | 0, _ => rfl
  | n + 1, b => by
    simp only [pbRest, readCell_retOff, pbRest_retOff mem0 s p a n]

@[simp] theorem loadVal_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) :
    loadVal mem0 (retOff k s) a = loadVal mem0 s a := by
  simp only [loadVal, readCell_retOff, loadLane_retOff, pbRest_retOff]

theorem getC_retOff (s : CS) (i : Nat) (h : i ≠ 30) :
    getC (retOff k s) i = getC s i := by
  simp only [getC, retOff_getG k s i h]

theorem getW_retOff (s : CS) (i : Nat) (h : i ≠ 30) :
    getW (retOff k s) i = getW s i := by
  simp only [getW, retOff_getG k s i h]

theorem getX_retOff (s : CS) (i : Nat) (h : i ≠ 30) :
    getX (retOff k s) i = getX s i := by
  simp only [getX, retOff_getG k s i h]

theorem baseAddr_retOff (s : CS) (n : Nat) (h : n ≠ 30) :
    baseAddr (retOff k s) n = baseAddr s n := by
  simp only [baseAddr, retOff_getG k s n h]

theorem addrWB_retOff (s : CS) (n : Nat) (i : Idx) (hn : n ≠ 30) (hi : IdxOk i) :
    addrWB (retOff k s) n i = addrWB s n i := by
  cases i with
  | off j =>
    simp only [addrWB]
    rw [baseAddr_retOff k s n hn]
  | pre j =>
    simp only [addrWB]
    rw [baseAddr_retOff k s n hn]
  | post j =>
    simp only [addrWB]
    rw [baseAddr_retOff k s n hn]
  | postR m =>
    simp only [IdxOk] at hi
    simp only [addrWB]
    rw [baseAddr_retOff k s n hn]
    cases hb : baseAddr s n with
    | error e => rfl
    | ok b =>
      simp only [hb]
      by_cases hm : m = sp
      · simp only [hm, if_true]
      · simp only [hm, if_false]
        rw [getC_retOff k s m hi]

/-! ## Except algebra -/

theorem except_bind_pure' {β δ : Type} (h : β → δ) (x : Except String β) :
    (x >>= fun a => pure (h a)) = h <$> x := by
  cases x <;> rfl

theorem map_comp_retOff {β : Type} (f : β → CS) (x : Except String β) :
    (f <$> x).map (retOff k) = (fun y => retOff k (f y)) <$> x := by
  cases x <;> rfl

theorem okOr_retOff (s : CS) (r : Except String CS) :
    retOff k (okOr s r) = okOr (retOff k s) (r.map (retOff k)) := by
  cases r with
  | ok s' => rfl
  | error e =>
    show retOff k (s.fail e) = (retOff k s).fail e
    rw [retOff_fail]

theorem writeBack_retOff_out (s : CS) (n : Nat) (h : n ≠ 30) (a : Option (Addr Int)) :
    writeBack (retOff k s) n a = retOff k (writeBack s n a) :=
  (retOff_writeBack k s n a h).symm

/-! ## The state-building steps commute -/

theorem loadReg_retOff (mem0 : Addr Int → Cell W32 Int) (s0 s : CS) (sz : Sz) (t : Nat)
    (a : Addr Int) (h : t ≠ 30) :
    loadReg mem0 (retOff k s0) (retOff k s) sz t a
      = Except.map (retOff k) (loadReg mem0 s0 s sz t a) := by
  cases sz with
  | w =>
    simp only [loadReg]
    by_cases ht : t = sp
    · simp only [ht, ite_true]; rfl
    · simp only [ht, ite_false, except_bind_pure', map_comp_retOff, loadLane_retOff,
        retOff_setW k s t _ h]
  | x =>
    simp only [loadReg]
    by_cases ht : t = sp
    · simp only [ht, ite_true]; rfl
    · simp only [ht, ite_false, except_bind_pure', map_comp_retOff, loadVal_retOff,
        retOff_setG k s t _ h]
  | d =>
    simp only [loadReg, except_bind_pure', map_comp_retOff, loadLanes_retOff]
    rfl
  | q =>
    simp only [loadReg, except_bind_pure', map_comp_retOff, loadLanes_retOff]
    rfl

theorem storeReg_retOff (s0 s : CS) (sz : Sz) (t : Nat) (a : Addr Int) (h : t ≠ 30) :
    storeReg (retOff k s0) (retOff k s) sz t a
      = Except.map (retOff k) (storeReg s0 s sz t a) := by
  cases sz with
  | w =>
    simp only [storeReg, except_bind_pure', map_comp_retOff, retOff_storeLane,
      getW_retOff k s0 t h]
  | x =>
    simp only [storeReg]
    by_cases ht : t = sp
    · simp only [ht, ite_true]; rfl
    · simp only [ht, ite_false]
      rw [retOff_getG k s0 t h]
      rw [← retOff_storeVal k s a (s0.getG t)]
      rfl
  | d =>
    simp only [storeReg]
    rw [retOff_getD k s0 t]
    rw [← retOff_storeLanes k s a (getD s0 t)]
    rfl
  | q =>
    simp only [storeReg]
    rw [retOff_getQ k s0 t]
    rw [← retOff_storeLanes k s a (getQ s0 t)]
    rfl

@[simp] theorem ld1Step_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int)
    (t : Nat) (st : CS) (j : Nat) :
    ld1Step mem0 (retOff k s) a t (retOff k st) j
      = Except.map (retOff k) (ld1Step mem0 s a t st j) := by
  simp only [ld1Step, except_bind_pure', map_comp_retOff, loadLanes_retOff]
  rfl

@[simp] theorem ld4Step_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int)
    (t e : Nat) (st : CS) (r : Nat) :
    ld4Step mem0 (retOff k s) a t e (retOff k st) r
      = Except.map (retOff k) (ld4Step mem0 s a t e st r) := by
  simp only [ld4Step, except_bind_pure', map_comp_retOff, loadLane_retOff]
  rfl

@[simp] theorem st1Step_retOff (s : CS) (a : Addr Int) (t : Nat) (st : CS) (j : Nat) :
    st1Step (retOff k s) a t (retOff k st) j
      = retOff k (st1Step s a t st j) := rfl

@[simp] theorem st4Step_retOff (s : CS) (a : Addr Int) (t e : Nat) (st : CS) (r : Nat) :
    st4Step (retOff k s) a t e (retOff k st) r
      = retOff k (st4Step s a t e st r) := rfl

theorem foldlM_retOff (step : CS → CS → Nat → Except String CS)
    (hstep : ∀ s0 st j, step (retOff k s0) (retOff k st) j
      = Except.map (retOff k) (step s0 st j))
    (s0 init : CS) (l : List Nat) :
    l.foldlM (step (retOff k s0)) (retOff k init)
      = Except.map (retOff k) (l.foldlM (step s0) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldlM_cons]
    rw [hstep]
    rw [except_bind_map (retOff k) (step s0 init j)
      (fun b => l.foldlM (step (retOff k s0)) b)]
    simp only [ih]
    rw [← except_map_bind (retOff k) (step s0 init j)
      (fun a => l.foldlM (step s0) a)]

theorem foldl_retOff (step : CS → CS → Nat → CS)
    (hstep : ∀ s0 st j, step (retOff k s0) (retOff k st) j = retOff k (step s0 st j))
    (s0 init : CS) (l : List Nat) :
    l.foldl (step (retOff k s0)) (retOff k init) = retOff k (l.foldl (step s0) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih => simp [List.foldl, hstep, ih]

theorem foldlM_ld1_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (t : Nat)
    (a : Addr Int) (init : CS) (l : List Nat) :
    l.foldlM (ld1Step mem0 (retOff k s) a t) (retOff k init)
      = Except.map (retOff k) (l.foldlM (ld1Step mem0 s a t) init) :=
  foldlM_retOff k (fun s0 st j => ld1Step mem0 s0 a t st j)
    (fun s0 st j => ld1Step_retOff k mem0 s0 a t st j) s init l

theorem foldlM_ld4_retOff (mem0 : Addr Int → Cell W32 Int) (s : CS) (t e : Nat)
    (a : Addr Int) (init : CS) (l : List Nat) :
    l.foldlM (ld4Step mem0 (retOff k s) a t e) (retOff k init)
      = Except.map (retOff k) (l.foldlM (ld4Step mem0 s a t e) init) :=
  foldlM_retOff k (fun s0 st j => ld4Step mem0 s0 a t e st j)
    (fun s0 st j => ld4Step_retOff k mem0 s0 a t e st j) s init l

theorem foldl_st1_retOff (s : CS) (t : Nat) (a : Addr Int) (init : CS) (l : List Nat) :
    l.foldl (st1Step (retOff k s) a t) (retOff k init)
      = retOff k (l.foldl (st1Step s a t) init) :=
  foldl_retOff k (fun s0 st j => st1Step s0 a t st j)
    (fun s0 st j => st1Step_retOff k s0 a t st j) s init l

theorem foldl_st4_retOff (s : CS) (t e : Nat) (a : Addr Int) (init : CS) (l : List Nat) :
    l.foldl (st4Step (retOff k s) a t e) (retOff k init)
      = retOff k (l.foldl (st4Step s a t e) init) :=
  foldl_retOff k (fun s0 st j => st4Step s0 a t e st j)
    (fun s0 st j => st4Step_retOff k s0 a t e st j) s init l

theorem getG_next (s : CS) : s.next.getG 30 = s.getG 30 := rfl
theorem getG_fail (s : CS) (e : String) : (s.fail e).getG 30 = s.getG 30 := by
  simp only [State.fail]; split <;> rfl
theorem getG_halt (s : CS) : (halt s).getG 30 = s.getG 30 := rfl
theorem getG_branch (s : CS) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    (s.branch orc c t).getG 30 = s.getG 30 := by
  unfold State.branch
  cases hd : c.decideC with
  | none =>
    simp only [Option.isNone_none, ite_true]
    split <;> first | rfl | exact getG_next _
  | some b =>
    simp only [Option.isNone_some, ite_false]
    split <;> first | rfl | exact getG_next _
theorem getG_setQ (s : CS) (d : Nat) (v : List W32) : (setQ s d v).getG 30 = s.getG 30 := rfl
theorem getG_setD (s : CS) (d : Nat) (v : List W32) : (setD s d v).getG 30 = s.getG 30 := rfl
theorem getG_setFlags (s : CS) (a b : Int) : (setFlags s a b).getG 30 = s.getG 30 := rfl
theorem getG_storeLane (s : CS) (a : Addr Int) (x : W32) : (storeLane s a x).getG 30 = s.getG 30 := rfl
theorem getG_storeVal (s : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal s a v).getG 30 = s.getG 30 := by
  cases v <;> rfl
theorem getG_writeBack (s : CS) (n : Nat) (a : Option (Addr Int)) (h : n ≠ 30) :
    (writeBack s n a).getG 30 = s.getG 30 := by
  cases a with
  | none => rfl
  | some a' => simp only [writeBack, getG_setG_ne s n 30 (.ptr a') h]

/-- The body's successful state keeps `x30`. -/
def Ok30 (s : CS) (E : Except String CS) : Prop := ∀ s', E = .ok s' → s'.getG 30 = s.getG 30

theorem ok30_error (s : CS) (e : String) : Ok30 s (.error e) := by
  intro s' h; nomatch h

theorem ok30_ok (s t : CS) (h : t.getG 30 = s.getG 30) : Ok30 s (.ok t) := by
  intro s' he; cases he; exact h

theorem ok30_ite (s : CS) (c : Prop) [Decidable c] (a b : Except String CS) :
    Ok30 s (if c then a else b) ↔ (c → Ok30 s a) ∧ (¬ c → Ok30 s b) := by
  by_cases h : c <;> simp [h, Ok30]

theorem ok30_bind {β : Type} (s : CS) (x : Except String β) (k : β → Except String CS)
    (h : ∀ a, x = .ok a → Ok30 s (k a)) : Ok30 s (x >>= k) := by
  intro s' he
  cases hx : x with
  | ok a =>
    rw [hx] at he
    exact h a hx s' (show k a = .ok s' from he)
  | error e =>
    rw [hx] at he
    exact ok30_error s e s' (show Except.error e = .ok s' from he)

theorem okOr_getG30 (s : CS) (E : Except String CS) (h : Ok30 s E) :
    (okOr s E).getG 30 = s.getG 30 := by
  cases E with
  | ok s' => exact h s' rfl
  | error e => simp only [okOr_error, getG_fail]

theorem ok30_next (s : CS) : Ok30 s (.ok s.next) := ok30_ok s _ (getG_next s)

theorem ok30_setG (s : CS) (d : Nat) (v : Val W32 Int) (h : d ≠ 30) :
    Ok30 s (.ok (s.setG d v)) := ok30_ok s _ (getG_setG_ne s d 30 v h)
theorem ok30_setG_next (s : CS) (d : Nat) (v : Val W32 Int) (h : d ≠ 30) :
    Ok30 s (.ok (s.setG d v).next) := ok30_ok s _ (by rw [getG_next]; exact getG_setG_ne s d 30 v h)

theorem ok30_setW (s : CS) (d : Nat) (x : W32) (h : d ≠ 30) :
    Ok30 s (.ok (setW s d x)) :=
  ok30_ok s _ (by rw [setW]; exact getG_setG_ne s d 30 (.num x (Lane.const 0)) h)
theorem ok30_setW_next (s : CS) (d : Nat) (x : W32) (h : d ≠ 30) :
    Ok30 s (.ok (setW s d x).next) :=
  ok30_ok s _ (by rw [getG_next, setW]; exact getG_setG_ne s d 30 (.num x (Lane.const 0)) h)

theorem ok30_setQ (s : CS) (d : Nat) (v : List W32) : Ok30 s (.ok (setQ s d v)) :=
  ok30_ok s _ (getG_setQ s d v)
theorem ok30_setQ_next (s : CS) (d : Nat) (v : List W32) : Ok30 s (.ok (setQ s d v).next) :=
  ok30_ok s _ (by rw [getG_next]; exact getG_setQ s d v)
theorem ok30_setD (s : CS) (d : Nat) (v : List W32) : Ok30 s (.ok (setD s d v)) :=
  ok30_ok s _ (getG_setD s d v)
theorem ok30_setD_next (s : CS) (d : Nat) (v : List W32) : Ok30 s (.ok (setD s d v).next) :=
  ok30_ok s _ (by rw [getG_next]; exact getG_setD s d v)

theorem ok30_setFlags_next (s : CS) (a b : Int) : Ok30 s (.ok (setFlags s a b).next) :=
  ok30_ok s _ (by rw [getG_next]; exact getG_setFlags s a b)

theorem ok30_halt (s : CS) : Ok30 s (.ok (halt s)) := ok30_ok s _ (getG_halt s)

theorem ok30_branch (s : CS) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    Ok30 s (.ok (s.branch orc c t)) := ok30_ok s _ (getG_branch s orc c t)

theorem ok30_writeBack (s : CS) (n : Nat) (a : Option (Addr Int)) (h : n ≠ 30) :
    Ok30 s (.ok (writeBack s n a)) := ok30_ok s _ (getG_writeBack s n a h)

theorem ok30_storeLane (s : CS) (a : Addr Int) (x : W32) : Ok30 s (.ok (storeLane s a x)) :=
  ok30_ok s _ (getG_storeLane s a x)

theorem ok30_storeVal (s : CS) (a : Addr Int) (v : Val W32 Int) : Ok30 s (.ok (storeVal s a v)) :=
  ok30_ok s _ (getG_storeVal s a v)

theorem storeLanes_getG30 (l : List W32) (a : Addr Int) (s : CS) :
    (storeLanes s a l).getG 30 = s.getG 30 := by
  induction l generalizing a s with
  | nil => rfl
  | cons x xs ih => exact Eq.trans (ih (a.plusI 4) (storeLane s a x)) (getG_storeLane s a x)

theorem ok30_storeLanes (s : CS) (a : Addr Int) (l : List W32) : Ok30 s (.ok (storeLanes s a l)) :=
  ok30_ok s _ (storeLanes_getG30 l a s)

theorem ok30_loadReg (mem0 : Addr Int → Cell W32 Int) (s0 s : CS) (sz : Sz) (t : Nat)
    (a : Addr Int) (h : t ≠ 30) : Ok30 s (loadReg mem0 s0 s sz t a) := by
  cases sz with
  | w =>
    simp only [loadReg]
    by_cases hsp : t = sp
    · simp only [hsp, ite_true]; exact ok30_error s _
    · simp only [hsp, ite_false]
      exact ok30_bind s _ _ (fun x _ => ok30_setW s t x h)
  | x =>
    simp only [loadReg]
    by_cases hsp : t = sp
    · simp only [hsp, ite_true]; exact ok30_error s _
    · simp only [hsp, ite_false]
      exact ok30_bind s _ _ (fun v _ => ok30_setG s t v h)
  | d =>
    simp only [loadReg]
    exact ok30_bind s _ _ (fun v _ => ok30_setD s t v)
  | q =>
    simp only [loadReg]
    exact ok30_bind s _ _ (fun v _ => ok30_setQ s t v)

theorem ok30_storeReg (s0 s : CS) (sz : Sz) (t : Nat) (a : Addr Int) (h : t ≠ 30) :
    Ok30 s (storeReg s0 s sz t a) := by
  cases sz with
  | w => simp only [storeReg]; exact ok30_bind s _ _ (fun x _ => ok30_storeLane s a x)
  | x =>
    simp only [storeReg]
    by_cases hsp : t = sp
    · simp only [hsp, ite_true]; exact ok30_error s _
    · simp only [hsp, ite_false]; exact ok30_storeVal s a (s0.getG t)
  | d => simp only [storeReg]; exact ok30_storeLanes s a _
  | q => simp only [storeReg]; exact ok30_storeLanes s a _

theorem ok30_ld1Step (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) (t : Nat)
    (st : CS) (j : Nat) : Ok30 st (ld1Step mem0 s a t st j) := by
  simp only [ld1Step]
  exact ok30_bind st _ _ (fun v _ => ok30_setQ st ((t + j) % 32) v)

theorem ok30_ld4Step (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) (t e : Nat)
    (st : CS) (r : Nat) : Ok30 st (ld4Step mem0 s a t e st r) := by
  simp only [ld4Step]
  exact ok30_bind st _ _ (fun x _ => ok30_setQ st ((t + r) % 32) _)

theorem ok30_foldlM_ld1 (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) (t : Nat) :
    ∀ (l : List Nat) (init : CS), Ok30 init (l.foldlM (ld1Step mem0 s a t) init) := by
  intro l
  induction l with
  | nil => intro init; exact ok30_ok init _ rfl
  | cons j js ih =>
    intro init
    simp only [List.foldlM_cons]
    refine ok30_bind init _ _ (fun st' hst' => ?_)
    have h1 := ok30_ld1Step mem0 s a t init j
    exact fun s' he => Eq.trans (ih st' s' he) (h1 st' hst')

theorem ok30_foldlM_ld4 (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) (t e : Nat) :
    ∀ (l : List Nat) (init : CS), Ok30 init (l.foldlM (ld4Step mem0 s a t e) init) := by
  intro l
  induction l with
  | nil => intro init; exact ok30_ok init _ rfl
  | cons j js ih =>
    intro init
    simp only [List.foldlM_cons]
    refine ok30_bind init _ _ (fun st' hst' => ?_)
    have h1 := ok30_ld4Step mem0 s a t e init j
    exact fun s' he => Eq.trans (ih st' s' he) (h1 st' hst')

theorem foldl_st1_getG30 (s : CS) (a : Addr Int) (t : Nat) :
    ∀ (l : List Nat) (init : CS), (l.foldl (st1Step s a t) init).getG 30 = init.getG 30 := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons j js ih =>
    intro init
    simp only [List.foldl_cons]
    exact Eq.trans (ih (st1Step s a t init j)) rfl

theorem foldl_st4_getG30 (s : CS) (a : Addr Int) (t e : Nat) :
    ∀ (l : List Nat) (init : CS), (l.foldl (st4Step s a t e) init).getG 30 = init.getG 30 := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons j js ih =>
    intro init
    simp only [List.foldl_cons]
    exact Eq.trans (ih (st4Step s a t e init j)) rfl



variable (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : CS)


theorem ok30_weaken (E : Except String CS) (s t : CS) (h : t.getG 30 = s.getG 30) (hE : Ok30 t E) :
    Ok30 s E := fun s' he => Eq.trans (hE s' he) h

theorem getG_loadReg (mem0 : Addr Int → Cell W32 Int) (s0 s : CS) (sz : Sz) (t : Nat)
    (a : Addr Int) (h : t ≠ 30) {s' : CS} (hs : loadReg mem0 s0 s sz t a = .ok s') :
    s'.getG 30 = s.getG 30 := ok30_loadReg mem0 s0 s sz t a h s' hs

theorem getG_storeReg (s0 s : CS) (sz : Sz) (t : Nat) (a : Addr Int) (h : t ≠ 30)
    {s' : CS} (hs : storeReg s0 s sz t a = .ok s') : s'.getG 30 = s.getG 30 :=
  ok30_storeReg s0 s sz t a h s' hs

theorem exec_getG30 (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : CS) (hi : NoTouch i) :
    (exec ro mem0 orc i s).getG 30 = s.getG 30 := by
  by_cases hs : s.halted = true
  · simp only [exec, hs, ite_true]
  cases i with
  | nop =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    exact getG_next s
  | movz d imm =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    exact ⟨fun _ => ok30_error s _, fun _ => ok30_setG_next s d _ hi⟩
  | addi d n imm =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    exact okOr_getG30 s _ (ok30_bind s _ _ (fun a _ => ok30_setG_next s d _ hi.1))
  | subi d n imm =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    exact okOr_getG30 s _ (ok30_bind s _ _ (fun a _ => ok30_setG_next s d _ hi.1))
  | addr d n m sh =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun a _ => ?_)
    refine ok30_bind s _ _ (fun b _ => ?_)
    rw [ok30_ite]
    refine ⟨fun _ => ok30_setG_next s d _ hi.1, fun _ => ?_⟩
    rw [ok30_ite]
    exact ⟨fun _ => ok30_setG_next s d _ hi.1, fun _ => ok30_error s _⟩
  | adrp d off =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    exact ⟨fun _ => ok30_error s _, fun _ => ok30_setG_next s d _ hi⟩
  | addLo12 d n off =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    exact okOr_getG30 s _ (ok30_bind s _ _ (fun a _ => ok30_setG_next s d _ hi.1))
  | wop op d n m =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun a _ => ?_)
    exact ok30_bind s _ _ (fun b _ => ok30_setW_next s d _ hi.1)
  | rorw d n k =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    exact ok30_bind s _ _ (fun a _ => ok30_setW_next s d _ hi.1)
  | rev32x d n =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    exact ok30_bind s _ _ (fun a _ => ok30_setG_next s d _ hi.1)
  | cmpr n m =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun a _ => ?_)
    refine ok30_bind s _ _ (fun b _ => ?_)
    rw [ok30_ite]
    exact ⟨fun _ => ok30_setFlags_next s _ _, fun _ => ok30_error s _⟩
  | cmpi n imm =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    refine ok30_bind s _ _ (fun a _ => ?_)
    rw [ok30_ite]
    exact ⟨fun _ => ok30_setFlags_next s _ _, fun _ => ok30_error s _⟩
  | bcc c t =>
    simp only [NoTouch] at hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    cases hf : s.flags with
    | none => exact okOr_getG30 s _ (ok30_error s _)
    | some p =>
      obtain ⟨a, b⟩ := p
      exact okOr_getG30 s _ (ok30_branch s orc (ccCond c a b) t)
  | b t =>
    simp only [exec, hs, ite_true]
    rfl
  | bTail nm =>
    simp only [exec, hs, ite_true]
    rfl
  | ret =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    split
    · exact ok30_halt s
    · exact ok30_error s _
  | ldr sz t n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun aw _ => ?_)
    refine ok30_weaken _ _ _ (getG_writeBack s n aw.2 hn)
      (ok30_bind (writeBack s n aw.2) _ _ (fun s' hs' =>
        ok30_ok _ _ (by rw [getG_next]; exact Eq.trans (getG_loadReg mem0 s (writeBack s n aw.2) sz t aw.1 ht hs') rfl)))
  | str sz t n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun aw _ => ?_)
    refine ok30_weaken _ _ _ (getG_writeBack s n aw.2 hn)
      (ok30_bind (writeBack s n aw.2) _ _ (fun s' hs' =>
        ok30_ok _ _ (by rw [getG_next]; exact Eq.trans (getG_storeReg s (writeBack s n aw.2) sz t aw.1 ht hs') rfl)))
  | ldp sz t1 t2 n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht1, ht2, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun aw _ => ?_)
    have hwb : (writeBack s n aw.2).getG 30 = s.getG 30 := getG_writeBack s n aw.2 hn
    refine ok30_weaken _ _ _ hwb (ok30_bind (writeBack s n aw.2) _ _ (fun s1 hs1 => ?_))
    refine ok30_bind (writeBack s n aw.2) _ _ (fun s2 hs2 => ?_)
    refine ok30_ok (writeBack s n aw.2) _ ?_
    rw [getG_next]
    exact Eq.trans (getG_loadReg mem0 s s1 sz t2 (aw.1.plusI sz.bytes) ht2 hs2)
      (getG_loadReg mem0 s (writeBack s n aw.2) sz t1 aw.1 ht1 hs1)
  | stp sz t1 t2 n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht1, ht2, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun aw _ => ?_)
    have hwb : (writeBack s n aw.2).getG 30 = s.getG 30 := getG_writeBack s n aw.2 hn
    refine ok30_weaken _ _ _ hwb (ok30_bind (writeBack s n aw.2) _ _ (fun s1 hs1 => ?_))
    refine ok30_bind (writeBack s n aw.2) _ _ (fun s2 hs2 => ?_)
    refine ok30_ok (writeBack s n aw.2) _ ?_
    rw [getG_next]
    exact Eq.trans (getG_storeReg s s1 sz t2 (aw.1.plusI sz.bytes) ht2 hs2)
      (getG_storeReg s (writeBack s n aw.2) sz t1 aw.1 ht1 hs1)
  | ld1 t k n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    refine ok30_bind s _ _ (fun aw _ => ?_)
    refine ok30_weaken _ _ _ (getG_writeBack s n aw.2 hn)
      (ok30_bind (writeBack s n aw.2) _ _ (fun s' hs' =>
        ok30_ok _ _ (by rw [getG_next]; exact ok30_foldlM_ld1 mem0 s aw.1 t (List.range k) (writeBack s n aw.2) s' hs')))
  | st1 t k n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    refine ok30_bind s _ _ (fun aw _ => ?_)
    refine ok30_ok s _ ?_
    rw [getG_next]
    exact Eq.trans (foldl_st1_getG30 s aw.1 t (List.range k) (writeBack s n aw.2)) (getG_writeBack s n aw.2 hn)
  | ld4s t e n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun aw _ => ?_)
    refine ok30_weaken _ _ _ (getG_writeBack s n aw.2 hn)
      (ok30_bind (writeBack s n aw.2) _ _ (fun s' hs' =>
        ok30_ok _ _ (by rw [getG_next]; exact ok30_foldlM_ld4 mem0 s aw.1 t e (List.range 4) (writeBack s n aw.2) s' hs')))
  | st4s t e n idx =>
    simp only [NoTouch] at hi
    obtain ⟨ht, hn, hidx⟩ := hi
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    refine ⟨fun _ => ok30_error s _, fun _ => ?_⟩
    refine ok30_bind s _ _ (fun aw _ => ?_)
    refine ok30_ok s _ ?_
    rw [getG_next]
    exact Eq.trans (foldl_st4_getG30 s aw.1 t e (List.range 4) (writeBack s n aw.2)) (getG_writeBack s n aw.2 hn)
  | vop op d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | movi d imm =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | shl esz d n k =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    split
    · exact ok30_setQ_next s d _
    · split
      · exact ok30_setQ_next s d _
      · exact ok30_error s _
  | ushr esz d n k =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    split
    · exact ok30_setQ_next s d _
    · split
      · exact ok30_setQ_next s d _
      · exact ok30_error s _
  | ext d n m imm =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    refine okOr_getG30 s _ ?_
    rw [ok30_ite]
    exact ⟨fun _ => ok30_error s _, fun _ => ok30_setQ_next s d _⟩
  | zip1 d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | zip2 d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | uzp1 d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | xtn d n =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setD s d _
  | rev32 d n =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | sha256h d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | sha256h2 d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | sha256su0 d n =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _
  | sha256su1 d n m =>
    simp only [exec, hs, Bool.false_eq_true, ite_false]
    rw [getG_next]
    exact getG_setQ s d _

/-! ## One instruction -/

theorem exec_retOff (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : CS) (o : Int) (hi : NoTouch i)
    (hs30 : s.getG 30 = .ptr ⟨rRet, o⟩) :
    exec ro mem0 orc i (retOff k s) = retOff k (exec ro mem0 orc i s) ∧
    (exec ro mem0 orc i s).getG 30 = s.getG 30 := by
  constructor
  · by_cases hs : s.halted = true
    · simp only [exec, hs, retOff_halted, ite_true]
    cases i with
    | nop =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, retOff_next]
    | movz d imm =>
      simp only [NoTouch] at hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_ite, except_map_error, except_map_ok, pure_ok, throw_error,
        retOff_next, retOff_setG k s d _ hi]
    | addi d n imm =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getC_retOff k s n hn, retOff_next, retOff_setG k s d _ hd]
    | subi d n imm =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getC_retOff k s n hn, retOff_next, retOff_setG k s d _ hd]
    | addr d n m sh =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn, hm⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getC_retOff k s n hn, getC_retOff k s m hm,
        retOff_next, retOff_setG k s d _ hd]
    | adrp d off =>
      simp only [NoTouch] at hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_ite, except_map_error, except_map_ok, pure_ok, throw_error,
        retOff_next, retOff_setG k s d _ hi]
    | addLo12 d n off =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getC_retOff k s n hn, retOff_next, retOff_setG k s d _ hd]
    | wop op d n m =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn, hm⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getW_retOff k s n hn, getW_retOff k s m hm,
        retOff_next, retOff_setW k s d _ hd]
    | rorw d n kk =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getW_retOff k s n hn, retOff_next, retOff_setW k s d _ hd]
    | rev32x d n =>
      simp only [NoTouch] at hi
      obtain ⟨hd, hn⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getX_retOff k s n hn, retOff_next, retOff_setG k s d _ hd]
    | cmpr n m =>
      simp only [NoTouch] at hi
      obtain ⟨hn, hm⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getC_retOff k s n hn, getC_retOff k s m hm,
        retOff_next, retOff_setFlags]
    | cmpi n imm =>
      simp only [NoTouch] at hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, getC_retOff k s n hi, retOff_next, retOff_setFlags]
    | bcc c t =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        retOff_flags]
      cases hf : s.flags with
      | none => rfl
      | some p =>
        obtain ⟨a, b⟩ := p
        simp only [except_map_ok, pure_ok, retOff_branch]
    | b t =>
      simp only [exec, hs, retOff_halted, ite_true]
      simp [retOff, State.setG]
    | bTail name =>
      simp only [exec, hs, retOff_halted, ite_true]
      simp [retOff, State.setG]
    | ret =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_ite, except_map_error, except_map_ok, pure_ok, throw_error,
        getG_retOff_self' k s hs30, hs30, retOff_halt, rRet]
    | ldr sz t n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, loadReg_retOff k mem0 s _ sz t _ ht, retOff_next]
    | str sz t n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, storeReg_retOff k s _ sz t _ ht, retOff_next]
    | ldp sz t1 t2 n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht1, ht2, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, loadReg_retOff k mem0 s _ sz t1 _ ht1,
        loadReg_retOff k mem0 s _ sz t2 _ ht2, retOff_next]
    | stp sz t1 t2 n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht1, ht2, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, storeReg_retOff k s _ sz t1 _ ht1,
        storeReg_retOff k s _ sz t2 _ ht2, retOff_next]
    | ld1 t kk n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, foldlM_ld1_retOff k mem0 s t, retOff_next]
    | st1 t kk n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, foldl_st1_retOff k s t, retOff_next]
    | ld4s t e n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, foldlM_ld4_retOff k mem0 s t e, retOff_next]
    | st4s t e n idx =>
      simp only [NoTouch] at hi
      obtain ⟨ht, hn, hidx⟩ := hi
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, addrWB_retOff k s n idx hn hidx,
        writeBack_retOff_out k s n hn, foldl_st4_retOff k s t e, retOff_next]
    | vop op d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | movi d imm =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ]
    | shl esz d n kk =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false]
      rw [okOr_retOff k]
      congr 1
      split <;> simp only [pure_ok, throw_error, except_map_ok, except_map_error,
        retOff_getQ, retOff_setQ, retOff_next]
      split <;> simp only [pure_ok, throw_error, except_map_ok, except_map_error,
        retOff_getQ, retOff_setQ, retOff_next]
    | ushr esz d n kk =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false]
      rw [okOr_retOff k]
      congr 1
      split <;> simp only [pure_ok, throw_error, except_map_ok, except_map_error,
        retOff_getQ, retOff_setQ, retOff_next]
      split <;> simp only [pure_ok, throw_error, except_map_ok, except_map_error,
        retOff_getQ, retOff_setQ, retOff_next]
    | ext d n m imm =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false, okOr_retOff k,
        except_map_bind, except_bind_map, except_map_ite, except_map_error, except_map_ok,
        pure_ok, throw_error, retOff_next, retOff_setQ, retOff_getQ]
    | zip1 d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | zip2 d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | uzp1 d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | xtn d n =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setD, retOff_getQ]
    | rev32 d n =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | sha256h d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | sha256h2 d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | sha256su0 d n =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
    | sha256su1 d n m =>
      simp only [exec, hs, retOff_halted, Bool.false_eq_true, ite_false,
        retOff_next, retOff_setQ, retOff_getQ]
  · exact exec_getG30 ro mem0 orc i s hi


end

/-! ## Whole-program execution -/

theorem all_noTouch {prog : Array Instr} (h : prog.all (fun i => decide (NoTouch i)) = true)
    {pc : Nat} {i : Instr} (hp : prog[pc]? = some i) : NoTouch i := by
  obtain ⟨hpc, rfl⟩ := Array.getElem?_eq_some_iff.mp hp
  exact of_decide_eq_true ((Array.all_eq_true.mp h) pc hpc)

theorem run_retOff (prog : Array Instr) (ro : Region) (mem0 : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (hprog : prog.all (fun i => decide (NoTouch i)) = true) :
    ∀ (n : Nat) (s : CS) (k o : Int), s.getG 30 = .ptr ⟨rRet, o⟩ →
      run prog ro mem0 orc n (retOff k s) = retOff k (run prog ro mem0 orc n s) := by
  intro n
  induction n with
  | zero => intro s k o _; rfl
  | succ n ih =>
    intro s k o hs30
    by_cases hs : s.halted = true
    · simp [run, hs]
    · simp only [run, hs, retOff_halted, retOff_pc, Bool.false_eq_true, ite_false]
      cases hp : prog[s.pc]? with
      | none => dsimp only; simp only [retOff_fail]
      | some i =>
        dsimp only
        obtain ⟨heq, hinv⟩ := exec_retOff k ro mem0 orc i s o
          (all_noTouch hprog hp) hs30
        rw [heq]
        exact ih (exec ro mem0 orc i s) k o (hinv.trans hs30)

end Hashtree.Asm.ArmRet
