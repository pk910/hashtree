import Hashtree.Asm.ArmRun
import Hashtree.Asm.ArmRename

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# Stack-offset shift

The generated kernel trees are proved from a symbolic entry whose `SP` is the constant
`(rStack, 0)`: every stack access of the stream is at an absolute `(rStack, -32 .. 0)` address.
The shipped wrapper calls the same stream with an arbitrary `SP = (rStack, sp0)`.  This module
supplies the transport: a state transform that shifts every `rStack`-addressed pointer/cell by
`sp0` (`mapAddr`), together with the matching shift of the initial memory (`memSh`), and the
proof that a run commutes with it.

Two details:

* flags are not shifted: the model stores a comparison as the *pair of offsets* (the region is
  checked at `cmp` time and then dropped), so a shift would be ambiguous.  The relation
  `Rel` therefore only asks the compared *difference* to agree, which is all `b.cond` reads
  (and for the concrete `Int` model `Cond.decideC` is always decided, so `assume` never grows).
* the `SP` alignment check in `baseAddr` needs `sp0 % 16 = 0`; it is carried as `hk`.

The relation is over concrete states only; the generated tree enters through
`Proofs/ArmShaX1Exit`'s `entryS` instantiation.
-/

namespace Hashtree.Asm.ArmShift
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmRename

/-! ## The address shift -/

/-- Shift the offset of `rStack` addresses by `k`; every other address is unchanged. -/
def mapAddr (k : Int) (a : Addr Int) : Addr Int :=
  if a.region = rStack then ⟨rStack, a.off + k⟩ else a

@[simp] theorem mapAddr_region (k : Int) (a : Addr Int) : (mapAddr k a).region = a.region := by
  unfold mapAddr
  split <;> simp_all

theorem mapAddr_off (k : Int) (a : Addr Int) :
    (mapAddr k a).off = if a.region = rStack then a.off + k else a.off := by
  unfold mapAddr
  split <;> rfl

theorem mapAddr_of_ne (k : Int) (a : Addr Int) (h : a.region ≠ rStack) : mapAddr k a = a := by
  unfold mapAddr
  rw [if_neg h]

theorem mapAddr_num (k : Int) (o : Int) : mapAddr k ⟨rNum, o⟩ = ⟨rNum, o⟩ := by
  unfold mapAddr
  rw [if_neg (by decide : ¬ (rNum : Region) = rStack)]

theorem mapAddr_stack (k : Int) (o : Int) : mapAddr k ⟨rStack, o⟩ = ⟨rStack, o + k⟩ := by
  unfold mapAddr
  rfl

theorem mapAddr_add (k : Int) (a : Addr Int) (i : Int) :
    mapAddr k (a.plusI i) = (mapAddr k a).plusI i := by
  obtain ⟨r, o⟩ := a
  by_cases h : r = rStack
  · subst h
    show (⟨rStack, o + i + k⟩ : Addr Int) = ⟨rStack, o + k + i⟩
    congr 1
    omega
  · rw [mapAddr_of_ne k _ h]
    rw [mapAddr_of_ne k _ h]

theorem mapAddr_plus (k : Int) (a : Addr Int) (n : Int) :
    mapAddr k (a.plus n) = (mapAddr k a).plus n := by
  obtain ⟨r, o⟩ := a
  by_cases h : r = rStack
  · subst h
    change mapAddr k (⟨rStack, o + n⟩ : Addr Int) = (mapAddr k ⟨rStack, o⟩).plus n
    rw [mapAddr_stack, mapAddr_stack]
    change (⟨rStack, o + n + k⟩ : Addr Int) = ⟨rStack, o + k + n⟩
    congr 1
    omega
  · rw [mapAddr_of_ne k _ h, mapAddr_of_ne k ⟨r, o⟩ h]

theorem mapAddr_inv (k : Int) (a : Addr Int) : mapAddr (-k) (mapAddr k a) = a := by
  obtain ⟨r, o⟩ := a
  by_cases h : r = rStack
  · subst h
    show (⟨rStack, o + k + -k⟩ : Addr Int) = ⟨rStack, o⟩
    congr 1
    omega
  · rw [mapAddr_of_ne k _ h]
    rw [mapAddr_of_ne (-k) _ h]

theorem mapAddr_inj {k : Int} {a b : Addr Int} : mapAddr k a = mapAddr k b ↔ a = b := by
  constructor
  · intro h
    have hr : a.region = b.region := by
      rw [← mapAddr_region k a, ← mapAddr_region k b, h]
    have ho : (mapAddr k a).off = (mapAddr k b).off := by rw [h]
    rw [mapAddr_off, mapAddr_off, ← hr] at ho
    have hoff : a.off = b.off := by
      by_cases hs : a.region = rStack
      · simp only [hs, ite_true] at ho
        omega
      · simp only [hs, ite_false] at ho
        exact ho
    cases a
    cases b
    simp_all
  · intro h
    rw [h]

theorem same_int (a b : Addr Int) :
    AddrEq.same a b = some (a.region == b.region && a.off == b.off) := rfl

/-- Address comparison is invariant: the shift renames both sides consistently. -/
theorem same_sh (k : Int) (a b : Addr Int) :
    AddrEq.same (mapAddr k a) (mapAddr k b) = AddrEq.same a b := by
  rw [same_int, same_int, mapAddr_region, mapAddr_region, mapAddr_off, mapAddr_off]
  by_cases hr : a.region = b.region
  · rw [hr]
    by_cases hs : b.region = rStack
    · simp only [hs, ite_true, beq_self_eq_true, Bool.true_and]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      constructor <;> intro h <;> omega
    · simp only [hs, ite_false]
  · rw [beq_eq_false_iff_ne.mpr hr]
    rfl

/-- SP alignment survives a multiple of 16. -/
theorem align_add (k o : Int) (hk : k % 16 = 0) : (o + k) % 16 = o % 16 := by
  rw [Int.add_emod, hk, Int.add_zero, Int.emod_emod]

/-! ## The shift on values, cells, logs, states and the initial memory -/

/-- The shift on values: numbers and non-stack pointers are unchanged. -/
def shVal (k : Int) : Val W32 Int → Val W32 Int
  | .num lo hi => .num lo hi
  | .ptr a => .ptr (mapAddr k a)

/-- The shift on memory cells. -/
def shCell (k : Int) : Cell W32 Int → Cell W32 Int
  | .dat x j => .dat x j
  | .pb a j => .pb (mapAddr k a) j

/-- The shift on a write log. -/
def shLog (k : Int) (L : List (Addr Int × Cell W32 Int)) : List (Addr Int × Cell W32 Int) :=
  L.map (fun p => (mapAddr k p.1, shCell k p.2))

/-- The shift on the register file and the write log (flags/assume are handled relationally). -/
def sh (k : Int) (s : CS) : CS :=
  { s with gpr := s.gpr.map (shVal k), mem := shLog k s.mem }

/-- The initial memory to run against at the shifted stack: a lookup at the shifted address
returns the shifted cell of the original initial memory. -/
def memSh (k : Int) (m : Addr Int → Cell W32 Int) : Addr Int → Cell W32 Int :=
  fun a => shCell k (m (mapAddr (-k) a))

theorem memSh_mapAddr (k : Int) (m : Addr Int → Cell W32 Int) (a : Addr Int) :
    memSh k m (mapAddr k a) = shCell k (m a) := by
  simp only [memSh, mapAddr_inv]

@[simp] theorem sh_gpr (k : Int) (s : CS) : (sh k s).gpr = s.gpr.map (shVal k) := rfl
@[simp] theorem sh_vr (k : Int) (s : CS) : (sh k s).vr = s.vr := rfl
@[simp] theorem sh_flags (k : Int) (s : CS) : (sh k s).flags = s.flags := rfl
@[simp] theorem sh_mem (k : Int) (s : CS) : (sh k s).mem = shLog k s.mem := rfl
@[simp] theorem sh_pc (k : Int) (s : CS) : (sh k s).pc = s.pc := rfl
@[simp] theorem sh_halted (k : Int) (s : CS) : (sh k s).halted = s.halted := rfl
@[simp] theorem sh_tail (k : Int) (s : CS) : (sh k s).tail = s.tail := rfl
@[simp] theorem sh_err (k : Int) (s : CS) : (sh k s).err = s.err := rfl
@[simp] theorem sh_assume (k : Int) (s : CS) : (sh k s).assume = s.assume := rfl
@[simp] theorem sh_getV (k : Int) (s : CS) (i : Nat) : (sh k s).getV i = s.getV i := rfl
@[simp] theorem sh_getQ (k : Int) (s : CS) (i : Nat) : getQ (sh k s) i = getQ s i := rfl
@[simp] theorem sh_getD (k : Int) (s : CS) (i : Nat) : getD (sh k s) i = getD s i := rfl

theorem sh_gpr_getD (k : Int) (s : CS) (i : Nat) :
    (s.gpr.map (shVal k)).getD i (.num (Lane.const 0) (Lane.const 0))
      = shVal k (s.gpr.getD i (.num (Lane.const 0) (Lane.const 0))) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s.gpr[i]? <;> rfl

theorem getG_sh (k : Int) (s : CS) (i : Nat) : (sh k s).getG i = shVal k (s.getG i) := by
  simp only [State.getG, sh]
  exact sh_gpr_getD k s i

theorem setG_sh (k : Int) (s : CS) (i : Nat) (v : Val W32 Int) :
    (sh k s).setG i (shVal k v) = sh k (s.setG i v) := by
  simp only [State.setG, sh]
  rw [List.map_set]

theorem setV_sh (k : Int) (s : CS) (i : Nat) (v : List W32) :
    (sh k s).setV i v = sh k (s.setV i v) := rfl

theorem setW_sh (k : Int) (s : CS) (d : Nat) (x : W32) : setW (sh k s) d x = sh k (setW s d x) := by
  simp only [setW]
  exact setG_sh k s d (.num x (Lane.const 0))

theorem setQ_sh (k : Int) (s : CS) (d : Nat) (v : List W32) :
    setQ (sh k s) d v = sh k (setQ s d v) := by
  simp only [setQ]
  rw [setV_sh]

theorem setD_sh (k : Int) (s : CS) (d : Nat) (v : List W32) :
    setD (sh k s) d v = sh k (setD s d v) := by
  simp only [setD]
  rw [setV_sh]

theorem next_sh (k : Int) (s : CS) : (sh k s).next = sh k s.next := rfl

theorem halt_sh (k : Int) (s : CS) : halt (sh k s) = sh k (halt s) := rfl

theorem fail_sh (k : Int) (s : CS) (msg : String) :
    (sh k s).fail msg = sh k (s.fail msg) := by
  unfold State.fail sh
  split <;> rfl

theorem getC_sh (k : Int) (s : CS) (i : Nat) :
    getC (sh k s) i = (getC s i).map (mapAddr k) := by
  unfold getC
  rw [getG_sh]
  cases h : s.getG i with
  | ptr a => rfl
  | num lo hi =>
    cases h1 : Lane.asConst lo <;> cases h2 : Lane.asConst hi <;>
      simp only [h1, h2, shVal, pure_ok, throw_error, except_map_ok, except_map_error]
    rw [mapAddr_num]

theorem getW_sh (k : Int) (s : CS) (i : Nat) : getW (sh k s) i = getW s i := by
  unfold getW
  rw [getG_sh]
  cases h : s.getG i with
  | num lo hi => rfl
  | ptr a =>
    obtain ⟨r, o⟩ := a
    by_cases hr : r = rStack
    · subst hr
      rfl
    · simp only [shVal]
      rw [mapAddr_of_ne k ⟨r, o⟩ hr]

theorem getX_sh (k : Int) (s : CS) (i : Nat) : getX (sh k s) i = getX s i := by
  unfold getX
  rw [getG_sh]
  cases h : s.getG i with
  | num lo hi => rfl
  | ptr a =>
    obtain ⟨r, o⟩ := a
    by_cases hr : r = rStack
    · subst hr
      rfl
    · simp only [shVal]
      rw [mapAddr_of_ne k ⟨r, o⟩ hr]

/-! ## Memory -/

theorem lookup_sh (k : Int) (a : Addr Int) (L : List (Addr Int × Cell W32 Int)) :
    lookup (mapAddr k a) (shLog k L)
      = (lookup a L).map (Option.map (shCell k)) := by
  induction L with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨b, c⟩ := p
    have hsh : shLog k ((b, c) :: rest) = (mapAddr k b, shCell k c) :: shLog k rest := rfl
    rw [hsh]
    simp only [lookup, same_sh]
    cases h : AddrEq.same a b with
    | some x => cases x <;> simp only [Except.map, Option.map, ih]
    | none => rfl

theorem readCell_sh (k : Int) (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) :
    readCell (memSh k mem0) (sh k s) (mapAddr k a) = (readCell mem0 s a).map (shCell k) := by
  unfold readCell
  rw [sh_mem]
  cases h : lookup a s.mem with
  | ok o =>
    cases o with
    | none =>
      rw [lookup_sh, h]
      simp only [except_map_ok, Option.map_none, memSh_mapAddr]
    | some c =>
      rw [lookup_sh, h]
      simp only [except_map_ok, Option.map_some]
  | error e =>
    rw [lookup_sh, h]
    simp only [except_map_error]

theorem cellData_sh (k : Int) (c : Cell W32 Int) : cellData (shCell k c) = cellData c := by
  cases c with
  | dat x j => rfl
  | pb a j => rfl

theorem lanePat_sh (k : Int) (c0 c1 c2 c3 : Cell W32 Int) :
    lanePat (shCell k c0) (shCell k c1) (shCell k c2) (shCell k c3)
      = lanePat c0 c1 c2 c3 := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem loadLane_sh (k : Int) (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) :
    loadLane (memSh k mem0) (sh k s) (mapAddr k a) = loadLane mem0 s a := by
  unfold loadLane
  simp only [readCell_sh, ← mapAddr_add, except_bind_map (g := shCell k), lanePat_sh, cellData_sh]

theorem loadLanes_sh (k : Int) (mem0 : Addr Int → Cell W32 Int) (s : CS) (a : Addr Int) (n : Nat) :
    loadLanes (memSh k mem0) (sh k s) (mapAddr k a) n = loadLanes mem0 s a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    unfold loadLanes
    rw [loadLane_sh, ← mapAddr_add, ih]

theorem storeLane_sh (k : Int) (s : CS) (a : Addr Int) (x : W32) :
    storeLane (sh k s) (mapAddr k a) x = sh k (storeLane s a x) := by
  unfold storeLane sh shLog
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons]
  rw [← mapAddr_add, ← mapAddr_add, ← mapAddr_add]
  rfl

theorem storeLanes_sh (k : Int) (s : CS) (a : Addr Int) (xs : List W32) :
    storeLanes (sh k s) (mapAddr k a) xs = sh k (storeLanes s a xs) := by
  induction xs generalizing a s with
  | nil => rfl
  | cons x xs ih =>
    unfold storeLanes
    rw [storeLane_sh, ← mapAddr_add, ih]

/-! ## Address formation and load/store steps -/

theorem baseAddr_sh (k : Int) (s : CS) (n : Nat) (hk : k % 16 = 0) :
    baseAddr (sh k s) n = (baseAddr s n).map (mapAddr k) := by
  unfold baseAddr
  rw [getG_sh]
  cases h : s.getG n with
  | num lo hi => rfl
  | ptr a =>
    obtain ⟨r, o⟩ := a
    simp only [shVal]
    by_cases hr : r = rNum
    · subst hr
      rfl
    · simp only [mapAddr_region, hr, ite_false]
      by_cases hn : n = sp
      · subst hn
        change (if (mapAddr k ⟨r, o⟩).off % 16 = 0 then Except.ok (mapAddr k ⟨r, o⟩)
            else Except.error "SP alignment fault")
          = Except.map (mapAddr k) (if o % 16 = 0 then Except.ok ⟨r, o⟩
            else Except.error "SP alignment fault")
        by_cases hs : r = rStack
        · subst hs
          rw [mapAddr_stack, except_map_ite, align_add k o hk]
          by_cases hz : o % 16 = 0
          · rw [if_pos hz, if_pos hz]
            simp only [except_map_ok, except_map_error, mapAddr_stack]
          · rw [if_neg hz, if_neg hz]
            simp only [except_map_ok, except_map_error]
        · rw [mapAddr_of_ne k ⟨r, o⟩ hs]
          change (if o % 16 = 0 then Except.ok ⟨r, o⟩ else Except.error "SP alignment fault")
            = Except.map (mapAddr k)
              (if o % 16 = 0 then Except.ok ⟨r, o⟩ else Except.error "SP alignment fault")
          rw [except_map_ite]
          by_cases hz : o % 16 = 0
          · rw [if_pos hz, if_pos hz]
            simp only [except_map_ok, except_map_error, mapAddr_of_ne k ⟨r, o⟩ hs]
          · rw [if_neg hz, if_neg hz]
            simp only [except_map_ok, except_map_error]
      · simp only [hn, ite_false]
        change Except.ok (mapAddr k ⟨r, o⟩) = Except.map (mapAddr k) (Except.ok ⟨r, o⟩)
        simp only [except_map_ok]

theorem addrWB_sh (k : Int) (s : CS) (n : Nat) (i : Idx) (hk : k % 16 = 0) :
    addrWB (sh k s) n i
      = (addrWB s n i).map (fun p => (mapAddr k p.1, p.2.map (mapAddr k))) := by
  unfold addrWB
  rw [baseAddr_sh k s n hk]
  cases h : baseAddr s n with
  | error e => rfl
  | ok b =>
    cases i with
    | off o => simp only [Except.map, mapAddr_add, Option.map_none]
    | pre o => simp only [Except.map, mapAddr_add, Option.map_some]
    | post o => simp only [Except.map, mapAddr_add, Option.map_some]
    | postR m =>
      by_cases hm : m = sp
      · subst hm
        rfl
      · simp only [hm, ite_false]
        rw [getC_sh]
        cases hg : getC s m with
        | error e => rfl
        | ok x =>
          obtain ⟨rx, ox⟩ := x
          simp only [Except.map, Option.map]
          by_cases hx : rx = rNum
          · subst hx
            rw [mapAddr_num]
            change Except.ok (mapAddr k b, some ((mapAddr k b).plus ox))
              = (if rNum = rNum then Except.ok (b, some (b.plus ox))
                  else Except.error "post-index by a pointer").map
                  (fun p => (mapAddr k p.1, p.2.map (mapAddr k)))
            rw [if_pos rfl]
            simp only [except_map_ok, Option.map_some, mapAddr_plus]
          · simp only [mapAddr_region, hx, ite_false]

theorem writeBack_sh (k : Int) (s : CS) (n : Nat) (a : Option (Addr Int)) :
    writeBack (sh k s) n (a.map (mapAddr k)) = sh k (writeBack s n a) := by
  cases a with
  | none => rfl
  | some a => exact setG_sh k s n (.ptr a)

/-! ## The whitelist of instruction forms occurring in the kernel -/

/-- The instruction forms of the stream, as they occur in `ShaX1.prog`: the scan is a `decide`
lemma in the driver. -/
def Canon : Instr → Bool
  | .subi _ _ _ => true
  | .adrp _ _ => true
  | .addLo12 _ _ _ => true
  | .addr _ _ _ _ => true
  | .vop _ _ _ _ => true
  | .rev32 _ _ => true
  | .sha256su0 _ _ => true
  | .sha256h _ _ _ => true
  | .sha256h2 _ _ _ => true
  | .sha256su1 _ _ _ => true
  | .b _ => true
  | .ret => true
  | .cmpr _ _ => true
  | .bcc _ _ => true
  | .ld1 _ _ _ _ => true
  | .st1 _ _ _ _ => true
  | .ldp .d _ _ _ _ => true
  | .stp .d _ _ _ _ => true
  | _ => false

/-- The canonical forms that neither read nor write the flags. -/
def FlagFree : Instr → Bool
  | .subi _ _ _ => true
  | .adrp _ _ => true
  | .addLo12 _ _ _ => true
  | .addr _ _ _ _ => true
  | .vop _ _ _ _ => true
  | .rev32 _ _ => true
  | .sha256su0 _ _ => true
  | .sha256h _ _ _ => true
  | .sha256h2 _ _ _ => true
  | .sha256su1 _ _ _ => true
  | .b _ => true
  | .ret => true
  | .ld1 _ _ _ _ => true
  | .st1 _ _ _ _ => true
  | .ldp .d _ _ _ _ => true
  | .stp .d _ _ _ _ => true
  | _ => false

theorem canon_of_flagFree (i : Instr) (h : FlagFree i = true) : Canon i = true := by
  cases i with
  | ldp sz t1 t2 n idx => cases sz <;> simp [Canon, FlagFree] at h ⊢
  | stp sz t1 t2 n idx => cases sz <;> simp [Canon, FlagFree] at h ⊢
  | _ => simp [Canon, FlagFree] at h ⊢

/-! ## Flags are irrelevant to the non-flag instructions -/

/-- A state with the flags overwritten. -/
def setFl (fl : Option (Int × Int)) (s : CS) : CS := { s with flags := fl }

@[simp] theorem setFl_gpr (fl : Option (Int × Int)) (s : CS) : (setFl fl s).gpr = s.gpr := rfl
@[simp] theorem setFl_vr (fl : Option (Int × Int)) (s : CS) : (setFl fl s).vr = s.vr := rfl
@[simp] theorem setFl_flags (fl : Option (Int × Int)) (s : CS) : (setFl fl s).flags = fl := rfl
@[simp] theorem setFl_mem (fl : Option (Int × Int)) (s : CS) : (setFl fl s).mem = s.mem := rfl
@[simp] theorem setFl_pc (fl : Option (Int × Int)) (s : CS) : (setFl fl s).pc = s.pc := rfl
@[simp] theorem setFl_halted (fl : Option (Int × Int)) (s : CS) : (setFl fl s).halted = s.halted := rfl
@[simp] theorem setFl_tail (fl : Option (Int × Int)) (s : CS) : (setFl fl s).tail = s.tail := rfl
@[simp] theorem setFl_err (fl : Option (Int × Int)) (s : CS) : (setFl fl s).err = s.err := rfl
@[simp] theorem setFl_assume (fl : Option (Int × Int)) (s : CS) : (setFl fl s).assume = s.assume := rfl

theorem setFl_mk (fl : Option (Int × Int)) (gpr : List (Val W32 Int)) (vr : List (List W32))
    (flags : Option (Int × Int)) (mem : List (Addr Int × Cell W32 Int)) (pc : Nat)
    (halted : Bool) (tail : Option String) (err : Option String)
    (assume : List (Cond Int × Bool)) :
    setFl fl ⟨gpr, vr, flags, mem, pc, halted, tail, err, assume⟩
      = ⟨gpr, vr, fl, mem, pc, halted, tail, err, assume⟩ := rfl

@[simp] theorem setFl_getG (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    (setFl fl s).getG i = s.getG i := rfl
@[simp] theorem setFl_getV (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    (setFl fl s).getV i = s.getV i := rfl
@[simp] theorem setFl_getQ (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    getQ (setFl fl s) i = getQ s i := rfl
@[simp] theorem setFl_getD (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    getD (setFl fl s) i = getD s i := rfl

@[simp] theorem setFl_setG (fl : Option (Int × Int)) (s : CS) (i : Nat) (v : Val W32 Int) :
    setFl fl (s.setG i v) = (setFl fl s).setG i v := rfl
@[simp] theorem setFl_setV (fl : Option (Int × Int)) (s : CS) (i : Nat) (v : List W32) :
    setFl fl (s.setV i v) = (setFl fl s).setV i v := rfl
@[simp] theorem setFl_setW (fl : Option (Int × Int)) (s : CS) (i : Nat) (x : W32) :
    setFl fl (setW s i x) = setW (setFl fl s) i x := rfl
@[simp] theorem setFl_setQ (fl : Option (Int × Int)) (s : CS) (i : Nat) (v : List W32) :
    setFl fl (setQ s i v) = setQ (setFl fl s) i v := rfl
@[simp] theorem setFl_setD (fl : Option (Int × Int)) (s : CS) (i : Nat) (v : List W32) :
    setFl fl (setD s i v) = setD (setFl fl s) i v := rfl
@[simp] theorem setFl_next (fl : Option (Int × Int)) (s : CS) :
    setFl fl s.next = (setFl fl s).next := rfl
@[simp] theorem setFl_halt (fl : Option (Int × Int)) (s : CS) :
    setFl fl (halt s) = halt (setFl fl s) := rfl
@[simp] theorem setFl_storeLane (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (x : W32) :
    setFl fl (storeLane s a x) = storeLane (setFl fl s) a x := rfl

@[simp] theorem setFl_ite (fl : Option (Int × Int)) (h : Prop) [Decidable h] (a b : CS) :
    setFl fl (if h then a else b) = if h then setFl fl a else setFl fl b := by
  by_cases hh : h <;> simp [hh]

@[simp] theorem setFl_fail (fl : Option (Int × Int)) (s : CS) (msg : String) :
    setFl fl (s.fail msg) = (setFl fl s).fail msg := by
  unfold State.fail
  by_cases h : s.err.isSome <;> simp [h, setFl]

theorem setFl_storeLanes (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (xs : List W32) :
    setFl fl (storeLanes s a xs) = storeLanes (setFl fl s) a xs := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih =>
    simp only [storeLanes]
    rw [ih]
    rfl

theorem setFl_storeVal (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (v : Val W32 Int) :
    setFl fl (storeVal s a v) = storeVal (setFl fl s) a v := by
  cases v with
  | num lo hi => simp [storeVal]
  | ptr p => simp [storeVal, setFl]

theorem setFl_writeBack (fl : Option (Int × Int)) (s : CS) (n : Nat) (a : Option (Addr Int)) :
    setFl fl (writeBack s n a) = writeBack (setFl fl s) n a := by
  cases a <;> rfl

theorem writeBack_setFl (fl : Option (Int × Int)) (s : CS) (n : Nat) (a : Option (Addr Int)) :
    writeBack (setFl fl s) n a = setFl fl (writeBack s n a) :=
  (setFl_writeBack fl s n a).symm

@[simp] theorem readCell_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) : readCell mem0 (setFl fl s) a = readCell mem0 s a := rfl
@[simp] theorem loadLane_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) : loadLane mem0 (setFl fl s) a = loadLane mem0 s a := rfl
@[simp] theorem loadLanes_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (n : Nat) : loadLanes mem0 (setFl fl s) a n = loadLanes mem0 s a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [loadLanes, ih]
@[simp] theorem loadVal_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) : loadVal mem0 (setFl fl s) a = loadVal mem0 s a := rfl
@[simp] theorem getC_fl (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    getC (setFl fl s) i = getC s i := rfl
@[simp] theorem getW_fl (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    getW (setFl fl s) i = getW s i := rfl
@[simp] theorem getX_fl (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    getX (setFl fl s) i = getX s i := rfl
@[simp] theorem baseAddr_fl (fl : Option (Int × Int)) (s : CS) (n : Nat) :
    baseAddr (setFl fl s) n = baseAddr s n := rfl
@[simp] theorem addrWB_fl (fl : Option (Int × Int)) (s : CS) (n : Nat) (i : Idx) :
    addrWB (setFl fl s) n i = addrWB s n i := rfl

theorem okOr_setFl (fl : Option (Int × Int)) (s : CS) (r : Except String CS) :
    setFl fl (okOr s r) = okOr (setFl fl s) (r.map (setFl fl)) := by
  cases r with
  | ok s' => rfl
  | error e => exact setFl_fail fl s e

theorem okOr_ite_fl (fl : Option (Int × Int)) (c : Prop) [Decidable c]
    (a b : Except String CS) (s : CS) :
    okOr s (if c then a else b) = if c then okOr s a else okOr s b := by
  by_cases h : c <;> simp [h]

theorem loadReg_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s0 s : CS)
    (sz : Sz) (t : Nat) (a : Addr Int) :
    loadReg mem0 (setFl fl s0) (setFl fl s) sz t a
      = (loadReg mem0 s0 s sz t a).map (setFl fl) := by
  cases sz <;> simp only [loadReg] <;> (try split) <;>
    simp only [pure_ok, throw_error, okOr_ok, okOr_error, loadLane_fl, loadVal_fl, loadLanes_fl,
      setFl_setW, setFl_setD, setFl_setQ, setFl_setG, except_map_ite, except_map_bind,
      except_map_ok, except_map_error] <;>
    rfl

theorem storeReg_fl (fl : Option (Int × Int)) (s0 s : CS) (sz : Sz) (t : Nat) (a : Addr Int) :
    storeReg (setFl fl s0) (setFl fl s) sz t a
      = (storeReg s0 s sz t a).map (setFl fl) := by
  cases sz <;> simp only [storeReg] <;> (try split) <;>
    simp only [pure_ok, throw_error, okOr_ok, okOr_error, getW_fl, getX_fl, setFl_getG,
      setFl_getD, setFl_getQ, setFl_storeLane, setFl_storeVal, setFl_storeLanes,
      except_map_ite, except_map_bind, except_map_ok, except_map_error] <;>
    rfl

theorem ld1Step_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (t : Nat) (st : CS) (j : Nat) :
    ld1Step mem0 (setFl fl s) a t (setFl fl st) j
      = (ld1Step mem0 s a t st j).map (setFl fl) := by
  simp only [ld1Step]
  simp only [pure_ok, throw_error, loadLanes_fl, setFl_setQ, except_map_bind, except_map_ok,
    except_map_error]

theorem ld4Step_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (t e : Nat) (st : CS) (r : Nat) :
    ld4Step mem0 (setFl fl s) a t e (setFl fl st) r
      = (ld4Step mem0 s a t e st r).map (setFl fl) := by
  simp only [ld4Step]
  simp only [pure_ok, throw_error, loadLane_fl, setFl_getQ, setFl_setQ, except_map_bind,
    except_map_ok, except_map_error]

@[simp] theorem st1Step_fl (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (t : Nat) (st : CS)
    (j : Nat) : st1Step (setFl fl s) a t (setFl fl st) j = setFl fl (st1Step s a t st j) := rfl
@[simp] theorem st4Step_fl (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (t e : Nat) (st : CS)
    (r : Nat) : st4Step (setFl fl s) a t e (setFl fl st) r = setFl fl (st4Step s a t e st r) := rfl

theorem foldlM_fl (fl : Option (Int × Int))
    (step : CS → CS → Nat → Except String CS)
    (hstep : ∀ s0 st j, step (setFl fl s0) (setFl fl st) j
      = (step s0 st j).map (setFl fl))
    (s0 init : CS) (l : List Nat) :
    l.foldlM (step (setFl fl s0)) (setFl fl init)
      = (l.foldlM (step s0) init).map (setFl fl) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldlM_cons]
    rw [hstep]
    rw [except_bind_map (setFl fl) (step s0 init j)
      (fun b => l.foldlM (step (setFl fl s0)) b)]
    simp only [ih]
    rw [← except_map_bind (setFl fl) (step s0 init j)
      (fun a => l.foldlM (step s0) a)]

theorem foldl_fl (fl : Option (Int × Int))
    (step : CS → CS → Nat → CS)
    (hstep : ∀ s0 st j, step (setFl fl s0) (setFl fl st) j = setFl fl (step s0 st j))
    (s0 init : CS) (l : List Nat) :
    l.foldl (step (setFl fl s0)) (setFl fl init) = setFl fl (l.foldl (step s0) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih => simp [List.foldl, hstep, ih]

theorem foldlM_ld1_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (t : Nat) (init : CS) (l : List Nat) :
    l.foldlM (ld1Step mem0 (setFl fl s) a t) (setFl fl init)
      = (l.foldlM (ld1Step mem0 s a t) init).map (setFl fl) :=
  foldlM_fl fl (fun s0 st j => ld1Step mem0 s0 a t st j)
    (fun s0 st j => ld1Step_fl fl mem0 s0 a t st j) s init l

theorem foldlM_ld4_fl (fl : Option (Int × Int)) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (t e : Nat) (init : CS) (l : List Nat) :
    l.foldlM (ld4Step mem0 (setFl fl s) a t e) (setFl fl init)
      = (l.foldlM (ld4Step mem0 s a t e) init).map (setFl fl) :=
  foldlM_fl fl (fun s0 st j => ld4Step mem0 s0 a t e st j)
    (fun s0 st j => ld4Step_fl fl mem0 s0 a t e st j) s init l

theorem foldl_st1_fl (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (t : Nat)
    (init : CS) (l : List Nat) :
    l.foldl (st1Step (setFl fl s) a t) (setFl fl init)
      = setFl fl (l.foldl (st1Step s a t) init) :=
  foldl_fl fl (fun s0 st j => st1Step s0 a t st j)
    (fun s0 st j => st1Step_fl fl s0 a t st j) s init l

theorem foldl_st4_fl (fl : Option (Int × Int)) (s : CS) (a : Addr Int) (t e : Nat)
    (init : CS) (l : List Nat) :
    l.foldl (st4Step (setFl fl s) a t e) (setFl fl init)
      = setFl fl (l.foldl (st4Step s a t e) init) :=
  foldl_fl fl (fun s0 st j => st4Step s0 a t e st j)
    (fun s0 st j => st4Step_fl fl s0 a t e st j) s init l

theorem exec_flags (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : CS) (fl : Option (Int × Int)) (hf : FlagFree i = true) :
    exec ro mem0 orc i (setFl fl s) = setFl fl (exec ro mem0 orc i s) := by
  by_cases hs : s.halted = true
  · simp [exec, hs, setFl]
  cases i with
  | ldp sz t1 t2 n idx =>
      cases sz <;> simp [FlagFree] at hf
      all_goals
        simp [exec, hs, setFl_mk, loadReg_fl, storeReg_fl, foldlM_ld1_fl, foldlM_ld4_fl,
          foldl_st1_fl, foldl_st4_fl, writeBack_setFl, except_bind_map, except_map_bind,
          okOr_setFl, except_map_ite, okOr_ite_fl] <;>
        first | rfl | (split <;> simp_all)
  | stp sz t1 t2 n idx =>
      cases sz <;> simp [FlagFree] at hf
      all_goals
        simp [exec, hs, setFl_mk, loadReg_fl, storeReg_fl, foldlM_ld1_fl, foldlM_ld4_fl,
          foldl_st1_fl, foldl_st4_fl, writeBack_setFl, except_bind_map, except_map_bind,
          okOr_setFl, except_map_ite, okOr_ite_fl] <;>
        first | rfl | (split <;> simp_all)
  | _ =>
      simp [FlagFree] at hf
      all_goals
        simp [exec, hs, setFl_mk, loadReg_fl, storeReg_fl, foldlM_ld1_fl, foldlM_ld4_fl,
          foldl_st1_fl, foldl_st4_fl, writeBack_setFl, except_bind_map, except_map_bind,
          okOr_setFl, except_map_ite, okOr_ite_fl] <;>
        first | rfl | (split <;> simp_all)

/-! ## Commutation with the shift: binds, loads, stores -/

theorem okOr_sh (k : Int) (s : CS) (r : Except String CS) :
    sh k (okOr s r) = okOr (sh k s) (r.map (sh k)) := by
  cases r with
  | ok s' => rfl
  | error e => exact (fail_sh k s e).symm

theorem map_sh_comp {β : Type} (k : Int) (h : β → CS) (x : Except String β) :
    (h <$> x).map (sh k) = ((sh k) ∘ h) <$> x := by
  cases x <;> rfl

theorem setG_ptr_sh (k : Int) (s : CS) (i : Nat) (a : Addr Int) :
    (sh k s).setG i (.ptr (mapAddr k a)) = sh k (s.setG i (.ptr a)) :=
  setG_sh k s i (.ptr a)

theorem setG_ptr_symbolic_sh (k : Int) (s : CS) (i : Nat) (r : Region) (o : Int)
    (h : r ≠ rStack) :
    (sh k s).setG i (.ptr (⟨r, o⟩ : Addr Int)) = sh k (s.setG i (.ptr ⟨r, o⟩)) := by
  have hv : shVal k (Val.ptr (⟨r, o⟩ : Addr Int)) = Val.ptr ⟨r, o⟩ := by
    show Val.ptr (mapAddr k ⟨r, o⟩) = Val.ptr ⟨r, o⟩
    rw [mapAddr_of_ne k _ h]
  calc (sh k s).setG i (.ptr (⟨r, o⟩ : Addr Int))
      = (sh k s).setG i (shVal k (.ptr ⟨r, o⟩)) := by rw [hv]
    _ = sh k (s.setG i (.ptr ⟨r, o⟩)) := setG_sh k s i (.ptr ⟨r, o⟩)

theorem sh_ite (k : Int) (c : Prop) [Decidable c] (a b : CS) :
    sh k (if c then a else b) = if c then sh k a else sh k b := by
  by_cases hc : c <;> simp [hc]

theorem bind_ok {α : Type} (a : α) (f : α → Except String CS) :
    (Except.ok a >>= f) = f a := rfl

theorem bind_error {α : Type} (e : String) (f : α → Except String CS) :
    (Except.error e >>= f) = Except.error e := rfl

theorem loadReg_d_sh (k : Int) (mem0 : Addr Int → Cell W32 Int) (s0 s : CS)
    (t : Nat) (a : Addr Int) :
    loadReg (memSh k mem0) (sh k s0) (sh k s) .d t (mapAddr k a)
      = (loadReg mem0 s0 s .d t a).map (sh k) := by
  simp only [loadReg, except_bind_pure, loadLanes_sh]
  rw [map_sh_comp]
  have hD : (sh k ∘ setD s t) = fun v => setD (sh k s) t v := by
    funext v
    exact setD_sh k s t v
  rw [hD]

theorem storeReg_d_sh (k : Int) (s0 s : CS) (t : Nat) (a : Addr Int) :
    storeReg (sh k s0) (sh k s) .d t (mapAddr k a)
      = (storeReg s0 s .d t a).map (sh k) := by
  simp only [storeReg, sh_getD, storeLanes_sh, pure_ok, except_map_ok]

theorem ld1Step_sh (k : Int) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (t : Nat) (st : CS) (j : Nat) :
    ld1Step (memSh k mem0) (sh k s) (mapAddr k a) t (sh k st) j
      = (ld1Step mem0 s a t st j).map (sh k) := by
  simp only [ld1Step, except_bind_pure, ← mapAddr_add, loadLanes_sh]
  rw [map_sh_comp]
  have hQ : (sh k ∘ setQ st ((t + j) % 32))
      = fun v => setQ (sh k st) ((t + j) % 32) v := by
    funext v
    exact setQ_sh k st ((t + j) % 32) v
  rw [hQ]

theorem st1Step_sh (k : Int) (s : CS) (a : Addr Int) (t : Nat) (st : CS) (j : Nat) :
    st1Step (sh k s) (mapAddr k a) t (sh k st) j = sh k (st1Step s a t st j) := by
  simp only [st1Step, ← mapAddr_add, storeLanes_sh, sh_getQ]

theorem foldlM_ld1_sh (k : Int) (mem0 : Addr Int → Cell W32 Int) (s : CS)
    (a : Addr Int) (t : Nat) (init : CS) (l : List Nat) :
    l.foldlM (ld1Step (memSh k mem0) (sh k s) (mapAddr k a) t) (sh k init)
      = (l.foldlM (ld1Step mem0 s a t) init).map (sh k) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldlM_cons]
    rw [ld1Step_sh]
    rw [except_bind_map (sh k) (ld1Step mem0 s a t init j)
      (fun b => l.foldlM (ld1Step (memSh k mem0) (sh k s) (mapAddr k a) t) b)]
    simp only [ih]
    rw [← except_map_bind (sh k) (ld1Step mem0 s a t init j)
      (fun st' => l.foldlM (ld1Step mem0 s a t) st')]

theorem foldl_st1_sh (k : Int) (s : CS) (a : Addr Int) (t : Nat)
    (init : CS) (l : List Nat) :
    l.foldl (st1Step (sh k s) (mapAddr k a) t) (sh k init)
      = sh k (l.foldl (st1Step s a t) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl]
    rw [st1Step_sh]
    exact ih (st1Step s a t init j)

/-! ## The flag-free instructions step the same way -/

theorem exec_sh (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : CS) (k : Int) (hro : ro ≠ rStack) (hk : k % 16 = 0)
    (hf : FlagFree i = true) :
    exec ro (memSh k mem0) orc i (sh k s) = sh k (exec ro mem0 orc i s) := by
  by_cases hs : s.halted = true
  · simp [exec, hs, sh]
  cases i with
  | ldp sz t1 t2 n idx =>
      cases sz <;> simp [FlagFree] at hf
      all_goals
        simp [exec, hs, okOr_sh, fail_sh, baseAddr_sh (hk := hk), addrWB_sh (hk := hk),
          writeBack_sh, loadReg_d_sh, ← mapAddr_add, next_sh, isGpr, except_bind_map,
          except_map_bind, except_map_ite, okOr_ite] <;>
        first | rfl | (split <;> simp_all [okOr_sh, fail_sh, isGpr, except_bind_map,
          except_map_bind, except_map_ite, okOr_ite, loadReg_d_sh, next_sh])
  | stp sz t1 t2 n idx =>
      cases sz <;> simp [FlagFree] at hf
      all_goals
        simp [exec, hs, okOr_sh, fail_sh, baseAddr_sh (hk := hk), addrWB_sh (hk := hk),
          writeBack_sh, storeReg_d_sh, ← mapAddr_add, next_sh, isGpr, except_bind_map,
          except_map_bind, except_map_ite, okOr_ite] <;>
        first | rfl | (split <;> simp_all [okOr_sh, fail_sh, isGpr, except_bind_map,
          except_map_bind, except_map_ite, okOr_ite, storeReg_d_sh, next_sh])
  | subi d n imm =>
      simp [FlagFree] at hf
      simp [exec, hs, okOr_sh, fail_sh, getC_sh, ← mapAddr_add, setG_ptr_sh, next_sh,
        except_bind_map, except_map_bind, except_map_ite, okOr_ite]
  | addLo12 d n off =>
      simp [FlagFree] at hf
      simp [exec, hs, okOr_sh, fail_sh, getC_sh, ← mapAddr_add, setG_ptr_sh, next_sh,
        except_bind_map, except_map_bind, except_map_ite, okOr_ite]
  | adrp d off =>
      simp [FlagFree] at hf
      by_cases hd : d = sp
      · simp [exec, hs, hd, fail_sh]
      · simp [exec, hs, hd, fail_sh, setG_ptr_symbolic_sh, hro, next_sh, except_bind_map,
          except_map_bind, except_map_ite, okOr_ite]
  | addr d n m shf =>
      simp [FlagFree] at hf
      cases h1 : getC s n with
      | error e =>
          simp [exec, hs, okOr_sh, fail_sh, getC_sh, h1, except_map_ok, except_map_error,
            bind_ok, bind_error, sh_ite, okOr_ite, except_map_ite, except_map_bind, rNum,
            rStack] <;>
          (split <;> simp_all [okOr_sh, fail_sh, bind_ok, bind_error, sh_ite, okOr_ite,
            except_map_ite, except_map_bind, except_map_ok, except_map_error, rNum, rStack])
      | ok a =>
        cases h2 : getC s m with
        | error e =>
            simp [exec, hs, okOr_sh, fail_sh, getC_sh, h1, h2, except_map_ok,
              except_map_error, bind_ok, bind_error, sh_ite, okOr_ite, except_map_ite,
              except_map_bind, rNum, rStack] <;>
            (split <;> simp_all [okOr_sh, fail_sh, bind_ok, bind_error, sh_ite, okOr_ite,
              except_map_ite, except_map_bind, except_map_ok, except_map_error, rNum, rStack])
        | ok b =>
          simp only [exec, hs, Bool.false_eq_true, ite_false, okOr_sh, fail_sh, getC_sh,
            h1, h2, except_bind_map, except_map_bind, except_map_ite, except_map_ok,
            except_map_error, okOr_ite]
          split
          · simp_all [fail_sh]
          · by_cases hb : b.region = 0
            · simp_all [fail_sh, okOr_sh, okOr_ok, okOr_error, okOr_ite, sh_ite, bind_ok,
                bind_error, setG_ptr_sh, next_sh, ← mapAddr_plus, mapAddr_add, mapAddr_off,
                mapAddr_region, except_map_ite, except_map_bind, except_map_ok,
                except_map_error, hb, rNum, rStack]
            · by_cases h1 : a.region = 0
              · by_cases h2 : shf = 0
                · simp_all [fail_sh, okOr_sh, okOr_ok, okOr_error, okOr_ite, sh_ite, bind_ok,
                  bind_error, setG_ptr_sh, next_sh, ← mapAddr_plus, mapAddr_add, mapAddr_off,
                  mapAddr_region, except_map_ite, except_map_bind, except_map_ok,
                  except_map_error, hb, h1, h2, rNum, rStack]
                · simp_all [fail_sh, okOr_sh, okOr_ok, okOr_error, okOr_ite, sh_ite, bind_ok,
                  bind_error, setG_ptr_sh, next_sh, ← mapAddr_plus, mapAddr_add, mapAddr_off,
                  mapAddr_region, except_map_ite, except_map_bind, except_map_ok,
                  except_map_error, hb, h1, h2, rNum, rStack]
              · simp_all [fail_sh, okOr_sh, okOr_ok, okOr_error, okOr_ite, sh_ite, bind_ok,
                  bind_error, setG_ptr_sh, next_sh, ← mapAddr_plus, mapAddr_add, mapAddr_off,
                  mapAddr_region, except_map_ite, except_map_bind, except_map_ok,
                  except_map_error, hb, h1, rNum, rStack]
  | ret =>
      simp [FlagFree] at hf
      simp [exec, hs, okOr_sh, fail_sh, getG_sh, halt_sh, except_map_ok, except_map_error]
      cases h : s.getG 30 with
      | num lo hi => rfl
      | ptr a =>
        obtain ⟨r, o⟩ := a
        by_cases hr : r = 5 <;> by_cases hr3 : r = 3 <;>
          simp [shVal, mapAddr, halt_sh, fail_sh, okOr_sh, okOr_ok, okOr_error,
            mapAddr_stack, mapAddr_num, mapAddr_off, hr, hr3, rStack]
  | _ =>
      simp [FlagFree] at hf
      all_goals
        simp [exec, hs, okOr_sh, fail_sh, baseAddr_sh (hk := hk), addrWB_sh (hk := hk),
          writeBack_sh, foldlM_ld1_sh, foldl_st1_sh, ← mapAddr_add, next_sh, setQ_sh,
          except_bind_map, except_map_bind, except_map_ite, okOr_ite] <;>
        first | rfl | (split <;> simp_all [okOr_sh, fail_sh, except_bind_map,
          except_map_bind, except_map_ite, okOr_ite, foldlM_ld1_sh, foldl_st1_sh, next_sh])


/-! ## The run-level relation -/

/-- Flags of the shifted side are either the same pair or both offsets moved by `k` (which of the
two depends on the region of the compared values, no longer recorded in the flags). -/
def FlRel (k : Int) : Option (Int × Int) → Option (Int × Int) → Prop
  | none, none => True
  | some (a1, b1), some (a2, b2) =>
      (a1 = a2 ∧ b1 = b2) ∨ (a1 = a2 + k ∧ b1 = b2 + k)
  | _, _ => False

/-- The shifted run's state, up to the flags. -/
structure Rel (k : Int) (s1 s2 : CS) : Prop where
  gpr : s1.gpr = (sh k s2).gpr
  vr : s1.vr = (sh k s2).vr
  fl : FlRel k s1.flags s2.flags
  mem : s1.mem = (sh k s2).mem
  pc : s1.pc = s2.pc
  halted : s1.halted = s2.halted
  tail : s1.tail = s2.tail
  err : s1.err = s2.err
  assume : s1.assume = s2.assume

theorem rel_of_setFl {k : Int} {s1 s2 : CS} {fl : Option (Int × Int)}
    (h : s1 = setFl fl (sh k s2)) (hf : FlRel k fl s2.flags) : Rel k s1 s2 := by
  subst h
  exact ⟨rfl, rfl, hf, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Rel.to_setFl {k : Int} {s1 s2 : CS} (h : Rel k s1 s2) :
    s1 = setFl s1.flags (sh k s2) := by
  obtain ⟨hg, hv, hf, hm, hp, hh, ht, he, ha⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, h1, t1, e1, a1⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, h2, t2, e2, a2⟩ := s2
  simp only [sh, setFl, shLog] at hg hv hm hp hh ht he ha ⊢
  simp_all

theorem rel_sh (k : Int) (s : CS) : Rel k (sh k s) s := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hs : s.flags <;> simp [sh, hs, FlRel]

theorem fail_rel {k : Int} {s1 s2 : CS} (h : Rel k s1 s2) (msg : String) :
    Rel k (s1.fail msg) (s2.fail msg) := by
  obtain ⟨hg, hv, hf, hm, hp, hh, ht, he, ha⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, h1, t1, e1, a1⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, h2, t2, e2, a2⟩ := s2
  simp only [sh, State.fail] at hg hv hm hp hh ht he ha ⊢
  rw [show e1 = e2 from he] at *
  by_cases hsome : e2.isSome = true <;>
    simp only [hsome, if_true, ite_false, Bool.false_eq_true] <;>
    exact ⟨hg, hv, hf, hm, hp, rfl, ht, rfl, ha⟩

/-! ### Flags and branch decisions -/

theorem decideC_some (c : Cond Int) : ∃ b, c.decideC = some b := by
  cases c with
  | eq a b => exact ⟨_, rfl⟩
  | lt a b => exact ⟨_, rfl⟩
  | le a b => exact ⟨_, rfl⟩
  | not c => obtain ⟨b, hb⟩ := decideC_some c; exact ⟨!b, by simp [Cond.decideC, hb]⟩
  | tt => exact ⟨true, rfl⟩

theorem decideC_isNone (c : Cond Int) : c.decideC.isNone = false := by
  obtain ⟨b, hb⟩ := decideC_some c
  simp [hb]

theorem branch_some (s : CS) (orc : Nat → Bool) (c : Cond Int) (t : Nat) (b : Bool)
    (hb : c.decideC = some b) :
    s.branch orc c t = if b then { s with pc := t } else s.next := by
  simp [State.branch, hb]

theorem decideC_shift (c : CC) (a b : Int) (k : Int) :
    (ccCond c (a + k) (b + k)).decideC = (ccCond c a b).decideC := by
  have h : ∀ a b : Int,
      Ctl.add (a + k) (Ctl.smul (-1) (b + k)) = Ctl.add a (Ctl.smul (-1) b) := by
    intro a b
    show (a + k) + (-1) * (b + k) = a + (-1) * b
    omega
  cases c <;> simp [ccCond, Cond.decideC, Ctl.sub, h]

/-! ### The instructions that do not read or write the flags -/

theorem exec_flags_same (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : CS) (hf : FlagFree i = true) :
    (exec ro mem0 orc i s).flags = s.flags := by
  have h := exec_flags ro mem0 orc i s s.flags hf
  have h2 : setFl s.flags s = s := by cases s; rfl
  rw [h2] at h
  rw [h]
  rfl

theorem exec_rel_ff (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (k : Int) (hro : ro ≠ rStack) (hk : k % 16 = 0)
    (hf : FlagFree i = true) {s1 s2 : CS} (h : Rel k s1 s2) :
    Rel k (exec ro (memSh k mem0) orc i s1) (exec ro mem0 orc i s2) := by
  apply rel_of_setFl
  · rw [h.to_setFl, exec_flags ro (memSh k mem0) orc i (sh k s2) s1.flags hf,
      exec_sh ro mem0 orc i s2 k hro hk hf]
  · rw [exec_flags_same ro mem0 orc i s2 hf]
    exact h.fl


/-! ## Projections through the shift and the flag overwrite -/

theorem getC_setFl (fl : Option (Int × Int)) (s : CS) (i : Nat) :
    getC (setFl fl s) i = getC s i := rfl

theorem fail_flags (s : CS) (msg : String) : (s.fail msg).flags = s.flags := by
  unfold State.fail
  split <;> rfl

theorem FlRel_fail_any {k : Int} {o : Option (Int × Int)} {s : CS} (msg : String)
    (h : FlRel k o s.flags) : FlRel k o (s.fail msg).flags := by
  rw [fail_flags]; exact h

theorem setFlags_setFl (fl : Option (Int × Int)) (s : CS) (a b : Int) :
    setFlags (setFl fl s) a b = setFl (some (a, b)) (setFlags s a b) := rfl

theorem setFlags_sh (k : Int) (s : CS) (a b : Int) :
    setFlags (sh k s) a b = sh k (setFlags s a b) := rfl

/-! ### Flag relation helpers -/

theorem flRel_none {k : Int} {o : Option (Int × Int)} (h : FlRel k o none) : o = none := by
  cases o with
  | none => rfl
  | some p =>
    obtain ⟨a, b⟩ := p
    simp [FlRel] at h

theorem flRel_some {k : Int} {o : Option (Int × Int)} {a2 b2 : Int}
    (h : FlRel k o (some (a2, b2))) :
    ∃ a1 b1, o = some (a1, b1) ∧
      ((a1 = a2 ∧ b1 = b2) ∨ (a1 = a2 + k ∧ b1 = b2 + k)) := by
  cases o with
  | none => simp [FlRel] at h
  | some p =>
    obtain ⟨a1, b1⟩ := p
    exact ⟨a1, b1, rfl, by simpa [FlRel] using h⟩

theorem FlRel_of_mapAddr {k : Int} {a1 a2 b1 b2 : Addr Int}
    (ha : a1 = mapAddr k a2) (hb : b1 = mapAddr k b2) (hreg : a2.region = b2.region) :
    FlRel k (some (a1.off, b1.off)) (some (a2.off, b2.off)) := by
  rw [ha, hb, mapAddr_off, mapAddr_off]
  by_cases hs : a2.region = rStack
  · have hs' : b2.region = rStack := by rw [← hreg, hs]
    simp [hs, hs', FlRel]
  · have hs' : ¬ (b2.region = rStack) := by rw [← hreg]; exact hs
    simp [hs, hs', FlRel]

theorem Rel.next {k : Int} {s1 s2 : CS} (h : Rel k s1 s2) : Rel k s1.next s2.next := by
  obtain ⟨hg, hv, hf, hm, hp, hh, ht, he, ha⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, h1, t1, e1, a1⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, h2, t2, e2, a2⟩ := s2
  simp only [sh, State.next] at hg hv hm hp hh ht he ha ⊢
  refine ⟨hg, hv, hf, hm, ?_, hh, ht, he, ha⟩
  show p1 + 1 = p2 + 1
  omega

theorem Rel.setPc {k : Int} {s1 s2 : CS} (h : Rel k s1 s2) (t : Nat) :
    Rel k { s1 with pc := t } { s2 with pc := t } := by
  obtain ⟨hg, hv, hf, hm, hp, hh, ht, he, ha⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, h1, t1, e1, a1⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, h2, t2, e2, a2⟩ := s2
  simp only [sh] at hg hv hm hp hh ht he ha ⊢
  exact ⟨hg, hv, hf, hm, rfl, hh, ht, he, ha⟩

theorem Rel.sFlags {k : Int} {s1 s2 : CS} (h : Rel k s1 s2) {a1 b1 a2 b2 : Int}
    (hf : FlRel k (some (a1, b1)) (some (a2, b2))) :
    Rel k (Hashtree.Asm.Arm.setFlags s1 a1 b1) (Hashtree.Asm.Arm.setFlags s2 a2 b2) := by
  obtain ⟨hg, hv, _, hm, hp, hh, ht, he, ha⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, h1, t1, e1, a1'⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, h2, t2, e2, a2'⟩ := s2
  simp only [sh, Hashtree.Asm.Arm.setFlags] at hg hv hm hp hh ht he ha ⊢
  exact ⟨hg, hv, hf, hm, hp, hh, ht, he, ha⟩

theorem Rel.sFlags_next {k : Int} {s1 s2 : CS} (h : Rel k s1 s2) {a1 b1 a2 b2 : Int}
    (hf : FlRel k (some (a1, b1)) (some (a2, b2))) :
    Rel k (Hashtree.Asm.Arm.setFlags s1 a1 b1).next (Hashtree.Asm.Arm.setFlags s2 a2 b2).next :=
  (Rel.sFlags h hf).next

/-! ### The two flag-reading instructions -/

theorem exec_cmpr_rel (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (n m : Nat) (k : Int) {s1 s2 : CS} (h : Rel k s1 s2) :
    Rel k (exec ro (memSh k mem0) orc (.cmpr n m) s1) (exec ro mem0 orc (.cmpr n m) s2) := by
  by_cases hh : s2.halted = true
  · have hh1 : s1.halted = true := by rw [h.halted]; exact hh
    simp [exec, hh, hh1]
    exact h
  · rw [h.to_setFl]
    simp only [exec, hh, sh_halted, setFl_halted, sh_flags, setFl_flags, getC_setFl, getC_sh, mapAddr_region,
      ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
    by_cases hsp : n = sp ∨ m = sp
    · simp only [if_pos hsp, throw_error, okOr_error, ← setFl_fail, fail_sh]
      refine rel_of_setFl rfl ?_
      exact FlRel_fail_any _ h.fl
    · simp only [if_neg hsp]
      cases hn : getC s2 n with
      | error e =>
          simp only [hn, Except.map, throw_error, bind_error, okOr_error, ← setFl_fail, fail_sh]
          refine rel_of_setFl rfl ?_
          exact FlRel_fail_any _ h.fl
      | ok a =>
          cases hm : getC s2 m with
          | error e =>
              simp only [hn, hm, Except.map, throw_error, bind_ok, bind_error, okOr_error,
                ← setFl_fail, fail_sh]
              refine rel_of_setFl rfl ?_
              exact FlRel_fail_any _ h.fl
          | ok b =>
              simp only [hn, hm, Except.map, bind_ok, mapAddr_region]
              by_cases hreg : a.region = b.region
              · simp only [hreg, ite_true, ite_false, pure_ok, okOr_ok]
                refine rel_of_setFl
                  (s1 := (setFlags (setFl s1.flags (sh k s2)) (mapAddr k a).off (mapAddr k b).off).next)
                  (s2 := (setFlags s2 a.off b.off).next)
                  (fl := some ((mapAddr k a).off, (mapAddr k b).off)) ?_ ?_
                · rfl
                · exact FlRel_of_mapAddr rfl rfl hreg
              · simp only [hreg, ite_true, ite_false, throw_error, okOr_error, ← setFl_fail,
                  fail_sh]
                refine rel_of_setFl rfl ?_
                exact FlRel_fail_any _ h.fl

theorem exec_bcc_rel (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (c : CC) (t : Nat) (k : Int) {s1 s2 : CS} (h : Rel k s1 s2) :
    Rel k (exec ro (memSh k mem0) orc (.bcc c t) s1) (exec ro mem0 orc (.bcc c t) s2) := by
  by_cases hh : s2.halted = true
  · have hh1 : s1.halted = true := by rw [h.halted]; exact hh
    simp [exec, hh, hh1]
    exact h
  · rw [h.to_setFl]
    cases hfl : s2.flags with
    | none =>
        have hfl1 : s1.flags = none := flRel_none (hfl ▸ h.fl)
        have h' : FlRel k none none := by simpa [hfl1, hfl] using h.fl
        simp only [exec, hh, hfl1, hfl, sh_halted, setFl_halted, sh_flags, setFl_flags,
          ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, throw_error, okOr_error,
          ← setFl_fail, fail_sh]
        refine rel_of_setFl rfl ?_
        simpa [fail_flags, hfl] using h'
    | some p =>
        obtain ⟨a2, b2⟩ := p
        have hsome : FlRel k s1.flags (some (a2, b2)) := hfl ▸ h.fl
        obtain ⟨a1, b1, hfl1, hrel⟩ := flRel_some hsome
        simp only [exec, hh, hfl1, hfl, sh_halted, setFl_halted, sh_flags, setFl_flags,
          ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, okOr_ok]
        obtain ⟨b, hb2⟩ := decideC_some (ccCond c a2 b2)
        have hdec : (ccCond c a1 b1).decideC = (ccCond c a2 b2).decideC := by
          rcases hrel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact decideC_shift c a2 b2 k
        have hb1 : (ccCond c a1 b1).decideC = some b := by rw [hdec, hb2]
        have hbase : Rel k (setFl (some (a1, b1)) (sh k s2)) s2 :=
          rel_of_setFl (s2 := s2) (fl := some (a1, b1)) rfl (by rw [hfl]; exact hrel)
        have hL := branch_some (setFl (some (a1, b1)) (sh k s2)) orc (ccCond c a1 b1) t b hb1
        have hR := branch_some s2 orc (ccCond c a2 b2) t b hb2
        rw [hL, hR]
        split
        · exact hbase.setPc t
        · exact hbase.next

/-! ### Every canonical instruction -/

theorem canon_flagFree_or (i : Instr) (h : Canon i = true) :
    FlagFree i = true ∨ (∃ n m, i = .cmpr n m) ∨ (∃ c t, i = .bcc c t) := by
  cases i with
  | cmpr n m => exact Or.inr (Or.inl ⟨n, m, rfl⟩)
  | bcc c t => exact Or.inr (Or.inr ⟨c, t, rfl⟩)
  | ldp sz t1 t2 n idx =>
      cases sz <;> simp [Canon] at h
      all_goals first | exact Or.inl rfl | exact h.elim
  | stp sz t1 t2 n idx =>
      cases sz <;> simp [Canon] at h
      all_goals first | exact Or.inl rfl | exact h.elim
  | _ => simp_all [Canon, FlagFree]

theorem canon_of_get {prog : Array Instr} {pc : Nat} {i : Instr}
    (h : prog.all Canon = true) (hp : prog[pc]? = some i) : Canon i = true := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hp
  have hc := (Array.all_eq_true.mp h) pc hlt
  rwa [heq] at hc

theorem exec_rel (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (k : Int) (hro : ro ≠ rStack) (hk : k % 16 = 0)
    (hcanon : Canon i = true) {s1 s2 : CS} (h : Rel k s1 s2) :
    Rel k (exec ro (memSh k mem0) orc i s1) (exec ro mem0 orc i s2) := by
  rcases canon_flagFree_or i hcanon with hf | ⟨n, m, rfl⟩ | ⟨c, t, rfl⟩
  · exact exec_rel_ff ro mem0 orc i k hro hk hf h
  · exact exec_cmpr_rel ro mem0 orc n m k h
  · exact exec_bcc_rel ro mem0 orc c t k h

/-! ### Runs -/

theorem run_rel (prog : Array Instr) (ro : Region) (orc : Nat → Bool)
    (mem0 : Addr Int → Cell W32 Int) (k : Int) (hro : ro ≠ rStack) (hk : k % 16 = 0)
    (hcanon : prog.all Canon = true) :
    ∀ (n : Nat) {s1 s2 : CS}, Rel k s1 s2 →
      Rel k (run prog ro (memSh k mem0) orc n s1) (run prog ro mem0 orc n s2)
  | 0, s1, s2, h => h
  | n + 1, s1, s2, h => by
      by_cases hh : s2.halted = true
      · have hh1 : s1.halted = true := by rw [h.halted]; exact hh
        simp only [run, hh, hh1, ite_true]
        exact h
      · have hh1 : ¬ (s1.halted = true) := by rw [h.halted]; exact hh
        cases hf : prog[s2.pc]? with
        | none =>
            have hf1 : prog[s1.pc]? = none := by rw [h.pc]; exact hf
            simp only [run, hh, hh1, ite_false, hf, hf1]
            exact fail_rel h "pc out of program"
        | some i =>
            have hf1 : prog[s1.pc]? = some i := by rw [h.pc]; exact hf
            simp only [run, hh, hh1, ite_false, hf, hf1]
            exact run_rel prog ro orc mem0 k hro hk hcanon n
              (exec_rel ro mem0 orc i k hro hk (canon_of_get hcanon hf) h)

end Hashtree.Asm.ArmShift
