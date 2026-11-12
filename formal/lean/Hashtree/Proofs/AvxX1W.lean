import Hashtree.Gen.AvxX1LW.It0.Shape
import Hashtree.Gen.AvxX1LW.It.Shape
import Hashtree.Gen.AvxX1LW.T0a.Final
import Hashtree.Gen.AvxX1LW.T0b.Final
import Hashtree.Proofs.ShaniW

/-!
# `hashtree_sha256_avx_x1` at the call state of the Go wrapper, every count

As `Hashtree.Proofs.AvxX1L.correct`, from `X86SymW.entryW` (pointer-valued rbx/rbp/r12/r14,
integer-tagged r13/r15, rax = output, rcx = count, entry stack pointer `σ 9`).  The prologue pushes
the six callee-saved registers (pointer cells, `pushL`); a restarted segment sees them through the
older log (`PushOkW`), and the epilogue pops them back (the exit segments' decided register shape).
Footprint: output bytes and stack bytes in `[σ 9 - 200, σ 9)`.
-/

set_option maxRecDepth 10000

namespace Hashtree.Proofs.AvxX1W
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.AvxX1
open Hashtree.Asm.SpecQ Hashtree.Spec Hashtree.Gen.AvxX1LW
open Hashtree.Proofs.ShaniW (OutOk RegsOk RegShape regs_of OutLogW outLogW_ne tau_hi)

/-- Every logged write is an output byte in `[ob, ob + len)` or a stack byte in `[sp - 200, sp)`. -/
def InRange (sp ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ sp - 200 ≤ p.1.off ∧ p.1.off < sp)

/-- The prologue's pushes are visible at `σ 9 + k`. -/
def PushOkW (σ : Nat → Int) (M : CLog) : Prop :=
  ∀ q ∈ pushL, lookup (⟨rStack, σ 9 + q.1⟩ : Addr Int) M = .ok (some (mapCell (fun _ => 0) σ q.2))

/-- A pushed pointer cell whose address only uses symbols 5–12. -/
def pbOk : Cell E Lin → Bool
  | .pb a _ => (a.off.c.take 5).all (· == 0) && decide (a.off.c.length ≤ 13)
  | _ => false

theorem pushL_pb : ∀ q ∈ pushL, pbOk q.2 = true := by decide

theorem dotC_congr (σ σ' : Nat → Int) : ∀ (c : List Int) (i : Nat),
    (∀ j, j < c.length → c.getD j 0 = 0 ∨ σ (i + j) = σ' (i + j)) → dotC c i σ = dotC c i σ'
  | [], _, _ => rfl
  | x :: xs, i, h => by
    simp only [dotC]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    have ih := dotC_congr σ σ' xs (i + 1) (fun j hj => by
      have := h (j + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rw [show i + 1 + j = i + (j + 1) by omega]; exact this)
    rcases h0 with h0 | h0 <;> simp [h0, ih]

theorem pushL_cell (σ σ' : Nat → Int) (hs : ∀ i, 5 ≤ i → i ≤ 12 → σ' i = σ i) (e : Key → W32) :
    ∀ q ∈ pushL, mapCell e σ' q.2 = mapCell (fun _ => 0) σ q.2 := by
  intro q hq
  have h := pushL_pb q hq
  revert h
  cases q.2 with
  | dat _ _ => simp [pbOk]
  | pb a j =>
    intro h
    simp only [pbOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [mapCell, mapAddr, Lin.eval]
    congr 3
    apply dotC_congr σ' σ
    intro j hj
    by_cases hj5 : j < 5
    · left
      apply h1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
    · right; simp only [Nat.zero_add]; exact hs j (by omega) (by omega)

theorem outLog_of (sp ob : Int) (len : Nat) (M : CLog) (h : InRange sp ob len M) : OutLogW sp M := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

/-- The kernel's initial memory at a restart: the wrapper's, seen through the older log. -/
theorem wfP_view (env env' : Key → W32) (σ σ' : Nat → Int) (hs : ∀ i, 5 ≤ i → i ≤ 12 → σ' i = σ i)
    (m : Addr Int → Cell W32 Int) (M : CLog) (hM : OutLogW (σ 9) M) (hP : PushOkW σ M)
    (hw : WfMemW rodata [] env σ m) : WfMemW rodata pushL env' σ' (view M m) := by
  obtain ⟨hro, hret, hin, _⟩ := hw
  have h9 := hs 9 (by decide) (by decide)
  refine ⟨fun o => ?_, fun k h1 h2 => ?_, fun o => ?_, fun k c hl _ _ => ?_⟩
  · rw [view_other M m _ (outLogW_ne _ M hM _ ⟨show (4 : Region) ≠ rOut by decide,
      fun h => absurd (show (4 : Region) = rStack from h) (by decide)⟩)]
    exact hro o
  · rw [view_other M m _ (outLogW_ne _ M hM _ ⟨show rStack ≠ rOut by decide, fun _ => by simp only; omega⟩), h9]
    exact hret k h1 h2
  · rw [view_other M m _ (outLogW_ne _ M hM _ ⟨show rIn ≠ rOut by decide,
      fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
    exact hin o
  · have hm := plookup_mem k pushL c hl
    have hq := hP (k, c) hm
    simp only [view, h9, hq]
    exact (pushL_cell σ σ' hs env' (k, c) hm).symm

theorem fr_fr (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

theorem blk_shift (inp : Nat → Byte) (k : Nat) : blk (fun o => inp (64 * k + o)) 0 = blk inp k := by
  funext i; simp only [blk]; congr 1; omega

theorem hmem_k (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (k : Nat) (e : Key → W32) (σ' : Nat → Int) (h0 : σ' 0 = σ0 + 64 * k) (sp : Int) (M : CLog) (hM : OutLogW sp M) :
    HMem 128 (fun o => inp (64 * k + o)) (ecomb e σ' (view M mem0c)) := by
  intro o _
  simp only [ecomb]
  rw [view_other M mem0c _ (outLogW_ne sp M hM _ ⟨show rIn ≠ rOut by decide,
    fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
  have ha : (⟨rIn, (⟨(o : Int), [1]⟩ : Lin).eval σ'⟩ : Addr Int) = ⟨rIn, σ0 + ((64 * k + o : Nat) : Int)⟩ := by
    simp only [Lin.eval, dotC, Addr.mk.injEq, true_and]; omega
  rw [ha, hin]; rfl

theorem inRange_mono (sp ob : Int) (a b : Nat) (hab : a ≤ b) (M : CLog) (h : InRange sp ob a M) : InRange sp ob b M := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, h2, by omega⟩
  · exact Or.inr h

theorem inRange_app (sp ob : Int) (len : Nat) (L M : CLog) (hL : InRange sp ob len L) (hM : InRange sp ob len M) :
    InRange sp ob len (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- Mapped log of a segment's final cut: output bytes above `σ' 1`, stack bytes below the pushes. -/
theorem range_seg (e : Key → W32) (σ' : Nat → Int) (sp ob : Int) (k : Nat) (h9 : σ' 9 = sp) (hob : σ' 1 = ob + 32 * k)
    (K : State E Lin) (len : Nat)
    (hl : ∀ p ∈ K.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < len) ∨
      (p.1.region = rStack ∧ stackRel p.1.off = some p.1.off.k ∧ -200 ≤ p.1.off.k ∧ p.1.off.k < lo)) :
    InRange sp ob (32 * k + len) (K.mem.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) ∧
      ∀ p ∈ K.mem.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2)),
        (p.1.region ≠ rOut ∨ ob + 32 * (k : Int) ≤ p.1.off) ∧ (p.1.region ≠ rStack ∨ p.1.off < sp + lo) := by
  have hlo : lo = -48 := rfl
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
    · right
      have := stackRel_eval σ' q.1.off _ h2
      simp only [mapAddr, h1, this]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
      exact ⟨Or.inr (by omega), Or.inl (by decide)⟩
    · have := stackRel_eval σ' q.1.off _ h2
      simp only [mapAddr, h1, this]
      exact ⟨Or.inl (by decide), Or.inr (by omega)⟩

theorem outOk_new (inp : Nat → Byte) (ob : Int) (n0 nb : Nat) (L M : CLog) (σ1 : Int) (hσ1 : σ1 = ob + 32 * (n0 : Int))
    (hnew : ∀ n i b, n < nb → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) L = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp (n0 + n))).getD (4 * i + b) 0).zeroExtend 32)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off) (hM : OutOk inp ob n0 M) :
    OutOk inp ob (n0 + nb) (L ++ M) := by
  intro n i b hn hi hb
  by_cases h : n < n0
  · obtain ⟨x, hx, hv⟩ := hM n i b h hi hb
    refine ⟨x, ?_, hv⟩
    rw [lookup_app_right]
    · exact hx
    · intro p hp heq
      rcases hL p hp with h' | h'
      · rw [heq] at h'; exact h' rfl
      · rw [heq] at h'; simp only at h'; omega
  · obtain ⟨x, hx, hv⟩ := hnew (n - n0) i b (by omega) hi hb
    refine ⟨x, ?_, ?_⟩
    · apply lookup_app_left
      rw [show ob + ((32 * n + 4 * i + b : Nat) : Int) = σ1 + ((32 * (n - n0) + 4 * i + b : Nat) : Int) by omega]
      exact hx
    · rw [show n = n0 + (n - n0) by omega]; exact hv

theorem pushOk_app (σ : Nat → Int) (L M : CLog) (hL : ∀ p ∈ L, p.1.region ≠ rStack ∨ p.1.off < σ 9 + lo)
    (hM : PushOkW σ M) : PushOkW σ (L ++ M) := by
  intro q hq
  have hr := pushL_range q hq
  rw [lookup_app_right]
  · exact hM q hq
  · intro p hp heq
    rcases hL p hp with h | h
    · rw [heq] at h; exact h rfl
    · rw [heq] at h; simp only at h; omega

/-- One iteration from a loop-head cut `K0` (`KH0` or `KH1`) to `KH1` under shifted symbols. -/
theorem iter_step (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (env0 : Key → W32) (σ : Nat → Int)
    (hw : WfMemW rodata [] env0 σ mem0c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) (orcC : Nat → Bool)
    (K0 : State E Lin) (hK0 : K0.nOnly = true) (NSi : Nat) (KFi : State E Lin) (EFi : (Key → W32) → Key → W32)
    (hrun : ∀ env0 σ mem0c orcC, Mem0Rel env0 σ (mem0sW 4 rodata pushL) mem0c → 1 ≤ σ 2 →
      run prog 4 mem0c orcC NSi (mapState env0 σ K0) = mapState (EFi env0) σ KFi)
    (tau : List Lin) (hτ : tau.length = 5)
    (hinst : ∀ env0 σ, mapState (EFi env0) σ KFi = mapState (EFi env0) σ { KFi with gpr := (KH1.substL tau).gpr, vr := KH1.vr })
    (hshape : { ({ KFi with gpr := (KH1.substL tau).gpr, vr := KH1.vr } : State E Lin) with mem := [], assume := [] } = KH1.substL tau)
    (htau : ∀ σ : Nat → Int, sigmaOf tau σ 0 = σ 0 + 64 ∧ sigmaOf tau σ 1 = σ 1 + 32 ∧ sigmaOf tau σ 2 = σ 2 - 1)
    (hout : ∀ inp env0 σ, HMem 128 inp env0 → ∀ n i b, n < 1 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) (mapState (EFi env0) σ KFi).mem = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32)
    (hlog : ∀ p ∈ KFi.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 32) ∨
      (p.1.region = rStack ∧ stackRel p.1.off = some p.1.off.k ∧ -200 ≤ p.1.off.k ∧ p.1.off.k < lo))
    (k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog)
    (h0 : σ' 0 = σ 0 + 64 * k) (h1 : σ' 1 = σ 1 + 32 * k) (h2 : 1 ≤ σ' 2) (hs : ∀ i, 5 ≤ i → i ≤ 12 → σ' i = σ i)
    (hR : InRange (σ 9) (σ 1) (32 * k) M) (hO : OutOk inp (σ 1) k M) (hP : PushOkW σ M) :
    ∃ e' M', run prog 4 mem0c orcC NSi (fr M (mapState e σ' K0)) = fr M' (mapState e' (sigmaOf tau σ') KH1) ∧
      InRange (σ 9) (σ 1) (32 * (k + 1)) M' ∧ OutOk inp (σ 1) (k + 1) M' ∧ PushOkW σ M' ∧
      (∀ i, 5 ≤ i → i ≤ 12 → sigmaOf tau σ' i = σ i) := by
  have hM := outLog_of _ _ _ M hR
  let E := ecomb e σ' (view M mem0c)
  have hrel : Mem0Rel E σ' (mem0sW 4 rodata pushL) (view M mem0c) :=
    mem0RelW_of_wf rodata pushL E σ' _ (wfP_view env0 E σ σ' hs mem0c M hM hP hw) (envMem_ecomb _ _ _)
  rw [run_fr, mapState_nOnly e E σ' (fun _ => rfl) K0 hK0, hrun E σ' (view M mem0c) orcC hrel h2,
    hinst, mapState_reached (EFi E) σ' _ KH1 tau hshape, fr_fr]
  have hs9 := hs 9 (by decide) (by decide)
  have hsr := range_seg (EFi E) σ' (σ 9) (σ 1) k hs9 h1 KFi 32 hlog
  refine ⟨EFi E, _, rfl, ?_, ?_, ?_, fun i h5 h12 => (tau_hi tau hτ σ' i h5).trans (hs i h5 h12)⟩
  · apply inRange_app
    · exact hsr.1
    · exact inRange_mono _ _ _ _ (by omega) M hR
  · have hnew := hout (fun o => inp (64 * k + o)) E σ' (hmem_k inp mem0c (σ 0) hin k e σ' h0 (σ 9) M hM)
    exact outOk_new inp (σ 1) k 1 _ M (σ' 1) (by omega)
      (by
        intro n i b hn hi hb
        obtain ⟨x, hx, hv⟩ := hnew n i b hn hi hb
        refine ⟨x, hx, ?_⟩
        have hn0 : n = 0 := by omega
        subst hn0
        rw [hv, blk_shift, Nat.add_zero])
      (fun p hp => (hsr.2 p hp).1) hO
  · exact pushOk_app σ _ M (fun p hp => (hsr.2 p hp).2) hP

/-- An exit from a loop-head cut. -/
theorem exit_step (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (env0 : Key → W32) (σ : Nat → Int)
    (hw : WfMemW rodata [] env0 σ mem0c) (orcC : Nat → Bool)
    (K0 : State E Lin) (hK0 : K0.nOnly = true) (NSi : Nat) (KFi : State E Lin) (EFi : (Key → W32) → Key → W32)
    (hrun : ∀ env0 σ mem0c orcC, Mem0Rel env0 σ (mem0sW 4 rodata pushL) mem0c → σ 2 = 0 →
      run prog 4 mem0c orcC NSi (mapState env0 σ K0) = mapState (EFi env0) σ KFi)
    (hlog : ∀ p ∈ KFi.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 0) ∨
      (p.1.region = rStack ∧ stackRel p.1.off = some p.1.off.k ∧ -200 ≤ p.1.off.k ∧ p.1.off.k < lo))
    (hh : KFi.halted = true) (he : KFi.err = none) (ht : KFi.tail = none) (hreg : RegShape KFi)
    (k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog) (h1 : σ' 1 = σ 1 + 32 * k) (h2 : σ' 2 = 0)
    (hs : ∀ i, 5 ≤ i → i ≤ 12 → σ' i = σ i)
    (hR : InRange (σ 9) (σ 1) (32 * k) M) (hO : OutOk inp (σ 1) k M) (hP : PushOkW σ M) :
    let fin := run prog 4 mem0c orcC NSi (fr M (mapState e σ' K0))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ InRange (σ 9) (σ 1) (32 * k) fin.mem ∧
      OutOk inp (σ 1) k fin.mem ∧ RegsOk env0 σ fin := by
  have hM := outLog_of _ _ _ M hR
  let E := ecomb e σ' (view M mem0c)
  have hrel : Mem0Rel E σ' (mem0sW 4 rodata pushL) (view M mem0c) :=
    mem0RelW_of_wf rodata pushL E σ' _ (wfP_view env0 E σ σ' hs mem0c M hM hP hw) (envMem_ecomb _ _ _)
  intro fin
  have hfin : fin = fr M (mapState (EFi E) σ' KFi) := by
    show run prog 4 mem0c orcC NSi (fr M (mapState e σ' K0)) = _
    rw [run_fr, mapState_nOnly e E σ' (fun _ => rfl) K0 hK0, hrun E σ' (view M mem0c) orcC hrel h2]
  rw [hfin]
  have hsr := range_seg (EFi E) σ' (σ 9) (σ 1) k (hs 9 (by decide) (by decide)) h1 KFi 0 hlog
  refine ⟨hh, he, ht, ?_, ?_, regs_of _ env0 σ' σ KFi M hreg hs (fun id hid => by simp [keepIdsW] at hid)⟩
  · show InRange _ _ _ (_ ++ M)
    apply inRange_app
    · exact inRange_mono _ _ _ _ (by omega) _ hsr.1
    · exact hR
  · show OutOk inp _ _ (_ ++ M)
    have := outOk_new inp (σ 1) k 0 _ M (σ' 1) (by omega) (fun n _ _ hn => by omega)
      (fun p hp => (hsr.2 p hp).1) hO
    rw [Nat.add_zero] at this
    exact this

theorem It_tau (σ : Nat → Int) : sigmaOf It.tauE σ 0 = σ 0 + 64 ∧ sigmaOf It.tauE σ 1 = σ 1 + 32 ∧ sigmaOf It.tauE σ 2 = σ 2 - 1 := by
  simp only [sigmaOf, tauAt, It.tauE, List.getD_cons_succ, List.getD_cons_zero, Lin.eval, dotC, Nat.zero_add, Nat.reduceAdd]
  omega

theorem It0_tau (σ : Nat → Int) : sigmaOf It0.tauE σ 0 = σ 0 + 64 ∧ sigmaOf It0.tauE σ 1 = σ 1 + 32 ∧ sigmaOf It0.tauE σ 2 = σ 2 - 1 := by
  simp only [sigmaOf, tauAt, It0.tauE, List.getD_cons_succ, List.getD_cons_zero, Lin.eval, dotC, Nat.zero_add, Nat.reduceAdd]
  omega

theorem T0a_regs : RegShape T0a.KF := by decide
theorem T0b_regs : RegShape T0b.KF := by decide

theorem loop (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (env0 : Key → W32) (σ : Nat → Int)
    (hw : WfMemW rodata [] env0 σ mem0c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) (orcC : Nat → Bool) :
    ∀ (j k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog),
      σ' 0 = σ 0 + 64 * k → σ' 1 = σ 1 + 32 * k → σ' 2 = j → (∀ i, 5 ≤ i → i ≤ 12 → σ' i = σ i) →
      InRange (σ 9) (σ 1) (32 * k) M → OutOk inp (σ 1) k M → PushOkW σ M →
      let fin := run prog 4 mem0c orcC (j * It.NS + T0b.NS) (fr M (mapState e σ' KH1))
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        InRange (σ 9) (σ 1) (32 * (k + j)) fin.mem ∧ OutOk inp (σ 1) (k + j) fin.mem ∧ RegsOk env0 σ fin := by
  intro j
  induction j with
  | zero =>
    intro k σ' e M h0 h1 h2 hs hR hO hP
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    exact exit_step inp mem0c env0 σ hw orcC KH1 KH1_nOnly T0b.NS T0b.KF T0b.EF
      (fun env0 σ m o h hσ => T0b.run_final env0 σ m o h hσ) T0b.log_final T0b.KF_halted T0b.KF_err T0b.KF_tail
      T0b_regs k σ' e M h1 (by omega) hs hR hO hP
  | succ j ih =>
    intro k σ' e M h0 h1 h2 hs hR hO hP
    obtain ⟨e', M', hrun, hR', hO', hP', hs'⟩ := iter_step inp mem0c env0 σ hw hin orcC KH1 KH1_nOnly It.NS It.KF It.EF
      (fun env0 σ m o h hσ => It.run_final env0 σ m o h hσ) It.tauE rfl It.KF_inst It.KF_shape It_tau
      (fun inp env0 σ hm => It.out_final inp env0 σ hm) It.log_final k σ' e M h0 h1 (by omega) hs hR hO hP
    rw [show (j + 1) * It.NS + T0b.NS = It.NS + (j * It.NS + T0b.NS) by rw [Nat.succ_mul]; omega, run_add, hrun]
    have t := It_tau σ'
    have := ih (k + 1) (sigmaOf It.tauE σ') e' M' (by rw [t.1, h0]; omega) (by rw [t.2.1, h1]; omega)
      (by rw [t.2.2, h2]; omega) hs' hR' hO' hP'
    obtain ⟨a, b, c, d, f, g⟩ := this
    refine ⟨a, b, c, ?_, ?_, g⟩
    · rw [show k + (j + 1) = k + 1 + j by omega]; exact d
    · rw [show k + (j + 1) = k + 1 + j by omega]; exact f

/-- The instruction count of a call with `c` blocks. -/
def steps (c : Nat) : Nat := NP + (if c = 0 then T0a.NS else It0.NS + ((c - 1) * It.NS + T0b.NS))

/-- **avx_x1 at the wrapper's call state, every count.** -/
theorem correctW (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemW rodata [] env0 σ mem0c) (he : EnvMem env0 σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 9) (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧ RegsOk env0 σ fin := by
  have h0 : Mem0Rel env0 σ (mem0sW 4 rodata []) mem0c := mem0RelW_of_wf rodata [] env0 σ mem0c hw he
  have hPr := (slice_sound env0 σ (mem0sW 4 rodata []) mem0c h0 prog 4 (fun _ => false) orcC NP entryW KP []
    slicePro rfl (fun p hp => by rw [KP_assume] at hp; cases hp)).1
  let e0 := envAbs env0 (run prog 4 (mem0sW 4 rodata []) (fun _ => false) NP entryW)
  simp only [steps]
  rw [run_add, hPr, mapState_reached e0 σ KP KH0 tauP KP_inst]
  have hσ : ∀ i, sigmaOf tauP σ i = (tauP.getD i (Lin.sym i)).eval σ := fun _ => rfl
  have s0 : sigmaOf tauP σ 0 = σ 0 + 64 * 0 := by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym]
  have s1 : sigmaOf tauP σ 1 = σ 1 + 32 * 0 := by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym]
  have s2 : sigmaOf tauP σ 2 = c := by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym, hc]
  have sh : ∀ i, 5 ≤ i → i ≤ 12 → sigmaOf tauP σ i = σ i := by
    intro i h5 h12
    rcases (by omega : i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sigmaOf, tauAt, tauP, Lin.eval_sym]
  let Mp := KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))
  have hR : InRange (σ 9) (σ 1) (32 * 0) Mp := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := KP_log q hq
    right
    have := stackRel_eval σ q.1.off _ h2
    simp only [mapAddr, h1, this]
    refine ⟨trivial, ?_, ?_⟩ <;> simp only [lo] at h3 <;> omega
  have hO : OutOk inp (σ 1) 0 Mp := fun n _ _ hn => by omega
  have hP : PushOkW σ Mp := by
    intro q hq
    have hl := lookup_hom e0 σ _ KP.mem _ (lkIsW_sound _ _ _ (KP_push q hq))
    have ha : mapAddr σ (⟨rStack, sAt q.1⟩ : Addr Lin) = ⟨rStack, σ 9 + q.1⟩ := by
      simp only [mapAddr, stackRel_eval σ (sAt q.1) q.1 (by simp [stackRel, sAt, stkC, trimC])]
    rw [ha, Option.map_some, pushL_cell σ σ (fun _ _ _ => rfl) e0 q hq] at hl
    exact hl
  by_cases hc0 : c = 0
  · subst hc0
    simp only [ite_true]
    have := exit_step inp mem0c env0 σ hw orcC KH0 KH0_nOnly T0a.NS T0a.KF T0a.EF
      (fun env0 σ m o h hσ => T0a.run_final env0 σ m o h hσ) T0a.log_final T0a.KF_halted T0a.KF_err T0a.KF_tail
      T0a_regs 0 (sigmaOf tauP σ) e0 Mp s1 (by omega) sh hR hO hP
    simpa using this
  · simp only [hc0, ite_false]
    rw [run_add]
    obtain ⟨e', M', hrun, hR', hO', hP', hs'⟩ := iter_step inp mem0c env0 σ hw hin orcC KH0 KH0_nOnly It0.NS It0.KF It0.EF
      (fun env0 σ m o h hσ => It0.run_final env0 σ m o h hσ) It0.tauE rfl It0.KF_inst It0.KF_shape It0_tau
      (fun inp env0 σ hm => It0.out_final inp env0 σ hm) It0.log_final 0 (sigmaOf tauP σ) e0 Mp s0 s1 (by omega) sh hR hO hP
    rw [hrun]
    have t := It0_tau (sigmaOf tauP σ)
    have := loop inp mem0c env0 σ hw hin orcC (c - 1) 1 (sigmaOf It0.tauE (sigmaOf tauP σ)) e' M'
      (by rw [t.1, s0]; omega) (by rw [t.2.1, s1]; omega) (by rw [t.2.2, s2]; omega) hs' hR' hO' hP'
    obtain ⟨a, b, d, f, g, hreg⟩ := this
    refine ⟨a, b, d, ?_, ?_, hreg⟩
    · have hc1 : 32 * (1 + (c - 1)) = 32 * c := by omega
      rw [hc1] at f; exact f
    · have hc1 : 1 + (c - 1) = c := by omega
      rw [hc1] at g; exact g

end Hashtree.Proofs.AvxX1W
