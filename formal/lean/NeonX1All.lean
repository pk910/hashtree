import Hashtree.Gen.ArmNeonX1L.It0.Shape
import Hashtree.Gen.ArmNeonX1L.It.Shape
import Hashtree.Gen.ArmNeonX1L.T0a.Final
import Hashtree.Gen.ArmNeonX1L.T0b.Final
import Hashtree.Asm.X86Loop

/-!
# `hashtree_sha256_neon_x1` (shipped linux_arm64 object) is correct for every count

From the four checked segments — the prologue to the loop-head cut `KH0`, one iteration from `KH0`
to `KH1`, one iteration from `KH1` back to `KH1`, and the exits for count 0 and after the last
block — by induction on the iterations: started on any well-formed memory holding the input
bytes, the kernel returns (via `ret`) without a model error after `steps c` instructions; it wrote
only the `32 c` output bytes and bytes of its own spill area below the entry stack pointer; and
output byte `32 n + 4 i + b` is byte `4 i + b` of SHA-256 of block `n`.
-/

set_option maxRecDepth 10000

namespace Hashtree.Proofs.ArmNeon
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmSym Hashtree.Kernels.Arm.NeonX1
  Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Gen.ArmNeonX1L

/-- The first `nblk` output blocks (base `ob`) hold the SHA-256 bytes of the input blocks. -/
def OutOk (inp : Nat → Byte) (ob : Int) (nblk : Nat) (M : CLog) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

/-- Every logged write is an output byte in `[ob, ob + len)` or a byte of the spill area
`[lo, 0)` below the entry stack pointer. -/
def InRange (ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ lo ≤ p.1.off ∧ p.1.off < 0)

theorem outLog_of (ob : Int) (len : Nat) (M : CLog) (h : InRange ob len M) : OutLog 0 M := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

theorem inRange_shift (ob ob' : Int) (k len : Nat) (L : CLog) (h : InRange ob' len L)
    (hob : ob' = ob + 32 * k) : InRange ob (32 * k + len) L := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, by omega, by omega⟩
  · exact Or.inr h

/-- Output blocks below `ob` are not touched by a log above it. -/
theorem above_of (ob : Int) (len : Nat) (L : CLog) (h : InRange ob len L) :
    ∀ p ∈ L, p.1.region ≠ rOut ∨ ob ≤ p.1.off := by
  intro p hp
  rcases h p hp with ⟨_, h2, _⟩ | ⟨h1, _⟩
  · exact Or.inr h2
  · exact Or.inl (by rw [h1]; decide)

theorem fr_fr (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

theorem fr_nil (s : CState) : fr [] s = s := by
  simp only [fr, List.append_nil]

theorem blk_shift (inp : Nat → Byte) (k n : Nat) : blk (fun o => inp (64 * k + o)) n = blk inp (k + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-- The input bytes of iteration `k`, relative to its input pointer. -/
theorem hmem_k (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (k : Nat) (e : Key → W32) (σ' : Nat → Int) (h0 : σ' 0 = σ0 + 64 * k) (M : CLog)
    (hM : OutLog 0 M) :
    HMem 64 (fun o => inp (64 * k + o)) (ecomb e σ' (view M mem0c)) := by
  intro o _
  simp only [ecomb]
  rw [view_other M mem0c _ (outLog_ne 0 M hM _ ⟨show rIn ≠ rOut by decide,
    fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
  have ha : (⟨rIn, (⟨(o : Int), [1]⟩ : Lin).eval σ'⟩ : Addr Int) = ⟨rIn, σ0 + ((64 * k + o : Nat) : Int)⟩ := by
    simp only [Lin.eval, dotC, Addr.mk.injEq, true_and]
    omega
  rw [ha, hin]
  rfl

/-- The loop head denotes the same with the memory keys re-read from memory. -/
theorem head_ecomb0 (e : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int) :
    mapState e σ' KH0 = mapState (ecomb e σ' m) σ' KH0 :=
  mapState_nOnly _ _ σ' (fun _ => rfl) KH0 KH0_nOnly

theorem head_ecomb1 (e : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int) :
    mapState e σ' KH1 = mapState (ecomb e σ' m) σ' KH1 :=
  mapState_nOnly _ _ σ' (fun _ => rfl) KH1 KH1_nOnly

theorem T0a_mem : T0a.KF.mem = [] := by decide
theorem T0b_mem : T0b.KF.mem = [] := by decide

/-- The address of an output cell: symbol 5 (the output pointer) plus a constant. -/
theorem mapAddr_out5 (σ' : Nat → Int) (a : Addr Lin) (h : a.off.c = [0, 0, 0, 0, 0, 1]) :
    (mapAddr σ' a).off = σ' 5 + a.off.k := by
  simp only [mapAddr, Lin.eval, h, dotC, Nat.zero_add, Nat.reduceAdd, Int.zero_mul,
    Int.one_mul, Int.zero_add, Int.add_zero]
  omega

/-- The address of a stack cell: a constant. -/
theorem mapAddr_stk (σ' : Nat → Int) (a : Addr Lin) (h : a.off.c = []) :
    (mapAddr σ' a).off = a.off.k := by
  simp only [mapAddr, Lin.eval, h, dotC]
  omega

/-- Mapped log entries of a segment's final cut: output bytes at `[σ' 5, σ' 5 + len)`. -/
theorem range_seg (e : Key → W32) (σ' : Nat → Int) (K : State E Lin) (len : Nat)
    (hl : ∀ p ∈ K.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 0, 0, 0, 0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < len) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ lo ≤ p.1.off.k ∧ p.1.off.k < 0)) :
    InRange (σ' 5) len (K.mem.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    rw [mapAddr_out5 σ' q.1 h2]
    exact ⟨h1, by omega, by omega⟩
  · right
    rw [mapAddr_stk σ' q.1 h2]
    exact ⟨h1, h3, h4⟩

theorem inRange_mono (ob : Int) (a b : Nat) (hab : a ≤ b) (M : CLog) (h : InRange ob a M) :
    InRange ob b M := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, h2, by omega⟩
  · exact Or.inr h

theorem inRange_app (ob : Int) (len : Nat) (L M : CLog) (hL : InRange ob len L)
    (hM : InRange ob len M) : InRange ob len (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- A cell found in the newer log is found in the appended log. -/
theorem lookup_app_left (a : Addr Int) (L M : CLog) (c : Cell W32 Int)
    (h : lookup a L = .ok (some c)) : lookup a (L ++ M) = .ok (some c) := by
  rw [lookup_append, h]

/-- An address not written by the newer log reads from the older log. -/
theorem lookup_app_right (a : Addr Int) (L M : CLog) (h : ∀ p ∈ L, p.1 ≠ a) :
    lookup a (L ++ M) = lookup a M := by
  rw [lookup_append, lookup_none_ne a L h]

/-- Output blocks below `lo` are not touched by a log above it. -/
theorem outOk_app (inp : Nat → Byte) (ob : Int) (n0 : Nat) (L M : CLog)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off)
    (hM : OutOk inp ob n0 M) :
    ∀ n i b, n < n0 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) (L ++ M) = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by
  intro n i b hn hi hb
  rw [lookup_app_right]
  · exact hM n i b hn hi hb
  · intro p hp heq
    rcases hL p hp with h | h
    · rw [heq] at h; exact h rfl
    · rw [heq] at h; simp only at h; omega

/-- The segment's new blocks, at block offset `n0`. -/
theorem outOk_new (inp : Nat → Byte) (ob : Int) (n0 nb : Nat) (L M : CLog) (σ1 : Int)
    (hσ1 : σ1 = ob + 32 * (n0 : Int))
    (hnew : ∀ n i b, n < nb → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) L = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp (n0 + n))).getD (4 * i + b) 0).zeroExtend 32)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off)
    (hM : OutOk inp ob n0 M) :
    OutOk inp ob (n0 + nb) (L ++ M) := by
  intro n i b hn hi hb
  by_cases h : n < n0
  · exact outOk_app inp ob n0 L M hL hM n i b h hi hb
  · obtain ⟨x, hx, hv⟩ := hnew (n - n0) i b (by omega) hi hb
    refine ⟨x, ?_, ?_⟩
    · apply lookup_app_left
      rw [show ob + ((32 * n + 4 * i + b : Nat) : Int) = σ1 + ((32 * (n - n0) + 4 * i + b : Nat) : Int) by omega]
      exact hx
    · rw [show n = n0 + (n - n0) by omega]; exact hv

/-! ## Logs of several parts -/

theorem view_append (L M : CLog) (m : Addr Int → Cell W32 Int) :
    view (L ++ M) m = view L (view M m) := by
  funext a
  obtain ⟨r, hr⟩ := lookup_conc_ok a L
  obtain ⟨r', hr'⟩ := lookup_conc_ok a M
  simp only [view, lookup_append, hr, hr']
  cases r with
  | none =>
    cases r' with
    | none => rfl
    | some c => rfl
  | some c => rfl

/-- An output-only log keeps a readable spill area readable. -/
theorem wfH_view_log (m : Addr Int → Cell W32 Int) (P : CLog)
    (hP : ∀ p ∈ P, p.1.region = rOut) (hw : WfMemH 7 rodata 0 lo m) :
    WfMemH 7 rodata 0 lo (view P m) := by
  refine ⟨wf_view 7 rodata 0 m P (fun p hp => Or.inl (hP p hp)) (by decide) hw.1, ?_⟩
  intro o h1 h2
  have hne : ∀ q ∈ P, q.1 ≠ (⟨rStack, o⟩ : Addr Int) := by
    intro q hq heq
    have h := hP q hq
    rw [heq] at h
    have h' : rStack ≠ rOut := by decide
    exact h' h
  have hne2 : ∀ q ∈ P, q.1 ≠ (⟨rStack, laneBase o⟩ : Addr Int) := by
    intro q hq heq
    have h := hP q hq
    rw [heq] at h
    have h' : rStack ≠ rOut := by decide
    exact h' h
  rw [view_other P m _ hne, view_other P m _ hne2]
  exact hw.2 o h1 h2

/-- A log of output cells only, mapped, is output only. -/
theorem outOnly_map (e : Key → W32) (σ : Nat → Int) (K : State E Lin)
    (h : K.mem.all (fun p => decide (p.1.region = rOut)) = true) :
    ∀ p ∈ (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))), p.1.region = rOut := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [List.all_eq_true] at h
  simpa only [mapAddr] using of_decide_eq_true (h q hq)

/-- The prologue's spill log is a readable spill area. -/
theorem wfH_pro (mem0c : Addr Int → Cell W32 Int) (env0 : Key → W32) (σ : Nat → Int)
    (hw : WfMem 7 rodata mem0c) :
    WfMemH 7 rodata 0 lo
      (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 KPrun) σ p.2))) mem0c) := by
  have hout : OutLog 0 (KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 KPrun) σ p.2))) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := KP_log q hq
    refine Or.inr ⟨?_, ?_⟩
    · simpa only [mapAddr] using h1
    · rw [mapAddr_stk σ q.1 h2]; exact h4
  refine ⟨wf_view 7 rodata 0 mem0c _ hout (by decide) hw, ?_⟩
  intro o h1 h2
  obtain ⟨x, hx, hy⟩ := pushOk_abstract env0 σ KPrun 0 lo KP_cutOk KP_push o h1 h2
  have hm : KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 KPrun) σ p.2))
      = (abstract KPrun).mem.map
          (fun p => (mapAddr σ p.1, mapCell (envAbs env0 KPrun) σ p.2)) := by
    rw [KP_abs]
  rw [hm]
  simp only [view, hx, hy, cellX]

/-- The prologue's log is inside the spill area. -/
theorem inRange_pro (e : Key → W32) (σ : Nat → Int) :
    InRange (σ 1) 0 (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨h1, h2, h3, h4⟩ := KP_log q hq
  refine Or.inr ⟨?_, ?_, ?_⟩
  · simpa only [mapAddr] using h1
  · rw [mapAddr_stk σ q.1 h2]; exact h3
  · rw [mapAddr_stk σ q.1 h2]; exact h4

/-- The instruction count of a call with `c` blocks. -/
def steps (c : Nat) : Nat := NP + (if c = 0 then T0a.NS else It0.NS + ((c - 1) * It.NS + T0b.NS))

/-- The iterations, then the exit, from a loop-head cut. -/
theorem loop (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 σ1 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) (orcC : Nat → Bool) :
    ∀ (j k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog),
      σ' 0 = σ0 + 64 * k → σ' 5 = σ1 + 32 * k → σ' 6 = σ1 + 32 * (k + j) →
      InRange σ1 (32 * k) M → OutOk inp σ1 k M → WfMemH 7 rodata 0 lo (view M mem0c) →
      let fin := Arm.run prog 7 mem0c orcC (j * It.NS + T0b.NS) (fr M (mapState e σ' KH1))
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        InRange σ1 (32 * k + 32 * j) fin.mem ∧ OutOk inp σ1 (k + j) fin.mem := by
  intro j
  induction j with
  | zero =>
    intro k σ' e M h0 h5 h6 hR hO hwM
    have hM := outLog_of _ _ M hR
    let E := ecomb e σ' (view M mem0c)
    have hrel : Mem0Rel E σ' (mem0sH 7 rodata 0 lo) (view M mem0c) :=
      mem0RelH_of_wf 7 rodata 0 lo E σ' _ hwM (envMem_ecomb _ _ _)
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    rw [run_fr, head_ecomb1 e σ' (view M mem0c)]
    rw [T0b.run_final E σ' (view M mem0c) orcC hrel (by omega)]
    refine ⟨T0b.KF_halted, T0b.KF_err, T0b.KF_tail, ?_, ?_⟩
    · show InRange σ1 (32 * k) (_ ++ M)
      simp only [mapState]
      rw [T0b_mem, List.map_nil, List.nil_append]
      exact hR
    · show OutOk inp σ1 k (_ ++ M)
      simp only [mapState]
      rw [T0b_mem, List.map_nil, List.nil_append]
      exact hO
  | succ j ih =>
    intro k σ' e M h0 h5 h6 hR hO hwM
    have hM := outLog_of _ _ M hR
    let E := ecomb e σ' (view M mem0c)
    have hrel : Mem0Rel E σ' (mem0sH 7 rodata 0 lo) (view M mem0c) :=
      mem0RelH_of_wf 7 rodata 0 lo E σ' _ hwM (envMem_ecomb _ _ _)
    rw [show (j + 1) * It.NS + T0b.NS = It.NS + (j * It.NS + T0b.NS) by rw [Nat.succ_mul]; omega,
      ArmSlice.run_add]
    rw [run_fr, head_ecomb1 e σ' (view M mem0c),
      It.run_final E σ' (view M mem0c) orcC hrel (by omega)]
    have hvr := It.KF_inst E σ'
    rw [hvr, mapState_reached (It.EF E) σ' _ KH1 It.tauE It.KF_shape, fr_fr]
    have hσ : ∀ i, sigmaOf It.tauE σ' i = (It.tauE.getD i (Lin.sym i)).eval σ' := fun _ => rfl
    have hL := range_seg (It.EF E) σ' It.KF 32 It.log_final
    have hnew := It.out_final (fun o => inp (64 * k + o)) E σ' (view M mem0c) orcC hrel
      (by omega) (hmem_k inp mem0c σ0 hin k e σ' h0 M hM)
    rw [It.run_final E σ' (view M mem0c) orcC hrel (by omega)] at hnew
    simp only [mapState] at hnew
    have := ih (k + 1) (sigmaOf It.tauE σ') (It.EF E)
      (It.KF.mem.map (fun p => (mapAddr σ' p.1, mapCell (It.EF E) σ' p.2)) ++ M)
      (by rw [hσ]; simp [It.tauE, Lin.eval, dotC]; omega)
      (by rw [hσ]; simp [It.tauE, Lin.eval, dotC]; omega)
      (by rw [hσ]; simp [It.tauE, Lin.eval, dotC]; omega)
      (by
        apply inRange_app
        · exact inRange_mono _ _ _ (by omega) _ (inRange_shift σ1 (σ' 5) k 32 _ hL h5)
        · exact inRange_mono _ _ _ (by omega) M hR)
      (by
        refine outOk_new inp σ1 k 1 _ M (σ' 5) h5 ?_ ?_ hO
        · intro n i b hn hi hb
          obtain ⟨x, hx, hv⟩ := hnew n i b hn hi hb
          refine ⟨x, hx, ?_⟩
          rw [hv, blk_shift]
        · intro p hp
          rcases above_of _ _ _ hL p hp with h | h
          · exact Or.inl h
          · exact Or.inr (by omega))
      (by
        rw [view_append]
        exact wfH_view_log (view M mem0c) _ (outOnly_map (It.EF E) σ' It.KF It.KF_onlyOut) hwM)
    obtain ⟨a, b, c, d, f⟩ := this
    refine ⟨a, b, c, ?_, ?_⟩
    · rw [show 32 * k + 32 * (j + 1) = 32 * (k + 1) + 32 * j by omega]; exact d
    · rw [show k + (j + 1) = k + 1 + j by omega]; exact f

theorem neon_x1_correct (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 7 rodata mem0c) (he : EnvMem env0 σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := Arm.run prog 7 mem0c orcC (steps c) (mapState env0 σ (entryS 0))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem := by
  have h0 : Mem0Rel env0 σ (mem0s 7 rodata) mem0c := mem0Rel_of_wf 7 rodata env0 σ mem0c hw he
  have hP := (ArmSlice.slice_sound env0 σ (mem0s 7 rodata) mem0c h0 prog 7 (fun _ => false) orcC NP
    (entryS 0) KP [] slicePro rfl (fun p hp => by rw [KP_assume] at hp; cases hp)).1
  simp only [steps]
  let e0 := envAbs env0 (run prog 7 (mem0s 7 rodata) (fun _ => false) NP (entryS 0))
  rw [ArmSlice.run_add, hP, mapState_reached e0 σ KP KH0 tauP KP_inst]
  have hσ : ∀ i, sigmaOf tauP σ i = (tauP.getD i (Lin.sym i)).eval σ := fun _ => rfl
  have h0P : sigmaOf tauP σ 0 = σ 0 := by
    rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym] <;> omega
  have h5P : sigmaOf tauP σ 5 = σ 1 := by
    rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym] <;> omega
  have h6P : sigmaOf tauP σ 6 = σ 1 + 32 * (c : Int) := by
    rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym, hc] <;> omega
  have hwPro : WfMemH 7 rodata 0 lo
      (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c) := wfH_pro mem0c env0 σ hw
  have hL0 := inRange_pro e0 σ
  have hML0 := outLog_of _ _ _ hL0
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0
    simp only [if_true]
    rw [run_fr, head_ecomb0 e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c)]
    rw [T0a.run_final (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c))
      (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c) orcC
      (mem0RelH_of_wf 7 rodata 0 lo _ (sigmaOf tauP σ) _ hwPro (envMem_ecomb _ _ _))
      (by rw [h6P, h5P]; omega)]
    refine ⟨T0a.KF_halted, T0a.KF_err, T0a.KF_tail, ?_, ?_⟩
    · show InRange (σ 1) (32 * 0) (_ ++ _)
      simp only [mapState]
      rw [T0a_mem, List.map_nil, List.nil_append]
      exact inRange_mono _ _ _ (by omega) _ hL0
    · show OutOk inp (σ 1) 0 (_ ++ _)
      simp only [mapState]
      rw [T0a_mem, List.map_nil, List.nil_append]
      exact fun n i b hn => absurd hn (by omega)
  · simp only [if_neg (Nat.pos_iff_ne_zero.mp hcpos)]
    rw [ArmSlice.run_add]
    rw [run_fr, head_ecomb0 e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c)]
    rw [It0.run_final (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c))
      (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c) orcC
      (mem0RelH_of_wf 7 rodata 0 lo _ (sigmaOf tauP σ) _ hwPro (envMem_ecomb _ _ _))
      (by rw [h6P, h5P]; omega)]
    rw [It0.KF_inst (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c))
      (sigmaOf tauP σ),
      mapState_reached (It0.EF (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c)))
        (sigmaOf tauP σ) _ KH1 It0.tauE It0.KF_shape, fr_fr]
    have hσI : ∀ i, sigmaOf It0.tauE (sigmaOf tauP σ) i
        = (It0.tauE.getD i (Lin.sym i)).eval (sigmaOf tauP σ) := fun _ => rfl
    have hl := loop inp mem0c (σ 0) (σ 1) hin orcC (c - 1) 1
      (sigmaOf It0.tauE (sigmaOf tauP σ))
      (It0.EF (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c)))
      (It0.KF.mem.map (fun p => (mapAddr (sigmaOf tauP σ) p.1,
        mapCell (It0.EF (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c))) (sigmaOf tauP σ) p.2))
        ++ KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2)))
      (by
        rw [hσI]; simp [It0.tauE, Lin.eval, dotC]; omega)
      (by
        rw [hσI]; simp [It0.tauE, Lin.eval, dotC]; omega)
      (by
        rw [hσI]; simp [It0.tauE, Lin.eval, dotC]; omega)
      (by
        refine inRange_app _ _ _ _ ?_ (inRange_mono _ _ _ (by omega) _ hL0)
        have hL1 := range_seg (It0.EF (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c)))
          (sigmaOf tauP σ) It0.KF 32 It0.log_final
        rw [h5P] at hL1
        exact inRange_mono (σ 1) 32 (32 * 1) (by omega) _ hL1)
      (by
        refine outOk_new inp (σ 1) 0 1 _ _ (sigmaOf tauP σ 5) (by omega) ?_ ?_
          (fun n i b hn => absurd hn (by omega))
        · intro n i b hn hi hb
          obtain ⟨x, hx, hv⟩ := It0.out_final (fun o => inp (64 * 0 + o))
            (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c))
            (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c) orcC
            (mem0RelH_of_wf 7 rodata 0 lo _ (sigmaOf tauP σ) _ hwPro (envMem_ecomb _ _ _))
            (by rw [h6P, h5P]; omega)
            (hmem_k inp mem0c (σ 0) hin 0 e0 (sigmaOf tauP σ) (by rw [h0P]; omega) _ hML0) n i b hn hi hb
          rw [It0.run_final (ecomb e0 (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c))
            (sigmaOf tauP σ) (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c) orcC
            (mem0RelH_of_wf 7 rodata 0 lo _ (sigmaOf tauP σ) _ hwPro (envMem_ecomb _ _ _))
            (by rw [h6P, h5P]; omega)] at hx
          simp only [mapState] at hx
          refine ⟨x, hx, ?_⟩
          rw [hv, blk_shift]
        · intro p hp
          rcases above_of _ _ _ (range_seg (It0.EF _) (sigmaOf tauP σ) It0.KF 32 It0.log_final) p hp with h | h
          · exact Or.inl h
          · exact Or.inr (by omega))
      (by
        rw [view_append]
        exact wfH_view_log (view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) mem0c) _
          (outOnly_map _ (sigmaOf tauP σ) It0.KF It0.KF_onlyOut) hwPro)
    obtain ⟨a, b, d, f, g⟩ := hl
    refine ⟨a, b, d, ?_, ?_⟩
    · exact inRange_mono (σ 1) (32 * 1 + 32 * (c - 1)) (32 * c) (by omega) _ f
    · simpa only [show 1 + (c - 1) = c by omega] using g

/-- The hypotheses are satisfiable for every input and count. -/
theorem neon_x1_hyps_sat (inp : Nat → Byte) (env : Key → W32) (σ : Nat → Int) (c : Nat)
    (hc : σ 2 = c) :
    let m := cmem 7 rodata (fun x => (inp (x - σ 0).toNat).zeroExtend 32)
    WfMem 7 rodata m ∧ EnvMem (ecomb env σ m) σ m ∧ σ 2 = c ∧
      ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
  refine ⟨cmem_wf 7 rodata _ (by decide) (by decide), envMem_ecomb _ _ _, hc, ?_⟩
  intro o
  simp only [cmem, rIn, rStack]
  simp only [show (1 : Region) ≠ 7 from by decide, show (1 : Region) ≠ 3 from by decide, ite_false, ite_true]
  congr 3
  omega

end Hashtree.Proofs.ArmNeon
