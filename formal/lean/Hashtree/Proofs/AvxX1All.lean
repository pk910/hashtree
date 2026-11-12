import Hashtree.Gen.AvxX1L.It0.Shape
import Hashtree.Gen.AvxX1L.It.Shape
import Hashtree.Gen.AvxX1L.T0a.Final
import Hashtree.Gen.AvxX1L.T0b.Final

/-!
# `hashtree_sha256_avx_x1` (shipped linux_amd64 object) is correct for every count

Segments: the prologue to the first loop-head cut `KH0` (its pushes become part of the older log),
the first block-iteration `KH0 → KH1` (the body sets a register to a constant rodata pointer), the
block-iteration `KH1 → KH1` (pointers +64 / +32, count −1), and the exits from `KH0` (count 0) and
`KH1`.  The epilogue pops the saved registers from the prologue's pushes (`mem0sH`, `PushOk`).
Glued by induction: started on any well-formed memory holding the input, the kernel returns via
`ret` without a model error after `steps c` instructions, writes only the `32 c` output bytes and
bytes of its stack frame, and output byte `32 n + j` is byte `j` of SHA-256 of block `n`.
-/

set_option maxRecDepth 10000

namespace Hashtree.Proofs.AvxX1L
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Gen.AvxX1L

/-- The first `nblk` output blocks (base `ob`) hold the SHA-256 bytes of the input blocks. -/
def OutOk (inp : Nat → Byte) (ob : Int) (nblk : Nat) (M : CLog) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

/-- Every logged write is an output byte in `[ob, ob + len)` or a stack byte in the 224 bytes below
the entry stack pointer (offset 24; the return address at 24..31 is never written). -/
def InRange (ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ -200 ≤ p.1.off ∧ p.1.off < 24)

/-- The prologue's pushes are visible. -/
def PushOk (M : CLog) : Prop :=
  ∀ o, lo ≤ o → o < 24 → ∃ x, lookup (⟨rStack, o⟩ : Addr Int) M = .ok (some (.dat x (o % 4).toNat))

theorem outLog_of (ob : Int) (len : Nat) (M : CLog) (h : InRange ob len M) : OutLog M := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

theorem fr_fr (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

theorem blk_shift (inp : Nat → Byte) (k : Nat) : blk (fun o => inp (64 * k + o)) 0 = blk inp k := by
  funext i
  simp only [blk]
  congr 1
  omega

theorem hmem_k (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (k : Nat) (e : Key → W32) (σ' : Nat → Int) (h0 : σ' 0 = σ0 + 64 * k) (M : CLog) (hM : OutLog M) :
    HMem 128 (fun o => inp (64 * k + o)) (ecomb e σ' (view M mem0c)) := by
  intro o _
  simp only [ecomb]
  rw [view_other M mem0c _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
    fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
  have ha : (⟨rIn, (⟨(o : Int), [1]⟩ : Lin).eval σ'⟩ : Addr Int) = ⟨rIn, σ0 + ((64 * k + o : Nat) : Int)⟩ := by
    simp only [Lin.eval, dotC, Addr.mk.injEq, true_and]
    omega
  rw [ha, hin]
  rfl

theorem inRange_mono (ob : Int) (a b : Nat) (hab : a ≤ b) (M : CLog) (h : InRange ob a M) : InRange ob b M := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, h2, by omega⟩
  · exact Or.inr h

theorem inRange_app (ob : Int) (len : Nat) (L M : CLog) (hL : InRange ob len L) (hM : InRange ob len M) :
    InRange ob len (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- Mapped log of a segment's final cut. -/
theorem range_seg (e : Key → W32) (σ' : Nat → Int) (ob : Int) (k : Nat) (hob : σ' 1 = ob + 32 * k)
    (K : State E Lin) (len : Nat) (lo' : Int) (hlo : lo' ≤ 24)
    (hl : ∀ p ∈ K.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < len) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -200 ≤ p.1.off.k ∧ p.1.off.k < lo')) :
    InRange ob (32 * k + len) (K.mem.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) ∧
      ∀ p ∈ K.mem.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2)),
        (p.1.region ≠ rOut ∨ ob + 32 * (k : Int) ≤ p.1.off) ∧ (p.1.region ≠ rStack ∨ p.1.off < lo') := by
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
    · right
      simp only [mapAddr, Lin.eval, h2, dotC, h1]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
      exact ⟨Or.inr (by omega), Or.inl (by decide)⟩
    · simp only [mapAddr, Lin.eval, h2, dotC, h1]
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

theorem pushOk_app (L M : CLog) (hL : ∀ p ∈ L, p.1.region ≠ rStack ∨ p.1.off < lo) (hM : PushOk M) :
    PushOk (L ++ M) := by
  intro o h1 h2
  rw [lookup_app_right]
  · exact hM o h1 h2
  · intro p hp heq
    rcases hL p hp with h | h
    · rw [heq] at h; exact h rfl
    · rw [heq] at h; simp only at h; omega

/-- One iteration from a loop-head cut `K0` (`KH0` or `KH1`) to `KH1` under shifted symbols. -/
theorem iter_step (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (hw : WfMem 4 rodata 24 mem0c)
    (σ0 σ1 : Int) (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) (orcC : Nat → Bool)
    (K0 : State E Lin) (hK0 : K0.nOnly = true) (NSi : Nat) (KFi : State E Lin) (EFi : (Key → W32) → Key → W32)
    (memT : Addr Lin → Cell E Lin) (hmemT : memT = mem0sH 4 rodata 24 lo)
    (hrun : ∀ env0 σ mem0c orcC, Mem0Rel env0 σ memT mem0c → 1 ≤ σ 2 →
      run prog 4 mem0c orcC NSi (mapState env0 σ K0) = mapState (EFi env0) σ KFi)
    (tau : List Lin)
    (hinst : ∀ env0 σ, mapState (EFi env0) σ KFi = mapState (EFi env0) σ { KFi with gpr := (KH1.substL tau).gpr, vr := KH1.vr })
    (hshape : { ({ KFi with gpr := (KH1.substL tau).gpr, vr := KH1.vr } : State E Lin) with mem := [], assume := [] } = KH1.substL tau)
    (htau : ∀ σ : Nat → Int, sigmaOf tau σ 0 = σ 0 + 64 ∧ sigmaOf tau σ 1 = σ 1 + 32 ∧ sigmaOf tau σ 2 = σ 2 - 1)
    (hout : ∀ inp env0 σ, HMem 128 inp env0 → ∀ n i b, n < 1 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) (mapState (EFi env0) σ KFi).mem = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32)
    (hlog : ∀ p ∈ KFi.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 32) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -200 ≤ p.1.off.k ∧ p.1.off.k < lo))
    (k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog)
    (h0 : σ' 0 = σ0 + 64 * k) (h1 : σ' 1 = σ1 + 32 * k) (h2 : 1 ≤ σ' 2)
    (hR : InRange σ1 (32 * k) M) (hO : OutOk inp σ1 k M) (hP : PushOk M) :
    ∃ e' M', run prog 4 mem0c orcC NSi (fr M (mapState e σ' K0)) = fr M' (mapState e' (sigmaOf tau σ') KH1) ∧
      InRange σ1 (32 * (k + 1)) M' ∧ OutOk inp σ1 (k + 1) M' ∧ PushOk M' := by
  have hM := outLog_of _ _ M hR
  let E := ecomb e σ' (view M mem0c)
  have hrel : Mem0Rel E σ' (mem0sH 4 rodata 24 lo) (view M mem0c) :=
    mem0RelH_of_wf rodata lo E σ' _ (wfH_view rodata lo mem0c M hM hw hP) (envMem_ecomb _ _ _)
  rw [run_fr, mapState_nOnly e E σ' (fun _ => rfl) K0 hK0, hrun E σ' (view M mem0c) orcC (hmemT ▸ hrel) h2,
    hinst, mapState_reached (EFi E) σ' _ KH1 tau hshape, fr_fr]
  have hs := range_seg (EFi E) σ' σ1 k h1 KFi 32 lo (by decide) hlog
  refine ⟨EFi E, _, rfl, ?_, ?_, ?_⟩
  · apply inRange_app
    · exact hs.1
    · exact inRange_mono _ _ _ (by omega) M hR
  · have hnew := hout (fun o => inp (64 * k + o)) E σ' (hmem_k inp mem0c σ0 hin k e σ' h0 M hM)
    exact outOk_new inp σ1 k 1 _ M (σ' 1) (by omega)
      (by
        intro n i b hn hi hb
        obtain ⟨x, hx, hv⟩ := hnew n i b hn hi hb
        refine ⟨x, hx, ?_⟩
        have hn0 : n = 0 := by omega
        subst hn0
        rw [hv, blk_shift, Nat.add_zero])
      (fun p hp => (hs.2 p hp).1) hO
  · exact pushOk_app _ M (fun p hp => (hs.2 p hp).2) hP

/-- An exit from a loop-head cut. -/
theorem exit_step (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (hw : WfMem 4 rodata 24 mem0c) (σ1 : Int) (orcC : Nat → Bool)
    (K0 : State E Lin) (hK0 : K0.nOnly = true) (NSi : Nat) (KFi : State E Lin) (EFi : (Key → W32) → Key → W32)
    (memT : Addr Lin → Cell E Lin) (hmemT : memT = mem0sH 4 rodata 24 lo)
    (hrun : ∀ env0 σ mem0c orcC, Mem0Rel env0 σ memT mem0c → σ 2 = 0 →
      run prog 4 mem0c orcC NSi (mapState env0 σ K0) = mapState (EFi env0) σ KFi)
    (hlog : ∀ p ∈ KFi.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 0) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -200 ≤ p.1.off.k ∧ p.1.off.k < lo))
    (hh : KFi.halted = true) (he : KFi.err = none) (ht : KFi.tail = none)
    (k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog) (h1 : σ' 1 = σ1 + 32 * k) (h2 : σ' 2 = 0)
    (hR : InRange σ1 (32 * k) M) (hO : OutOk inp σ1 k M) (hP : PushOk M) :
    let fin := run prog 4 mem0c orcC NSi (fr M (mapState e σ' K0))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ InRange σ1 (32 * k) fin.mem ∧ OutOk inp σ1 k fin.mem := by
  have hM := outLog_of _ _ M hR
  let E := ecomb e σ' (view M mem0c)
  have hrel : Mem0Rel E σ' (mem0sH 4 rodata 24 lo) (view M mem0c) :=
    mem0RelH_of_wf rodata lo E σ' _ (wfH_view rodata lo mem0c M hM hw hP) (envMem_ecomb _ _ _)
  intro fin
  have hfin : fin = fr M (mapState (EFi E) σ' KFi) := by
    show run prog 4 mem0c orcC NSi (fr M (mapState e σ' K0)) = _
    rw [run_fr, mapState_nOnly e E σ' (fun _ => rfl) K0 hK0, hrun E σ' (view M mem0c) orcC (hmemT ▸ hrel) h2]
  rw [hfin]
  have hs := range_seg (EFi E) σ' σ1 k h1 KFi 0 lo (by decide) hlog
  refine ⟨hh, he, ht, ?_, ?_⟩
  · show InRange σ1 _ (_ ++ M)
    apply inRange_app
    · exact inRange_mono _ _ _ (by omega) _ hs.1
    · exact hR
  · show OutOk inp σ1 _ (_ ++ M)
    have := outOk_new inp σ1 k 0 _ M (σ' 1) (by omega) (fun n _ _ hn => by omega)
      (fun p hp => (hs.2 p hp).1) hO
    rw [Nat.add_zero] at this
    exact this

theorem It_tau (σ : Nat → Int) : sigmaOf It.tauE σ 0 = σ 0 + 64 ∧ sigmaOf It.tauE σ 1 = σ 1 + 32 ∧ sigmaOf It.tauE σ 2 = σ 2 - 1 := by
  simp only [sigmaOf, tauAt, It.tauE, List.getD_cons_succ, List.getD_cons_zero, Lin.eval, dotC, Nat.zero_add, Nat.reduceAdd]
  omega

theorem It0_tau (σ : Nat → Int) : sigmaOf It0.tauE σ 0 = σ 0 + 64 ∧ sigmaOf It0.tauE σ 1 = σ 1 + 32 ∧ sigmaOf It0.tauE σ 2 = σ 2 - 1 := by
  simp only [sigmaOf, tauAt, It0.tauE, List.getD_cons_succ, List.getD_cons_zero, Lin.eval, dotC, Nat.zero_add, Nat.reduceAdd]
  omega

theorem loop (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (hw : WfMem 4 rodata 24 mem0c) (σ0 σ1 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) (orcC : Nat → Bool) :
    ∀ (j k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog),
      σ' 0 = σ0 + 64 * k → σ' 1 = σ1 + 32 * k → σ' 2 = j →
      InRange σ1 (32 * k) M → OutOk inp σ1 k M → PushOk M →
      let fin := run prog 4 mem0c orcC (j * It.NS + T0b.NS) (fr M (mapState e σ' KH1))
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        InRange σ1 (32 * (k + j)) fin.mem ∧ OutOk inp σ1 (k + j) fin.mem := by
  intro j
  induction j with
  | zero =>
    intro k σ' e M h0 h1 h2 hR hO hP
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    exact exit_step inp mem0c hw σ1 orcC KH1 KH1_nOnly T0b.NS T0b.KF T0b.EF _ rfl
      (fun env0 σ m o h hσ => T0b.run_final env0 σ m o h hσ) T0b.log_final T0b.KF_halted T0b.KF_err T0b.KF_tail
      k σ' e M h1 (by omega) hR hO hP
  | succ j ih =>
    intro k σ' e M h0 h1 h2 hR hO hP
    obtain ⟨e', M', hrun, hR', hO', hP'⟩ := iter_step inp mem0c hw σ0 σ1 hin orcC KH1 KH1_nOnly It.NS It.KF It.EF _ rfl
      (fun env0 σ m o h hσ => It.run_final env0 σ m o h hσ) It.tauE It.KF_inst It.KF_shape It_tau
      (fun inp env0 σ hm => It.out_final inp env0 σ hm) It.log_final k σ' e M h0 h1 (by omega) hR hO hP
    rw [show (j + 1) * It.NS + T0b.NS = It.NS + (j * It.NS + T0b.NS) by rw [Nat.succ_mul]; omega, run_add, hrun]
    have t := It_tau σ'
    have := ih (k + 1) (sigmaOf It.tauE σ') e' M' (by rw [t.1, h0]; omega) (by rw [t.2.1, h1]; omega)
      (by rw [t.2.2, h2]; omega) hR' hO' hP'
    obtain ⟨a, b, c, d, f⟩ := this
    refine ⟨a, b, c, ?_, ?_⟩
    · rw [show k + (j + 1) = k + 1 + j by omega]; exact d
    · rw [show k + (j + 1) = k + 1 + j by omega]; exact f

/-- The instruction count of a call with `c` blocks. -/
def steps (c : Nat) : Nat := NP + (if c = 0 then T0a.NS else It0.NS + ((c - 1) * It.NS + T0b.NS))

/-- **`hashtree_sha256_avx_x1` is correct for every count.**  Called (System V) with `c` blocks, on any
well-formed memory whose input buffer holds `inp`: it returns via `ret` without a model error after
`steps c` instructions, it wrote only the `32 c` output bytes and bytes of its stack frame, and
output byte `32 n + 4 i + b` is byte `4 i + b` of SHA-256 of block `n`. -/
theorem correct (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (he : EnvMem env0 σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := run prog 4 mem0c orcC (steps c) (mapState env0 σ (entryS 24))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem := by
  have h0 : Mem0Rel env0 σ (mem0s 4 rodata 24) mem0c := mem0Rel_of_wf 4 rodata 24 env0 σ mem0c hw he
  have hPr := (slice_sound env0 σ (mem0s 4 rodata 24) mem0c h0 prog 4 (fun _ => false) orcC NP (entryS 24) KP []
    slicePro rfl (fun p hp => by rw [KP_assume] at hp; cases hp)).1
  let e0 := envAbs env0 (run prog 4 (mem0s 4 rodata 24) (fun _ => false) NP (entryS 24))
  simp only [steps]
  rw [run_add, hPr, mapState_reached e0 σ KP KH0 tauP KP_inst]
  have hσ : ∀ i, sigmaOf tauP σ i = (tauP.getD i (Lin.sym i)).eval σ := fun _ => rfl
  have s0 : sigmaOf tauP σ 0 = σ 0 + 64 * 0 := by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym]
  have s1 : sigmaOf tauP σ 1 = σ 1 + 32 * 0 := by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym]
  have s2 : sigmaOf tauP σ 2 = c := by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym, hc]
  let Mp := KP.mem.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))
  have hR : InRange (σ 1) (32 * 0) Mp := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := KP_log q hq
    right
    simp only [mapAddr, Lin.eval, h2, dotC, h1]
    refine ⟨trivial, ?_, ?_⟩ <;> simp only [lo] at h3 <;> omega
  have hO : OutOk inp (σ 1) 0 Mp := fun n _ _ hn => by omega
  have hP : PushOk Mp := fun o h1 h2 => pushOk_sound e0 σ KP lo KP_push o h1 h2
  by_cases hc0 : c = 0
  · subst hc0
    simp only [ite_true]
    have := exit_step inp mem0c hw (σ 1) orcC KH0 KH0_nOnly T0a.NS T0a.KF T0a.EF _ rfl
      (fun env0 σ m o h hσ => T0a.run_final env0 σ m o h hσ) T0a.log_final T0a.KF_halted T0a.KF_err T0a.KF_tail
      0 (sigmaOf tauP σ) e0 Mp s1 (by omega) hR hO hP
    simpa using this
  · simp only [hc0, ite_false]
    rw [run_add]
    obtain ⟨e', M', hrun, hR', hO', hP'⟩ := iter_step inp mem0c hw (σ 0) (σ 1) hin orcC KH0 KH0_nOnly It0.NS It0.KF It0.EF _ rfl
      (fun env0 σ m o h hσ => It0.run_final env0 σ m o h hσ) It0.tauE It0.KF_inst It0.KF_shape It0_tau
      (fun inp env0 σ hm => It0.out_final inp env0 σ hm) It0.log_final 0 (sigmaOf tauP σ) e0 Mp s0 s1 (by omega) hR hO hP
    rw [hrun]
    have t := It0_tau (sigmaOf tauP σ)
    have := loop inp mem0c hw (σ 0) (σ 1) hin orcC (c - 1) 1 (sigmaOf It0.tauE (sigmaOf tauP σ)) e' M'
      (by rw [t.1, s0]; omega) (by rw [t.2.1, s1]; omega) (by rw [t.2.2, s2]; omega) hR' hO' hP'
    obtain ⟨a, b, d, f, g⟩ := this
    refine ⟨a, b, d, ?_, ?_⟩
    · have hc1 : 32 * (1 + (c - 1)) = 32 * c := by omega
      rw [hc1] at f; exact f
    · have hc1 : 1 + (c - 1) = c := by omega
      rw [hc1] at g; exact g

/-- The hypotheses are satisfiable for every input and count. -/
theorem hyps_sat (c : Nat) (inp : Nat → Byte) (env : Key → W32) (σ : Nat → Int) (hc : σ 2 = c) :
    let m := cmem 4 rodata 24 (fun x => (inp (x - σ 0).toNat).zeroExtend 32)
    WfMem 4 rodata 24 m ∧ EnvMem (ecomb env σ m) σ m ∧ σ 2 = c ∧
      ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
  refine ⟨cmem_wf _ _ _, envMem_ecomb _ _ _, hc, ?_⟩
  intro o
  simp only [cmem, rIn, rStack]
  simp only [show (1 : Region) ≠ 4 from by decide, show (1 : Region) ≠ 3 from by decide, ite_false, ite_true]
  congr 3
  omega

end Hashtree.Proofs.AvxX1L
