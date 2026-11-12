import Hashtree.Gen.ShaniL.It.Shape
import Hashtree.Gen.ShaniL.T1.Final
import Hashtree.Gen.ShaniL.T0.Final
import Hashtree.Asm.X86Loop

/-!
# `hashtree_sha256_shani_x2` (shipped linux_amd64 object) is correct for every count

From the four checked segments — the prologue to the loop-head cut `KH`, one 2-block iteration
from `KH` back to `KH` (pointers +128 / +64, count −2), and the exits for count 0 and 1 — by
induction on the iterations: started on any well-formed memory holding the input bytes, the
kernel returns (via `ret`), without a model error, after `steps c` instructions; it wrote only
the `32 c` output bytes; and output byte `32 n + j` is byte `j` of SHA-256 of block `n`.
-/

set_option maxRecDepth 10000

namespace Hashtree.Proofs.Shani
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.Shani Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Gen.ShaniL

/-- The first `nblk` output blocks (base `ob`) hold the SHA-256 bytes of the input blocks. -/
def OutOk (inp : Nat → Byte) (ob : Int) (nblk : Nat) (M : CLog) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

/-- Every logged write is an output byte in `[ob, ob + len)` or a byte of the 88-byte stack frame
below the entry stack pointer (offset 24; the return address at 24..31 is never written). -/
def InRange (ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ -64 ≤ p.1.off ∧ p.1.off < 24)

theorem outLog_of (ob : Int) (len : Nat) (M : CLog) (h : InRange ob len M) : OutLog M := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

theorem inRange_shift (ob ob' : Int) (k len : Nat) (L : CLog) (h : InRange ob' len L) (hob : ob' = ob + 64 * k) :
    InRange ob (64 * k + len) L := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, by omega, by omega⟩
  · exact Or.inr h

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

theorem blk_shift (inp : Nat → Byte) (k n : Nat) : blk (fun o => inp (128 * k + o)) n = blk inp (2 * k + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-- The input bytes of iteration `k`, relative to its input pointer. -/
theorem hmem_k (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (k : Nat) (e : Key → W32) (σ' : Nat → Int) (h0 : σ' 0 = σ0 + 128 * k) (M : CLog) (hM : OutLog M) :
    HMem 128 (fun o => inp (128 * k + o)) (ecomb e σ' (view M mem0c)) := by
  intro o _
  simp only [ecomb]
  rw [view_other M mem0c _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
    fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
  have ha : (⟨rIn, (⟨(o : Int), [1]⟩ : Lin).eval σ'⟩ : Addr Int) = ⟨rIn, σ0 + ((128 * k + o : Nat) : Int)⟩ := by
    simp only [Lin.eval, dotC, Addr.mk.injEq, true_and]
    omega
  rw [ha, hin]
  rfl

theorem KH_nOnly : KH.nOnly = true := by decide

/-- The state at a loop head denotes the same with the memory keys re-read from memory. -/
theorem head_ecomb (e : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int) :
    mapState e σ' KH = mapState (ecomb e σ' m) σ' KH :=
  mapState_nOnly _ _ σ' (fun _ => rfl) KH KH_nOnly

theorem T0_mem : T0.KF.mem = [] := by decide
theorem T0_halted : T0.KF.halted = true := by decide
theorem T0_err : T0.KF.err = none := by decide
theorem T0_tail : T0.KF.tail = none := by decide
theorem T1_halted : T1.KF.halted = true := by decide
theorem T1_err : T1.KF.err = none := by decide
theorem T1_tail : T1.KF.tail = none := by decide

/-- Mapped log entries of a segment's final cut: output bytes at `[σ' 1, σ' 1 + len)`. -/
theorem range_seg (e : Key → W32) (σ' : Nat → Int) (K : State E Lin) (len : Nat)
    (hl : ∀ p ∈ K.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < len) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -64 ≤ p.1.off.k ∧ p.1.off.k < 24)) :
    InRange (σ' 1) len (K.mem.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
    refine ⟨trivial, ?_, ?_⟩ <;> omega
  · right
    simp only [mapAddr, Lin.eval, h2, dotC, h1]
    refine ⟨trivial, ?_, ?_⟩ <;> omega

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

/-- Output blocks below `lo` are not touched by a log above it. -/
theorem outOk_app (inp : Nat → Byte) (ob : Int) (n0 : Nat) (L M : CLog)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off) (hM : OutOk inp ob n0 M) :
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
theorem outOk_new (inp : Nat → Byte) (ob : Int) (n0 nb : Nat) (L M : CLog) (σ1 : Int) (hσ1 : σ1 = ob + 32 * (n0 : Int))
    (hnew : ∀ n i b, n < nb → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) L = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp (n0 + n))).getD (4 * i + b) 0).zeroExtend 32)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off) (hM : OutOk inp ob n0 M) :
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

/-- System V callee-saved general registers: rbx, rbp, r12–r15. -/
def calleeRegs : List Nat := [3, 5, 12, 13, 14, 15]

theorem callee_ids (g : Nat) (hg : g ∈ calleeRegs) : 2 * g ∈ calleeIds ∧ 2 * g + 1 ∈ calleeIds := by
  simp only [calleeRegs, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Callee-saved registers hold their entry values. -/
def RegsOk (env0 : Key → W32) (s : CState) : Prop :=
  (∀ g ∈ calleeRegs, s.gpr[g]? = some (.num (env0 (.n (2 * g))) (env0 (.n (2 * g + 1))))) ∧
    s.gpr[4]? = some (.ptr ⟨rStack, 32⟩)

theorem regs_of (env env0 : Key → W32) (σ : Nat → Int) (K : State E Lin) (M : CLog)
    (hK : ∀ g ∈ calleeRegs, K.gpr[g]? = some (.num (.var (.n (2 * g))) (.var (.n (2 * g + 1)))))
    (hsp : K.gpr[4]? = some (.ptr ⟨rStack, ⟨32, []⟩⟩))
    (hk : ∀ id ∈ calleeIds, env (.n id) = env0 (.n id)) : RegsOk env0 (fr M (mapState env σ K)) := by
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := callee_ids g hg
    simp only [fr, mapState, List.getElem?_map, hK g hg, Option.map_some, mapVal, E.eval, hk _ h1, hk _ h2]
  · simp only [fr, mapState, List.getElem?_map, hsp, Option.map_some, mapVal, mapAddr, Lin.eval, dotC]
    rfl

theorem T0_regs : ∀ g ∈ calleeRegs, T0.KF.gpr[g]? = some (.num (.var (.n (2 * g))) (.var (.n (2 * g + 1)))) := by decide
theorem T1_regs : ∀ g ∈ calleeRegs, T1.KF.gpr[g]? = some (.num (.var (.n (2 * g))) (.var (.n (2 * g + 1)))) := by decide
theorem T0_sp : T0.KF.gpr[4]? = some (.ptr ⟨rStack, ⟨32, []⟩⟩) := by decide
theorem T1_sp : T1.KF.gpr[4]? = some (.ptr ⟨rStack, ⟨32, []⟩⟩) := by decide

/-- The instruction count of a call with `c` blocks. -/
def steps (c : Nat) : Nat := 4 + (c / 2 * It.NS + (if c % 2 = 0 then T0.NS else T1.NS))

theorem loop (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (hw : WfMem 4 rodata 24 mem0c) (σ0 σ1 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) (orcC : Nat → Bool) (r : Nat) (hr : r < 2)
    (env0 : Key → W32) :
    ∀ (j k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog),
      σ' 0 = σ0 + 128 * k → σ' 1 = σ1 + 64 * k → σ' 2 = 2 * j + r →
      InRange σ1 (64 * k) M → OutOk inp σ1 (2 * k) M → (∀ id ∈ calleeIds, e (.n id) = env0 (.n id)) →
      let fin := run prog 4 mem0c orcC (j * It.NS + (if r = 0 then T0.NS else T1.NS)) (fr M (mapState e σ' KH))
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        InRange σ1 (64 * k + 64 * j + 32 * r) fin.mem ∧ OutOk inp σ1 (2 * k + 2 * j + r) fin.mem ∧
        RegsOk env0 fin := by
  intro j
  induction j with
  | zero =>
    intro k σ' e M h0 h1 h2 hR hO hk
    have hM := outLog_of _ _ M hR
    let E := ecomb e σ' (view M mem0c)
    have hrel : Mem0Rel E σ' (mem0s 4 rodata 24) (view M mem0c) :=
      mem0Rel_of_wf 4 rodata 24 E σ' _ (wf_view rodata mem0c M hM hw) (envMem_ecomb _ _ _)
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [run_fr, head_ecomb e σ' (view M mem0c)]
    rcases (by omega : r = 0 ∨ r = 1) with hr0 | hr1
    · subst hr0
      simp only [ite_true]
      rw [T0.run_final E σ' (view M mem0c) orcC hrel (by omega)]
      refine ⟨T0_halted, T0_err, T0_tail, ?_, ?_, regs_of _ env0 σ' T0.KF M T0_regs T0_sp
        (fun id hid => (T0.keep_final E id hid).trans (hk id hid))⟩
      · show InRange σ1 _ (_ ++ M)
        simp only [mapState]
        rw [show (T0.K1).mem = T0.KF.mem from rfl, T0_mem, List.map_nil, List.nil_append]
        exact inRange_mono _ _ _ (by omega) M hR
      · show OutOk inp σ1 _ (_ ++ M)
        simp only [mapState]
        rw [show (T0.K1).mem = T0.KF.mem from rfl, T0_mem, List.map_nil, List.nil_append]
        exact hO
    · subst hr1
      simp only [show (1 : Nat) ≠ 0 from by decide, ite_false]
      rw [T1.run_final E σ' (view M mem0c) orcC hrel (by omega)]
      refine ⟨T1_halted, T1_err, T1_tail, ?_, ?_, regs_of _ env0 σ' T1.KF M T1_regs T1_sp
        (fun id hid => (T1.keep_final E id hid).trans (hk id hid))⟩
      · show InRange σ1 _ (_ ++ M)
        apply inRange_app
        · exact inRange_mono _ _ _ (by omega) _
            (inRange_shift σ1 (σ' 1) k 32 _ (range_seg (T1.EF E) σ' T1.KF 32 T1.log_final) h1)
        · exact inRange_mono _ _ _ (by omega) M hR
      · show OutOk inp σ1 _ (_ ++ M)
        have hnew := T1.out_final (fun o => inp (128 * k + o)) E σ' (hmem_k inp mem0c σ0 hin k e σ' h0 M hM)
        refine outOk_new inp σ1 (2 * k) 1 _ M (σ' 1) (by omega) ?_ ?_ hO
        · intro n i b hn hi hb
          obtain ⟨x, hx, hv⟩ := hnew n i b hn hi hb
          refine ⟨x, hx, ?_⟩
          rw [hv, blk_shift]
        · intro p hp
          rcases above_of _ _ _ (range_seg (T1.EF E) σ' T1.KF 32 T1.log_final) p hp with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
  | succ j ih =>
    intro k σ' e M h0 h1 h2 hR hO hk
    have hM := outLog_of _ _ M hR
    let E := ecomb e σ' (view M mem0c)
    have hrel : Mem0Rel E σ' (mem0s 4 rodata 24) (view M mem0c) :=
      mem0Rel_of_wf 4 rodata 24 E σ' _ (wf_view rodata mem0c M hM hw) (envMem_ecomb _ _ _)
    rw [show (j + 1) * It.NS + (if r = 0 then T0.NS else T1.NS) =
        It.NS + (j * It.NS + (if r = 0 then T0.NS else T1.NS)) by rw [Nat.succ_mul]; omega, run_add]
    rw [run_fr, head_ecomb e σ' (view M mem0c), It.run_final E σ' (view M mem0c) orcC hrel (by omega)]
    have hvr : mapState (It.EF E) σ' It.KF = mapState (It.EF E) σ' { It.KF with vr := KH.vr } :=
      mapState_vrInst (It.E224 E) σ' _ _ _ _ _ _ _ _ It.slice224 KH.vr It.KF_vr
    rw [show It.K225 = It.KF from rfl, show It.E225 E = It.EF E from rfl, hvr,
      mapState_reached (It.EF E) σ' _ KH It.tauE It.KF_shape, fr_fr]
    have hσ : ∀ i, sigmaOf It.tauE σ' i = (It.tauE.getD i (Lin.sym i)).eval σ' := fun _ => rfl
    have hL := range_seg (It.EF E) σ' It.KF 64 It.log_final
    have hnew := It.out_final (fun o => inp (128 * k + o)) E σ' (hmem_k inp mem0c σ0 hin k e σ' h0 M hM)
    have := ih (k + 1) (sigmaOf It.tauE σ') (It.EF E) (_ ++ M)
      (by rw [hσ]; simp [It.tauE, Lin.eval, dotC]; omega)
      (by rw [hσ]; simp [It.tauE, Lin.eval, dotC]; omega)
      (by rw [hσ]; simp [It.tauE, Lin.eval, dotC]; omega)
      (by
        apply inRange_app
        · exact inRange_mono _ _ _ (by omega) _ (inRange_shift σ1 (σ' 1) k 64 _ hL h1)
        · exact inRange_mono _ _ _ (by omega) M hR)
      (by
        have := outOk_new inp σ1 (2 * k) 2 _ M (σ' 1) (by omega)
          (by
            intro n i b hn hi hb
            obtain ⟨x, hx, hv⟩ := hnew n i b hn hi hb
            refine ⟨x, hx, ?_⟩
            rw [hv, blk_shift])
          (by
            intro p hp
            rcases above_of _ _ _ hL p hp with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)) hO
        rw [show 2 * (k + 1) = 2 * k + 2 by omega]; exact this)
      (fun id hid => (It.keep_final E id hid).trans (hk id hid))
    obtain ⟨a, b, c, d, f, g⟩ := this
    refine ⟨a, b, c, ?_, ?_, g⟩
    · rw [show 64 * k + 64 * (j + 1) + 32 * r = 64 * (k + 1) + 64 * j + 32 * r by omega]; exact d
    · rw [show 2 * k + 2 * (j + 1) + r = 2 * (k + 1) + 2 * j + r by omega]; exact f

theorem KP_assume : KP.assume = [] := by decide

/-- **The SHA-NI kernel is correct for every count.**  Called (System V) with `c` blocks, on any
well-formed memory whose input buffer holds `inp`: it returns via `ret` without a model error after
`steps c` instructions; it wrote only the `32 c` output bytes and its 88-byte stack frame below the
entry stack pointer; output byte `32 n + 4 i + b` is byte `4 i + b` of SHA-256 of block `n`; and
rbx, rbp, r12–r15 hold their entry values and rsp is the entry rsp + 8 (popped return address). -/
theorem shani_correct (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (he : EnvMem env0 σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := run prog 4 mem0c orcC (steps c) (mapState env0 σ (entryS 24))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧ RegsOk env0 fin := by
  have h0 : Mem0Rel env0 σ (mem0s 4 rodata 24) mem0c := mem0Rel_of_wf 4 rodata 24 env0 σ mem0c hw he
  have hP := (slice_sound env0 σ (mem0s 4 rodata 24) mem0c h0 prog 4 (fun _ => false) orcC 4 (entryS 24) KP []
    slicePro rfl (fun p hp => by rw [KP_assume] at hp; cases hp)).1
  simp only [steps]
  let e0 := envAbs env0 (run prog 4 (mem0s 4 rodata 24) (fun _ => false) 4 (entryS 24))
  rw [run_add, hP, KP_inst, mapState_subst, ← fr_nil (mapState e0 (sigmaOf tauP σ) KH)]
  have hσ : ∀ i, sigmaOf tauP σ i = (tauP.getD i (Lin.sym i)).eval σ := fun _ => rfl
  have := loop inp mem0c hw (σ 0) (σ 1) hin orcC (c % 2) (Nat.mod_lt _ (by decide)) env0 (c / 2) 0 (sigmaOf tauP σ) e0 []
    (by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym])
    (by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym])
    (by rw [hσ]; simp [tauP, Lin.eval, dotC, Lin.sym, hc]; omega)
    (fun p hp => by cases hp) (fun n _ _ hn => by omega)
    (fun id hid => slice_keep _ _ _ _ _ _ _ _ slicePro env0 id (keepP id hid))
  obtain ⟨a, b, d, f, g, hreg⟩ := this
  refine ⟨a, b, d, ?_, ?_, hreg⟩
  · exact inRange_mono (σ 1) (64 * 0 + 64 * (c / 2) + 32 * (c % 2)) (32 * c) (by omega) _ f
  · have hcc : 2 * 0 + 2 * (c / 2) + c % 2 = c := by omega
    rw [hcc] at g; exact g

/-- The hypotheses are satisfiable for every input and count. -/
theorem shani_hyps_sat (c : Nat) (inp : Nat → Byte) (env : Key → W32) (σ : Nat → Int) (hc : σ 2 = c) :
    let m := cmem 4 rodata 24 (fun x => (inp (x - σ 0).toNat).zeroExtend 32)
    WfMem 4 rodata 24 m ∧ EnvMem (ecomb env σ m) σ m ∧ σ 2 = c ∧
      ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
  refine ⟨cmem_wf _ _ _, envMem_ecomb _ _ _, hc, ?_⟩
  intro o
  simp only [cmem, rIn, rStack]
  simp only [show (1 : Region) ≠ 4 from by decide, show (1 : Region) ≠ 3 from by decide, ite_false, ite_true]
  congr 3
  omega

end Hashtree.Proofs.Shani
