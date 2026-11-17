import Hashtree.Proofs.Avx2X8ChainRegs
import Hashtree.Proofs.WrapperAmd64

/-!
# The linux/amd64 wrapper `HashtreeHash` calling the shipped avx2 tail chain

`WrapperAmd64.wrapRun` models the wrapper's `CALL` by `callK`: one kernel, its rodata at
region 4, a pending tail call dropped.  That fits shani and avx_x1 only; the avx2 dispatch target
`hashtree_sha256_avx2_x8` ends in tail calls into `hashtree_sha256_avx_x4` and
`hashtree_sha256_avx_x1`.  This module states the same wrapper text with the chain-aware call
(`X86Chain.callChain`, cf. R5's `WinWrapperChain` for windows):

* `wrapRunC links`: prologue `pre`, the alignment, `CALL` (`pushRet`, then `chainRun` over
  `links.map specOf` — the run reads only the links, `chainRun_links`), epilogue `post`.
* `links8`: avx2_x8 (table at region 8) -> avx_x4 (region 4) -> avx_x1 (region 9), each with its
  own rodata table (`Tables`: regions 8 and 9; x4's is the wrapper's `WfMemW` region 4).
  `withTables_ok`: the layout is compatible with the wrapper's other memory hypotheses (and
  `WrapperAmd64.wrapper_hyps_sat` builds those), so the theorems below are not vacuous.
* `ChainSpec links D`: the chain analogue of `KSpec` (from `entryW`, every count: returns
  without error or pending tail, writes in outputs and `[σ 9 - D, σ 9)`, all outputs SHA-256,
  `RegsOk`).
* `wrapper_chain`: a chain meeting `ChainSpec` with `D ≤ 2009` makes the wrapper return with
  `RET`, rsp = `SPe + 8`, the caller's rbp, writes only output bytes and `[SPe - 2056, SPe)`,
  every output byte SHA-256 (the conclusion of `wrapper_kernel`).
* `chainSpec8` (every count, count 0 included) and **`wrapper_avx2_chain`**: `HashtreeHash` on
  avx2 hardware (`pick false false true = .avx2`, whose kernel is the head of `links8`) is
  correct for every count — conditional only on R2c's `TurnOut8`, `TurnOut8Last` (proved on
  research/formal-r2c-x16out) and `TurnOut4Last`.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace Hashtree.Proofs.WrapperAmd64Chain
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Region
open Hashtree.Kernels.X86.WrapperLinux
open Hashtree.Proofs.WrapperAmd64
open Hashtree.Proofs.X86Chain (Link chainRun callChain chainRun_fr KSpecC chain_sound step resume)
open Hashtree.Proofs.ShaniW (OutOk RegsOk)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW)
open Hashtree.Proofs.Avx2X8ChainC (link8 link4 link1)
open Hashtree.Proofs.Avx2X8OutLink (TurnOut8 TurnOut8Last TurnOut4Last D8L)
open Hashtree.Proofs.Avx2X8ChainOut (FootC)
open Hashtree.Proofs.Avx2X8ChainRegs (RetR x8SpecsR x8KSpecC_full x8Specs0 x8KSpecC_zero)
open Hashtree.Proofs.Avx2X8X4WAgree (fr_nil)

abbrev CSpec := Hashtree.Proofs.X86Chain.Spec

/-! ## The chain call reads only the links -/

/-- A link with trivial conditions: what the machine runs, nothing the proof assumes. -/
def specOf (l : Link) : CSpec := ⟨l, fun _ => True, fun _ => True⟩

theorem chainRun_links (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (c : Nat) :
    ∀ (specs specs' : List CSpec), specs.map Hashtree.Proofs.X86Chain.Spec.link = specs'.map Hashtree.Proofs.X86Chain.Spec.link →
      ∀ s, chainRun m0 orc c specs s = chainRun m0 orc c specs' s
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | [a], [b], h, s => by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    simp only [chainRun, step, h]
  | [_], _ :: _ :: _, h, _ => by simp at h
  | _ :: _ :: _, [_], h, _ => by simp at h
  | a :: a' :: r, b :: b' :: r', h, s => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have ih := chainRun_links m0 orc c (a' :: r) (b' :: r')
      (by simp only [List.map_cons, h2, h3])
    simp only [chainRun, step, h1, h2]
    cases (run b.link.prog b.link.ro m0 orc (b.link.steps c) s).tail with
    | none => rfl
    | some t =>
      simp only
      split
      · exact ih _
      · rfl

/-! ## The wrapper with the chain-aware call -/

/-- `HashtreeHash` with its `CALL` following the tail chain `links`. -/
def wrapRunC (links : List Link) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (c : Nat)
    (s : CState) : CState :=
  run post 4 m orc 4 (callChain m orc c (links.map specOf) (pushRet (alignStep m orc (run pre 4 m orc 9 s))))

/-- The shipped chain from the avx2 dispatch target `hashtree_sha256_avx2_x8`. -/
def links8 : List Link := [link8 8, link4, link1 9]

theorem links8_names : links8.map Link.name =
    ["hashtree_sha256_avx2_x8", "hashtree_sha256_avx_x4", "hashtree_sha256_avx_x1"] := rfl

theorem links8_regions : links8.map Link.ro = [8, 4, 9] := rfl

/-- On avx2 hardware (no SHA-NI, no AVX-512) the wrapper dispatches to the head of `links8`. -/
theorem pick_avx2 : pick false false true = .avx2 := rfl

theorem links8_head : (links8.head?).map Link.prog = some (kprogOf .avx2) := rfl

/-! ## The table layout -/

/-- The avx2_x8 and avx_x1 tables in regions 8 and 9 (avx_x4's is region 4, part of the
wrapper's `WfMemW`). -/
def Tables (m : Addr Int → Cell W32 Int) : Prop :=
  (∀ o, m ⟨8, o⟩ = .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86.Avx2X8.rodata.getD o.toNat 0)) 0) ∧
  (∀ o, m ⟨9, o⟩ = .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86.AvxX1.rodata.getD o.toNat 0)) 0)

/-- Lay the two tables into regions 8 and 9 of any memory. -/
def withTables (m : Addr Int → Cell W32 Int) : Addr Int → Cell W32 Int := fun a =>
  if a.region = 8 then .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86.Avx2X8.rodata.getD a.off.toNat 0)) 0
  else if a.region = 9 then .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86.AvxX1.rodata.getD a.off.toNat 0)) 0
  else m a

theorem withTables_other (m : Addr Int → Cell W32 Int) (a : Addr Int) (h8 : a.region ≠ 8)
    (h9 : a.region ≠ 9) : withTables m a = m a := by
  simp [withTables, h8, h9]

theorem argCells_env (e e' : Key → W32) (σ : Nat → Int) (k : Int) (c : Cell E Lin)
    (h : plookup k argCells = some c) : mapCell e σ c = mapCell e' σ c := by
  have hm := plookup_mem k argCells c h
  simp only [argCells, List.mem_append, List.mem_map, List.mem_range] at hm
  rcases hm with (⟨j, _, hj⟩ | ⟨j, _, hj⟩) | ⟨j, _, hj⟩ <;>
    (simp only [Prod.mk.injEq] at hj; rw [← hj.2]; rfl)

/-- **Non-vacuity of the layout**: a memory meeting the wrapper's hypotheses for the avx_x4
table still meets them with the other two tables laid in (environment re-read). -/
theorem withTables_ok (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Hashtree.Spec.Byte) (hw : WfMemW Hashtree.Kernels.X86.AvxX4.rodata argCells env σ m)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    WfMemW Hashtree.Kernels.X86.AvxX4.rodata argCells (ecomb env σ (withTables m)) σ (withTables m) ∧
      EnvMem (ecomb env σ (withTables m)) σ (withTables m) ∧ Tables (withTables m) ∧
      (∀ o : Nat, withTables m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have o4 : ∀ o, withTables m ⟨4, o⟩ = m ⟨4, o⟩ := fun o =>
    withTables_other m _ (show (4 : Region) ≠ 8 by decide) (show (4 : Region) ≠ 9 by decide)
  have oS : ∀ o, withTables m ⟨rStack, o⟩ = m ⟨rStack, o⟩ := fun o =>
    withTables_other m _ (show (rStack : Region) ≠ 8 by decide) (show (rStack : Region) ≠ 9 by decide)
  have oI : ∀ o, withTables m ⟨rIn, o⟩ = m ⟨rIn, o⟩ := fun o =>
    withTables_other m _ (show (rIn : Region) ≠ 8 by decide) (show (rIn : Region) ≠ 9 by decide)
  refine ⟨⟨fun o => (o4 o).trans (h1 o), fun k a b => (oS _).trans (h2 k a b),
    fun o => by rw [oI]; exact h3 o, fun k c hl hk hc => ?_⟩, envMem_ecomb _ _ _,
    ⟨fun _ => rfl, fun _ => rfl⟩, fun o => (oI _).trans (hin o)⟩
  rw [oS, h4 k c hl hk hc]
  exact argCells_env env _ σ k c hl

/-! ## The chain contract at the call state -/

/-- What a tail chain must deliver from the wrapper's call state `entryW` (the chain analogue
of `WrapperAmd64.KSpec`). -/
def ChainSpec (links : List Link) (D : Nat) : Prop :=
  ∀ (c : Nat) (inp : Nat → Hashtree.Spec.Byte) (env0 : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (orcC : Nat → Bool),
    WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ m → Tables m → σ 2 = c → σ 9 % 16 = 8 →
    (∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let f := chainRun m orcC c (links.map specOf) (mapState env0 σ entryW)
    f.halted = true ∧ f.err = none ∧ f.tail = none ∧ Foot (σ 9) D (σ 1) (32 * c) f.mem ∧
      OutOk inp (σ 1) c f.mem ∧ RegsOk env0 σ f

theorem wfAt_of (r : Region) (rodata : List Nat) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env σ m)
    (hr : ∀ o, m ⟨r, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) :
    WfMemAtW r rodata [] env σ m := by
  obtain ⟨_, h2, h3, _⟩ := hw
  exact ⟨hr, h2, h3, fun k c h _ _ => by simp [plookup] at h⟩

theorem foot_of (σ : Nat → Int) (c : Nat) (F : CLog) (h : FootC σ c [] F) :
    Foot (σ 9) D8L (σ 1) (32 * c) F := by
  intro p hp
  rcases h p hp with h | ⟨a, b, d⟩ | ⟨a, b, d⟩
  · cases h
  · exact Or.inl ⟨a, b, by push_cast; omega⟩
  · exact Or.inr ⟨a, b, d⟩

/-- **The shipped avx2 chain meets the chain contract**, every count (count 0: the x8 kernel's
own early return). -/
theorem chainSpec8 (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last) :
    ChainSpec links8 D8L := by
  intro c inp env σ m orcC hw hT hc habi hin
  obtain ⟨t8, t9⟩ := hT
  have hw8 := wfAt_of 8 Hashtree.Kernels.X86.Avx2X8.rodata env σ m hw t8
  have hw1 := wfAt_of 9 Hashtree.Kernels.X86.AvxX1.rodata env σ m hw t9
  dsimp only
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0
    have hK := x8KSpecC_zero inp env σ m orcC 8 9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw8 (by rw [hc]; rfl)
    rw [chainRun_links m orcC 0 (links8.map specOf) (x8Specs0 inp env σ 8 9) rfl]
    obtain ⟨he, ht, hpost⟩ := chain_sound m orcC 0 _ (mapState env σ entryW) hK rfl
    have hR : RetR inp env σ 0 [] (chainRun m orcC 0 (x8Specs0 inp env σ 8 9) (mapState env σ entryW)) := by
      rcases hpost with h | h | h <;> exact h
    obtain ⟨⟨⟨hh, _, _⟩, hO, hF⟩, hRg⟩ := hR
    exact ⟨hh, he, ht, foot_of σ 0 _ hF, hO, hRg⟩
  · have hK := x8KSpecC_full hT8 hT8L hT4L c inp env σ m orcC [] 8 9 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hw8 hw hw1 (fun p hp => by cases hp) hc hpos habi hin
    rw [chainRun_links m orcC c (links8.map specOf) (x8SpecsR c inp env σ m orcC [] 8 9) rfl]
    obtain ⟨he, ht, hpost⟩ := chain_sound m orcC c _ (mapState env σ entryW) hK (fr_nil _).symm
    have hR : RetR inp env σ c [] (chainRun m orcC c (x8SpecsR c inp env σ m orcC [] 8 9)
        (mapState env σ entryW)) := by
      rcases hpost with h | h | h <;> exact h
    obtain ⟨⟨⟨hh, _, _⟩, hO, hF⟩, hRg⟩ := hR
    exact ⟨hh, he, ht, foot_of σ c _ hF, hO, hRg⟩

/-! ## The wrapper composition (as `wrapper_kernel`, call = `callChain`) -/

/-- **The wrapper with any tail chain meeting `ChainSpec`** (stack depth `D ≤ 2009`).  From the
wrapper's ABI0 entry, on a memory with the x4 table (region 4), the other tables (`Tables`) and
the input bytes, with `σ 10` naming the aligned call rsp: `HashtreeHash` returns via `RET` with
rsp = `SPe + 8` and the caller's rbp, every write is an output byte or a byte of
`[SPe - 2056, SPe)`, and every output byte is the SHA-256 byte of its block. -/
theorem wrapper_chain (links : List Link) (D : Nat) (hk : ChainSpec links D) (hD : D ≤ 2009)
    (c : Nat) (inp : Nat → Hashtree.Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW Hashtree.Kernels.X86.AvxX4.rodata argCells env σ mem0c) (he : EnvMem env σ mem0c)
    (hT : Tables mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    let fin := wrapRunC links mem0c orc c (mapState env σ wEntry)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem := by
  intro fin
  have hA1 : σ 10 + 8 ≤ σ 9 - 8 := by omega
  have hA2 : σ 9 - 47 ≤ σ 10 := by omega
  -- the prefix
  have h0 := m0W_rel Hashtree.Kernels.X86.AvxX4.rodata env σ mem0c hw he
  have hP := (slice_sound env σ m0W mem0c h0 pre 4 (fun _ => false) orc 9 wEntry Kpre [] slicePre rfl
    (fun p hp => by rw [Kpre_assume] at hp; cases hp)).1
  generalize heP : envAbs env (run pre 4 m0W (fun _ => false) 9 wEntry) = eP at hP
  -- the call state
  let σK := sigmaOf tauC σ
  have k0 : σK 0 = σ 0 := by simp [σK, sigmaOf, tauAt, tauC, Lin.eval_sym]
  have k1 : σK 1 = σ 1 := by simp [σK, sigmaOf, tauAt, tauC, Lin.eval_sym]
  have k2 : σK 2 = σ 2 := by simp [σK, sigmaOf, tauAt, tauC, Lin.eval_sym]
  have k5 : σK 5 = σ 9 - 2056 := by simp [σK, sigmaOf, tauAt, tauC, sAt_eval]; omega
  have k9 : σK 9 = σ 10 := by simp [σK, sigmaOf, tauAt, tauC, l10_eval]
  let f := fun (p : Addr Lin × Cell E Lin) => (mapAddr σ p.1, mapCell eP σ p.2)
  let Lm := (KC.mem.take 8).map f
  let Lb := Kpre.mem.map f
  have hLw : KC.mem.map f = Lm ++ Lb := by
    show KC.mem.map f = (KC.mem.take 8).map f ++ Kpre.mem.map f
    rw [← List.map_append, ← KC_mem_split]
  have hcall : { pushRet (alignStep mem0c orc (run pre 4 mem0c orc 9 (mapState env σ wEntry))) with pc := 0 } =
      fr (Lm ++ Lb) (mapState eP σK entryW) := by
    rw [hP, align_hom eP σ mem0c orc hA, push_hom, mapState_reached eP σ KC entryW tauC KC_shape]
    show fr (KC.mem.map f) _ = _
    rw [hLw]
  -- facts on the log
  have hLm : ∀ p ∈ Lm, p.1.region = rStack ∧ σ 10 ≤ p.1.off ∧ p.1.off < σ 10 + 8 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := marker_facts q hq
    simp only [f, mapAddr, lin10_eval σ _ h2, h1]
    exact ⟨trivial, by omega, by omega⟩
  have hLb : ∀ p ∈ Lb, p.1.region = rStack ∧ σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := bp_facts q hq
    simp only [f, mapAddr, linS_eval σ _ h2, h1]
    exact ⟨trivial, by omega, by omega⟩
  have hLw3 : ∀ p ∈ Lm ++ Lb, p.1.region = rStack := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact (hLm p h).1
    · exact (hLb p h).1
  have ne3 : ∀ (a : Addr Int), a.region ≠ rStack → ∀ p ∈ Lm ++ Lb, p.1 ≠ a := by
    intro a ha p hp heq; rw [← heq] at ha; exact ha (hLw3 p hp)
  -- the chain's memory
  let mK := view (Lm ++ Lb) mem0c
  have hmK4 : ∀ o, mK ⟨4, o⟩ = mem0c ⟨4, o⟩ := fun o =>
    view_other _ _ _ (ne3 ⟨4, o⟩ (by decide : (4 : Region) ≠ rStack))
  have hmKI : ∀ o, mK ⟨rIn, o⟩ = mem0c ⟨rIn, o⟩ := fun o =>
    view_other _ _ _ (ne3 ⟨rIn, o⟩ (by decide : rIn ≠ rStack))
  have hmKR : ∀ k : Int, 0 ≤ k → k < 8 → mK ⟨rStack, σK 9 + k⟩ = .pb ⟨rRet, 0⟩ k.toNat := by
    intro k h1 h2
    have hk' := marker_lk k.toNat (by omega)
    have hl := lookup_hom eP σ _ KC.mem _ (lkIs_sound _ _ _ hk')
    have ha : mapAddr σ (⟨rStack, l10 k.toNat⟩ : Addr Lin) = ⟨rStack, σK 9 + k⟩ := by
      simp only [mapAddr, l10_eval, k9]; congr 1; omega
    have hc0 : mapCell eP σ (Cell.pb ⟨rRet, Lin.ofInt 0⟩ k.toNat) = .pb ⟨rRet, 0⟩ k.toNat := by
      simp [mapCell, mapAddr, Lin.ofInt, Lin.eval, dotC]
    rw [ha, show KC.mem.map (fun p => (mapAddr σ p.1, mapCell eP σ p.2)) = Lm ++ Lb from hLw,
      Option.map_some, hc0] at hl
    simp only [mK, view, hl]
  have hwK : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] (ecomb eP σK mK) σK mK := by
    obtain ⟨hro, _, hinw, _⟩ := hw
    refine ⟨fun o => (hmK4 o).trans (hro o), hmKR, fun o => ?_, fun k c hl => by simp [plookup] at hl⟩
    rw [hmKI]; exact hinw o
  have hinK : ∀ o : Nat, mK ⟨rIn, σK 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
    intro o; rw [hmKI, k0]; exact hin o
  have hTK : Tables mK := by
    obtain ⟨t8, t9⟩ := hT
    refine ⟨fun o => ?_, fun o => ?_⟩
    · rw [← t8 o]; exact view_other _ _ _ (ne3 ⟨8, o⟩ (by decide : (8 : Region) ≠ rStack))
    · rw [← t9 o]; exact view_other _ _ _ (ne3 ⟨9, o⟩ (by decide : (9 : Region) ≠ rStack))
  have hK := hk c inp (ecomb eP σK mK) σK mK orc hwK hTK (by rw [k2]; exact hc)
    (by rw [k9]; omega) hinK
  dsimp only at hK
  obtain ⟨kh, ke, kt, kfoot, kout, kregs⟩ := hK
  generalize hF : chainRun mK orc c (links.map specOf) (mapState (ecomb eP σK mK) σK entryW) = F
    at kh ke kt kfoot kout kregs
  have hcK : callChain mem0c orc c (links.map specOf) (pushRet (alignStep mem0c orc
        (run pre 4 mem0c orc 9 (mapState env σ wEntry)))) =
      { fr (Lm ++ Lb) F with pc := 0, halted := false, tail := none } := by
    simp only [callChain]
    rw [hcall, chainRun_fr, mapState_nOnly eP (ecomb eP σK mK) σK (fun _ => rfl) entryW entryW_nOnly]
    rw [hF]
  -- the epilogue
  obtain ⟨hr3, hr5, hr12, hr14, hr13, hr15, hr4⟩ := kregs
  have hlen : 5 < F.gpr.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hr12; omega
  let S : CState := { fr (Lm ++ Lb) F with pc := 0, halted := false, tail := none }
  have hFnot : ∀ (a : Addr Int), (a.region = rStack → σ 10 ≤ a.off) → a.region = rStack →
      ∀ p ∈ F.mem, p.1 ≠ a := by
    intro a ha har p hp heq
    rcases kfoot p hp with ⟨h1, _⟩ | ⟨h1, h2, h3⟩
    · rw [heq] at h1; rw [har] at h1; exact absurd h1 (by decide)
    · rw [heq] at h3; rw [k9] at h3; have := ha har; omega
  have hbp : ∀ k : Nat, k < 8 → readCell mem0c S ((⟨rStack, σ 9 - 2056 + 2048⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rStack, σ 6⟩ k) := by
    intro k hk8
    apply readCell_some
    show lookup _ (F.mem ++ (Lm ++ Lb)) = _
    rw [plusI_nat, lookup_app_right _ _ _ (hFnot _ (fun _ => by simp only; omega) rfl)]
    rw [lookup_app_right _ _ _ (by
      intro p hp heq; have := hLm p hp; rw [heq] at this; simp only at this; omega)]
    have hl := lookup_hom eP σ _ Kpre.mem _ (lkIs_sound _ _ _ (bp_lk k hk8))
    simp only [mapAddr, sAt_eval, Option.map_some, mapCell, Lin.eval_sym] at hl
    rw [show (⟨rStack, σ 9 - 2056 + 2048 + (k : Int)⟩ : Addr Int) = ⟨rStack, -8 + k + σ 9⟩ by congr 1; omega]
    exact hl
  have hret : ∀ k : Nat, k < 8 → readCell mem0c S ((⟨rStack, σ 9 - 2056 + 2048 + 8⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rRet, 0⟩ k) := by
    intro k hk8
    rw [plusI_nat, readCell_none]
    · obtain ⟨_, hret0, _, _⟩ := hw
      rw [show (⟨rStack, σ 9 - 2056 + 2048 + 8 + (k : Int)⟩ : Addr Int) = ⟨rStack, σ 9 + (k : Int)⟩ by congr 1; omega]
      rw [hret0 k (by omega) (by omega)]; rfl
    · show lookup _ (F.mem ++ (Lm ++ Lb)) = _
      rw [lookup_app_right _ _ _ (hFnot _ (fun _ => by simp only; omega) rfl)]
      apply lookup_none_ne
      intro p hp heq
      rcases List.mem_append.mp hp with h | h
      · have := hLm p h; rw [heq] at this; simp only at this; omega
      · have := hLb p h; rw [heq] at this; simp only at this; omega
  have h3S : S.getG 3 = .ptr ⟨rStack, σ 9 - 2056⟩ := by
    show F.getG 3 = _; rw [getG_of _ _ _ hr3, k5]
  obtain ⟨ph, pe, pt, pm, p4, p5⟩ := post_run mem0c orc S (σ 9 - 2056) ⟨rStack, σ 6⟩ rfl rfl hlen h3S hbp hret
  have hw' : fin = run post 4 mem0c orc 4 S := by
    show run post 4 mem0c orc 4 (callChain mem0c orc c (links.map specOf) (pushRet (alignStep mem0c orc
      (run pre 4 mem0c orc 9 (mapState env σ wEntry))))) = _
    rw [hcK]
  rw [hw']
  refine ⟨ph, pe.trans ke, pt, ?_, p5, ?_, ?_⟩
  · rw [p4, show σ 9 - 2056 + 2048 + 8 + 8 = σ 9 + 8 by omega]
  · rw [pm]
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases kfoot p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, by rw [k1] at h2; exact h2, by rw [k1] at h3; exact h3⟩
      · exact Or.inr ⟨h1, by rw [k9] at h2; omega, by rw [k9] at h3; omega⟩
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨a, b, d⟩ := hLm p h'; exact Or.inr ⟨a, by omega, by omega⟩
      · obtain ⟨a, b, d⟩ := hLb p h'; exact Or.inr ⟨a, by omega, by omega⟩
  · rw [pm]
    intro n i b hn' hi hb
    obtain ⟨x, hx, hv⟩ := kout n i b hn' hi hb
    rw [k1] at hx
    exact ⟨x, lookup_app_left _ _ _ _ hx, hv⟩

/-! ## `HashtreeHash` on avx2 hardware -/

/-- **`HashtreeHash` (linux/amd64, go1.26) on avx2 hardware, every count**: the `CALL` enters
`hashtree_sha256_avx2_x8`, the machine follows its tail calls into avx_x4 and avx_x1 (each with
its own table), and the wrapper returns via `RET` with rsp = `SPe + 8` and the caller's rbp,
writes only output bytes and `[SPe - 2056, SPe)`, and every output byte is the SHA-256 byte of
its block.  Conditional only on R2c's output contracts `TurnOut8`, `TurnOut8Last` (proved on
research/formal-r2c-x16out) and `TurnOut4Last`. -/
theorem wrapper_avx2_chain (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last)
    (c : Nat) (inp : Nat → Hashtree.Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW Hashtree.Kernels.X86.AvxX4.rodata argCells env σ mem0c) (he : EnvMem env σ mem0c)
    (hT : Tables mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    let fin := wrapRunC links8 mem0c orc c (mapState env σ wEntry)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem :=
  wrapper_chain links8 D8L (chainSpec8 hT8 hT8L hT4L) (by unfold D8L; decide) c inp env σ mem0c orc
    hw he hT hc hin hA

end Hashtree.Proofs.WrapperAmd64Chain
