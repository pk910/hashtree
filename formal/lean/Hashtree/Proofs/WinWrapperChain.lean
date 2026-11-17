import Hashtree.Proofs.WinChainRegions

/-!
# R5: the windows wrapper calling the shipped tail chain

`WinWrapper.wrapRunW` models the wrapper's `CALL` with `callK`: one kernel, its rodata at
region 4, and a pending tail call is dropped.  That fits the two terminal kernels (shani, avx_x1)
but not the shipped dispatch targets `hashtree_sha256_avx512_x16` and `hashtree_sha256_avx2_x8`,
which end in `jb`/`jmp` tail calls into the next kernel.  This file states the wrapper with the
chain-aware call (`X86Chain.callChain`) and ties the windows chain theorem
(`WinChainRegions.win_chain_correct_regions`) to it.

* `wrapRunWC Fr links`: the wrapper text (`pre Fr`, the alignment, the `CALL`) with the call
  following the tail calls through `links`, then the epilogue `post Fr`.  `chainRun` reads only
  the links (`chainRun_links`), so the wrapper is stated without the proof's pre/post conditions.
* `links512` / `links8`: the chains the binary executes from the two chain dispatch targets —
  the tail instructions name exactly these links (`WinChain.win_chain_tails`), each with its own
  rodata table: avx512_x16 at region 7, avx2_x8 at 8, avx_x4 at 4, avx_x1 at 9.
* `Tables`: the table layout — every kernel's table present at once, in its own region.  This is
  the layout of the shipped image (four distinct rodata symbols); `withTables` builds it from any
  memory, and `withTables_ok` shows it is compatible with the wrapper's other memory hypotheses,
  so the theorems below are not vacuous (unlike `WinChainAll`, whose four region-4 hypotheses
  contradict each other).
* `wrapper_chainW_core` (frame generic) / `wrapper_chainW_fixed` (`$2048`): a chain meeting
  `ChainSpecW` at the call state makes the whole wrapper return correctly.
* `chainSpec512`, `chainSpec8`: the two shipped chains meet `ChainSpecW` (from the per-link
  clauses, conditional on R2c's `TurnOut8W`/`TurnOut8WLast`/`TurnOut4W`/`TurnOut4WLast`).
* `wrapper_avx512_chain`, `wrapper_avx2_chain`: `HashtreeHash` (fixed frame) on the avx512 and
  avx2 dispatch targets returns, restores `rsp`/`rbp`/`r8`, writes only output bytes and
  `[SPe - 2056, SPe)`, and every output block is SHA-256 of its input block.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000

namespace Hashtree.Proofs.WinWrapperChain

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Proofs.X86Chain
open Hashtree.Proofs.WinChain (p512 p8 p4 p1)
open Hashtree.Proofs.WinWrapper
open Hashtree.Proofs.WrapperAmd64 (m0W m0W_rel l10 l10_eval sAt_eval getG_of pushRet
  argCells lkIs lkIs_sound)
open Hashtree.Proofs.WinAvx512Bridge (PostLink PreLink)
open Hashtree.Proofs.WinAvx2X8Link (U s8 rodata8)
open Hashtree.Proofs.WinAvxX4Link (rodata4W)
open Hashtree.Proofs.WinChainAll (DW P4 P1 s4 postLink_mono preLink_mono wf_env)
open Hashtree.Proofs.WinChainRegions (specsR win_chain_correct_regions win_KSpecC_regions
  clause_at fix7 fix8 fix9 P4_ren)
open Hashtree.Proofs.WinLinkSwap (Fix swap_mem_wf swap_mem_in envSwap envSwap_mem
  mapState_envSwap state_entryWin postLink_ren)
open Hashtree.Proofs.WinAvx2X8WOut (TurnOut8W TurnOut8WLast)
open Hashtree.Proofs.WinAvxX4WOut (TurnOut4W TurnOut4WLast)

/-! ## The chain call reads only the links -/

/-- A link with trivial conditions: what the machine runs, nothing the proof assumes. -/
def specOf (l : Link) : Spec := ⟨l, fun _ => True, fun _ => True⟩

theorem chainRun_links (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (c : Nat) :
    ∀ (specs specs' : List Spec), specs.map Spec.link = specs'.map Spec.link →
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

/-- The whole wrapper call for frame `Fr`: prologue, alignment, the `CALL` pushing the return
marker and running the tail chain `links` (each link at its own rodata region), epilogue. -/
def wrapRunWC (Fr : Int) (links : List Link) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (c : Nat) (s : CState) : CState :=
  run (post Fr) 4 m orc 5
    (callChain m orc c (links.map specOf) (pushRet (alignStep m orc (run (pre Fr) 4 m orc 9 s))))

/-- The shipped chain from `hashtree_sha256_avx512_x16`: the step function of each link is the
fuel for the blocks it receives (`c % 16`, `c % 8`, `c % 4` remaining). -/
def links512 : List Link :=
  [ ⟨"hashtree_sha256_avx512_x16", p512, 7, Hashtree.Proofs.Avx512X16WLoop.steps⟩,
    ⟨"hashtree_sha256_avx2_x8", p8, 8, fun c => s8 (c % 16)⟩,
    ⟨"hashtree_sha256_avx_x4", p4, 4, fun c => s4 (c % 8)⟩,
    ⟨"hashtree_sha256_avx_x1", p1, 9, fun c => Hashtree.Proofs.WinAvxX1W.steps (c % 4)⟩ ]

/-- The shipped chain from `hashtree_sha256_avx2_x8` (the avx2 dispatch target). -/
def links8 : List Link :=
  [ ⟨"hashtree_sha256_avx2_x8", p8, 8, s8⟩,
    ⟨"hashtree_sha256_avx_x4", p4, 4, fun c => s4 (c % 8)⟩,
    ⟨"hashtree_sha256_avx_x1", p1, 9, fun c => Hashtree.Proofs.WinAvxX1W.steps (c % 4)⟩ ]

theorem links512_names : links512.map Link.name =
    ["hashtree_sha256_avx512_x16", "hashtree_sha256_avx2_x8", "hashtree_sha256_avx_x4",
     "hashtree_sha256_avx_x1"] := rfl

theorem links512_regions : links512.map Link.ro = [7, 8, 4, 9] := rfl

/-! ## The table layout -/

/-- The rodata of the three other chain kernels, each in its own region (avx_x4's is region 4,
part of the wrapper's `WfMemW rodata4W argCells`). -/
def Tables (m : Addr Int → Cell W32 Int) : Prop :=
  (∀ o, m ⟨7, o⟩ = .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86Win.Avx512X16.rodata.getD o.toNat 0)) 0) ∧
  (∀ o, m ⟨8, o⟩ = .dat (BitVec.ofNat 32 (rodata8.getD o.toNat 0)) 0) ∧
  (∀ o, m ⟨9, o⟩ = .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86Win.AvxX1.rodata.getD o.toNat 0)) 0)

/-- Lay the three tables into regions 7, 8, 9 of any memory. -/
def withTables (m : Addr Int → Cell W32 Int) : Addr Int → Cell W32 Int := fun a =>
  if a.region = 7 then .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86Win.Avx512X16.rodata.getD a.off.toNat 0)) 0
  else if a.region = 8 then .dat (BitVec.ofNat 32 (rodata8.getD a.off.toNat 0)) 0
  else if a.region = 9 then .dat (BitVec.ofNat 32 (Hashtree.Kernels.X86Win.AvxX1.rodata.getD a.off.toNat 0)) 0
  else m a

theorem withTables_tables (m : Addr Int → Cell W32 Int) : Tables (withTables m) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem withTables_other (m : Addr Int → Cell W32 Int) (a : Addr Int) (h7 : a.region ≠ 7)
    (h8 : a.region ≠ 8) (h9 : a.region ≠ 9) : withTables m a = m a := by
  simp [withTables, h7, h8, h9]

/-- **Non-vacuity of the layout**: any memory meeting the wrapper's avx_x4 hypotheses (rodata in
region 4, the wrapper's argument cells, the return marker, the input bytes) still meets them
with the other three tables laid in (the environment re-read from the new memory), so the chain
theorems' memory hypotheses hold together. -/
theorem argCells_env (e e' : Key → W32) (σ : Nat → Int) (k : Int) (c : Cell E Lin)
    (h : plookup k argCells = some c) : mapCell e σ c = mapCell e' σ c := by
  have hm := plookup_mem k argCells c h
  simp only [argCells, List.mem_append, List.mem_map, List.mem_range] at hm
  rcases hm with (⟨j, _, hj⟩ | ⟨j, _, hj⟩) | ⟨j, _, hj⟩ <;>
    (simp only [Prod.mk.injEq] at hj; rw [← hj.2]; rfl)

theorem withTables_ok (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hw : WfMemW rodata4W argCells env σ m)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    WfMemW rodata4W argCells (ecomb env σ (withTables m)) σ (withTables m) ∧
      EnvMem (ecomb env σ (withTables m)) σ (withTables m) ∧ Tables (withTables m) ∧
      (∀ o : Nat, withTables m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have o4 : ∀ o, withTables m ⟨4, o⟩ = m ⟨4, o⟩ := fun o =>
    withTables_other m _ (show (4 : Region) ≠ 7 by decide) (show (4 : Region) ≠ 8 by decide)
      (show (4 : Region) ≠ 9 by decide)
  have oS : ∀ o, withTables m ⟨rStack, o⟩ = m ⟨rStack, o⟩ := fun o =>
    withTables_other m _ (show (rStack : Region) ≠ 7 by decide) (show (rStack : Region) ≠ 8 by decide)
      (show (rStack : Region) ≠ 9 by decide)
  have oI : ∀ o, withTables m ⟨rIn, o⟩ = m ⟨rIn, o⟩ := fun o =>
    withTables_other m _ (show (rIn : Region) ≠ 7 by decide) (show (rIn : Region) ≠ 8 by decide)
      (show (rIn : Region) ≠ 9 by decide)
  refine ⟨⟨fun o => (o4 o).trans (h1 o), fun k a b => (oS _).trans (h2 k a b),
    fun o => by rw [oI]; exact h3 o, fun k c hl hk hc => ?_⟩, envMem_ecomb _ _ _,
    withTables_tables m, fun o => (oI _).trans (hin o)⟩
  rw [oS, h4 k c hl hk hc]
  exact argCells_env env _ σ k c hl

/-! ## The chain contract at the call state -/

/-- What a tail chain must deliver from the wrapper's call state `entryWin` (cf. `KSpecW` for a
single kernel): for every count, on a memory with the layout, the return marker and the input
bytes, the chain ends without a model error and without a pending tail, its writes are output
bytes and stack bytes `[σ 9 - D, σ 9)`, the outputs are SHA-256 of the blocks, and the Win64
callee-saved registers and `rsp` are restored. -/
def ChainSpecW (links : List Link) (D : Nat) : Prop :=
  ∀ (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (orcC : Nat → Bool),
    WfMemW rodata4W [] env0 σ m → EnvMem env0 σ m → Tables m → σ 2 = c → σ 9 % 16 = 8 →
    (∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let f := chainRun m orcC c (links.map specOf) (mapState env0 σ entryWin)
    f.err = none ∧ f.tail = none ∧ PostLink σ c inp D f

theorem wfAt_of (r : Region) (rodata : List Nat) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata4W [] env σ m)
    (hr : ∀ o, m ⟨r, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) :
    WfMemAtW r rodata [] env σ m := by
  obtain ⟨_, h2, h3, _⟩ := hw
  exact ⟨hr, h2, h3, fun k c h _ _ => by simp [plookup] at h⟩

/-- **The shipped avx512_x16 chain meets the chain contract** (all four links, each table in
its own region). -/
theorem chainSpec512 (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (hT4 : TurnOut4W)
    (hT4L : TurnOut4WLast) : ChainSpecW links512 DW := by
  intro c inp env σ m orcC hw _ hT hc habi hin
  obtain ⟨t7, t8, t9⟩ := hT
  have h := win_chain_correct_regions env σ c inp hT8 hT8L hT4 hT4L m orcC
    (wfAt_of 7 _ env σ m hw t7) (wfAt_of 8 _ env σ m hw t8) hw (wfAt_of 9 _ env σ m hw t9) hc habi hin
  show (chainRun m orcC c (links512.map specOf) (mapState env σ entryWin)).err = none ∧ _
  rw [chainRun_links m orcC c (links512.map specOf) (specsR env σ c inp) rfl]
  exact h

/-! ## The avx2 dispatch: avx2_x8 called from the wrapper -/

/-- The avx2_x8 link entered at the call state, at region 8 (the head clause of `links8`). -/
theorem clause8E (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (env : Key → W32) (σ : Nat → Int)
    (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat) (inp : Nat → Byte)
    (hw8 : WfMemAtW 8 rodata8 [] env σ m0) (hc : σ 2 = c) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, s = mapState env σ entryWin →
      let f := run p8 8 m0 orcC (s8 c) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp DW f) ∨
         (f.tail = some "hashtree_sha256_avx_x4" ∧ P4 σ c inp (resume f))) := by
  let m8 := (swap 4 8).mem m0
  let e8 := envSwap env σ m8
  have h4 : ∀ s, s = mapState e8 σ entryWin →
      let f := run p8 4 m8 orcC (s8 c) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp DW f) ∨
         (f.tail = some "hashtree_sha256_avx_x4" ∧ P4 σ c inp (resume f))) := by
    intro s hs
    subst hs
    have h := Hashtree.Proofs.WinChainAll.callSpec8 hT8 hT8L e8 σ m8 orcC c inp
      (wf_env _ env e8 σ m8 (swap_mem_wf 8 fix8 _ env σ m0 hw8)) (envSwap_mem env σ m8) hc habi
      (swap_mem_in 8 fix8 m0 σ inp hin)
    obtain ⟨herr, hcase⟩ := h
    refine ⟨herr, ?_⟩
    rcases hcase with ⟨_, ht, hp⟩ | ⟨_, ht, e', hp⟩
    · exact Or.inl ⟨ht, postLink_mono σ c inp (by decide) _ hp⟩
    · exact Or.inr ⟨ht, e', preLink_mono e' σ c _ _ inp (by decide) (fun x hx => hx) _ hp⟩
  exact clause_at 8 fix8 (by decide) (by decide) p8 (s8 c) m0 orcC
    (fun s => s = mapState env σ entryWin) (fun s => s = mapState e8 σ entryWin)
    (PostLink σ c inp DW) (P4 σ c inp) "hashtree_sha256_avx_x4"
    (fun s hs => by rw [hs, state_entryWin fix8, mapState_envSwap])
    (fun f hf => postLink_ren fix8 σ c inp DW f hf) (P4_ren σ c inp 8 fix8) h4

/-- **The shipped avx2_x8 chain meets the chain contract.** -/
theorem chainSpec8 (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (hT4 : TurnOut4W)
    (hT4L : TurnOut4WLast) : ChainSpecW links8 DW := by
  intro c inp env σ m orcC hw _ hT hc habi hin
  obtain ⟨t7, t8, t9⟩ := hT
  let sp8 : List Spec :=
    ⟨⟨"hashtree_sha256_avx2_x8", p8, 8, s8⟩, (fun s => s = mapState env σ entryWin),
      PostLink σ c inp DW⟩ :: (specsR env σ c inp).drop 2
  have hK : KSpecC m orcC c sp8 :=
    ⟨clause8E hT8 hT8L env σ m orcC c inp (wfAt_of 8 _ env σ m hw t8) hc habi hin,
     (win_KSpecC_regions env σ c inp hT8 hT8L hT4 hT4L m orcC (wfAt_of 7 _ env σ m hw t7)
       (wfAt_of 8 _ env σ m hw t8) hw (wfAt_of 9 _ env σ m hw t9) hc habi hin).2.2⟩
  have h := chain_sound m orcC c sp8 (mapState env σ entryWin) hK rfl
  show (chainRun m orcC c (links8.map specOf) (mapState env σ entryWin)).err = none ∧ _
  rw [chainRun_links m orcC c (links8.map specOf) sp8 rfl]
  obtain ⟨herr, htl, hpost⟩ := h
  refine ⟨herr, htl, ?_⟩
  rcases hpost with h | h | h <;> exact h

/-! ## The wrapper composition (as `WinWrapper.wrapper_kernelW_core`, call = `callChain`) -/

theorem wrapper_chainW_core (Fr : Int) (links : List Link) (D : Nat) (hk : ChainSpecW links D)
    (hlenK : (KpreW Fr).gpr.length = 16)
    (hshape : { KCW Fr with mem := [], assume := [] } = entryWin.substL (tauCW Fr))
    (hsplit : (KCW Fr).mem = (KCW Fr).mem.take 8 ++ (KpreW Fr).mem)
    (hmarker : ∀ p ∈ (KCW Fr).mem.take 8, p.1.region = rStack ∧
      p.1.off.c = List.replicate 10 0 ++ [1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 8)
    (hmlk : ∀ k : Nat, k < 8 →
      lkIs ⟨rStack, l10 k⟩ (KCW Fr).mem (.pb ⟨rRet, Lin.ofInt 0⟩ k) = true)
    (hbpf : ∀ p ∈ (KpreW Fr).mem, p.1.region = rStack ∧ p.1.off.c = stkC ∧
      -8 ≤ p.1.off.k ∧ p.1.off.k < 0)
    (hbplk : ∀ k : Nat, k < 8 →
      lkIs ⟨rStack, sAt (-8 + k)⟩ (KpreW Fr).mem (.pb ⟨rStack, Lin.sym 6⟩ k) = true)
    (hhead : ((⟨rStack, l10 0⟩ : Addr Lin), Cell.pb ⟨rRet, Lin.ofInt 0⟩ 0) ∈
      (KCW Fr).mem.take 8)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (eP : Key → W32)
    (hP : run (pre Fr) 4 mem0c orc 9 (mapState env σ wEntryW) = mapState eP σ (KpreW Fr))
    (hA : alignStep mem0c orc (mapState eP σ (KpreW Fr)) = mapState eP σ (KalW Fr))
    (hsepM : σ 10 + 8 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10)
    (hsepK : σ 10 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 - (D : Int))
    (hw : WfMemW rodata4W argCells env σ mem0c) (_he : EnvMem env σ mem0c) (hT : Tables mem0c)
    (hc : σ 2 = c) (habi : σ 10 % 16 = 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := wrapRunWC Fr links mem0c orc c (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      (∀ p ∈ fin.mem, (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * c) ∨
        (p.1.region = rStack ∧ ((σ 10 - (D : Int) ≤ p.1.off ∧ p.1.off < σ 10) ∨
          (σ 10 ≤ p.1.off ∧ p.1.off < σ 10 + 8) ∨ (σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9)))) ∧
      OutOk inp (σ 1) c fin.mem ∧
      (σ 9 ≤ σ 10 → ∃ p ∈ fin.mem, p.1.region = rStack ∧ p.1.off = σ 10) := by
  let σK := sigmaOf (tauCW Fr) σ
  have k0 : σK 0 = σ 0 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k1 : σK 1 = σ 1 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k2 : σK 2 = σ 2 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k7 : σK 7 = σ 13 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k5 : σK 5 = σ 9 - 8 - Fr := by simp [σK, sigmaOf, tauAt, tauCW, sAt_eval]; omega
  have k9 : σK 9 = σ 10 := by simp [σK, sigmaOf, tauAt, tauCW, l10_eval]
  let f := fun (p : Addr Lin × Cell E Lin) => (mapAddr σ p.1, mapCell eP σ p.2)
  let Lm := (KCW Fr).mem.take 8 |>.map f
  let Lb := (KpreW Fr).mem.map f
  have hLw : (KCW Fr).mem.map f = Lm ++ Lb := by
    show (KCW Fr).mem.map f = ((KCW Fr).mem.take 8).map f ++ (KpreW Fr).mem.map f
    rw [← List.map_append, ← hsplit]
  have hcall : { pushRet (alignStep mem0c orc (run (pre Fr) 4 mem0c orc 9
        (mapState env σ wEntryW))) with pc := 0 } =
      fr (Lm ++ Lb) (mapState eP σK entryWin) := by
    rw [hP, hA, push_homW Fr eP σ hlenK, mapState_reached eP σ (KCW Fr) entryWin (tauCW Fr) hshape]
    show fr ((KCW Fr).mem.map f) _ = _
    rw [hLw]
  -- the call log: marker cells and the saved `rbp`
  have hLm : ∀ p ∈ Lm, p.1.region = rStack ∧ σ 10 ≤ p.1.off ∧ p.1.off < σ 10 + 8 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := hmarker q hq
    simp only [f, mapAddr, lin10_eval σ _ h2, h1]
    exact ⟨trivial, by omega, by omega⟩
  have hLb : ∀ p ∈ Lb, p.1.region = rStack ∧ σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := hbpf q hq
    simp only [f, mapAddr, linS_eval σ _ h2, h1]
    exact ⟨trivial, by omega, by omega⟩
  have hLw3 : ∀ p ∈ Lm ++ Lb, p.1.region = rStack := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact (hLm p h).1
    · exact (hLb p h).1
  have ne3 : ∀ (a : Addr Int), a.region ≠ rStack → ∀ p ∈ Lm ++ Lb, p.1 ≠ a := by
    intro a ha p hp heq; rw [← heq] at ha; exact ha (hLw3 p hp)
  let mK := view (Lm ++ Lb) mem0c
  have hmK4 : ∀ o, mK ⟨4, o⟩ = mem0c ⟨4, o⟩ := fun o =>
    view_other _ _ _ (ne3 ⟨4, o⟩ (by decide : (4 : Region) ≠ rStack))
  have hmKI : ∀ o, mK ⟨rIn, o⟩ = mem0c ⟨rIn, o⟩ := fun o =>
    view_other _ _ _ (ne3 ⟨rIn, o⟩ (by decide : rIn ≠ rStack))
  have hmKR : ∀ k : Int, 0 ≤ k → k < 8 → mK ⟨rStack, σK 9 + k⟩ = .pb ⟨rRet, 0⟩ k.toNat := by
    intro k h1 h2
    have hk' := hmlk k.toNat (by omega)
    have hl := lookup_hom eP σ _ (KCW Fr).mem _ (lkIs_sound _ _ _ hk')
    have ha : mapAddr σ (⟨rStack, l10 k.toNat⟩ : Addr Lin) = ⟨rStack, σK 9 + k⟩ := by
      simp only [mapAddr, l10_eval, k9]; congr 1; omega
    have hc0 : mapCell eP σ (Cell.pb ⟨rRet, Lin.ofInt 0⟩ k.toNat) = .pb ⟨rRet, 0⟩ k.toNat := by
      simp [mapCell, mapAddr, Lin.ofInt, Lin.eval, dotC]
    rw [ha, show (KCW Fr).mem.map (fun p => (mapAddr σ p.1, mapCell eP σ p.2)) = Lm ++ Lb from hLw,
      Option.map_some, hc0] at hl
    simp only [mK, view, hl]
  have hwK : WfMemW rodata4W [] (ecomb eP σK mK) σK mK := by
    obtain ⟨hro, _, hinw, _⟩ := hw
    refine ⟨fun o => (hmK4 o).trans (hro o), hmKR, fun o => ?_, fun k c hl => by simp [plookup] at hl⟩
    rw [hmKI]; exact hinw o
  have hinK : ∀ o : Nat, mK ⟨rIn, σK 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
    intro o; rw [hmKI, k0]; exact hin o
  have hTK : Tables mK := by
    obtain ⟨t7, t8, t9⟩ := hT
    refine ⟨fun o => ?_, fun o => ?_, fun o => ?_⟩
    · rw [← t7 o]; exact view_other _ _ _ (ne3 ⟨7, o⟩ (by decide : (7 : Region) ≠ rStack))
    · rw [← t8 o]; exact view_other _ _ _ (ne3 ⟨8, o⟩ (by decide : (8 : Region) ≠ rStack))
    · rw [← t9 o]; exact view_other _ _ _ (ne3 ⟨9, o⟩ (by decide : (9 : Region) ≠ rStack))
  obtain ⟨ke, kt, kh, kfoot, kout, kregs⟩ :=
    hk c inp (ecomb eP σK mK) σK mK orc hwK (envMem_ecomb _ _ _) hTK (by rw [k2]; exact hc)
      (by rw [k9]; exact habi) hinK
  generalize hF : chainRun mK orc c (links.map specOf) (mapState (ecomb eP σK mK) σK entryWin) = F
    at kh ke kt kfoot kout kregs
  have hcK : callChain mem0c orc c (links.map specOf) (pushRet (alignStep mem0c orc
        (run (pre Fr) 4 mem0c orc 9 (mapState env σ wEntryW)))) =
      { fr (Lm ++ Lb) F with pc := 0, halted := false, tail := none } := by
    simp only [callChain]
    rw [hcall, chainRun_fr, mapState_nOnly eP (ecomb eP σK mK) σK (fun _ => rfl) entryWin entryWin_nOnly]
    rw [hF]
  -- the epilogue
  obtain ⟨hr3, hr5, hr12, hr13, hr14, hr15, hr4⟩ := kregs
  have hlen : 12 < F.gpr.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hr12; omega
  let S : CState := { fr (Lm ++ Lb) F with pc := 0, halted := false, tail := none }
  -- the kernel's writes avoid the wrapper's saved `rbp` and return-address slots
  have hFsep : ∀ p ∈ F.mem, p.1.region = rStack → ¬(σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9 + 8) := by
    intro p hp hreg h
    rcases kfoot p hp with ⟨ho, _, _⟩ | ⟨hs, hlo, hhi⟩
    · rw [ho] at hreg; exact absurd hreg (by decide)
    · rw [k9] at hhi
      rcases hsepK with hk | hk <;> omega
  have hbp : ∀ k : Nat, k < 8 → readCell mem0c S ((⟨rStack, σK 5 + Fr⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rStack, σ 6⟩ k) := by
    intro k hk8
    apply readCell_some
    show lookup _ (F.mem ++ (Lm ++ Lb)) = _
    rw [plusI_nat, lookup_app_right _ _ _ (by
      intro p hp heq
      have hoff : p.1.off = σ 9 - 8 + (k : Int) := by rw [heq]; dsimp only; omega
      refine hFsep p hp ?_ ⟨by omega, by omega⟩
      rw [heq])]
    rw [lookup_app_right _ _ _ (by
      intro p hp heq
      obtain ⟨_, hlo, hhi⟩ := hLm p hp
      have hoff : p.1.off = σ 9 - 8 + (k : Int) := by rw [heq]; dsimp only; omega
      rcases hsepM with hs | hs <;> omega)]
    have hl := lookup_hom eP σ _ (KpreW Fr).mem _ (lkIs_sound _ _ _ (hbplk k hk8))
    simp only [mapAddr, sAt_eval, Option.map_some, mapCell, Lin.eval_sym] at hl
    rw [show (⟨rStack, σK 5 + Fr + (k : Int)⟩ : Addr Int) = ⟨rStack, -8 + (k : Int) + σ 9⟩ by
      congr 1; omega]
    exact hl
  have hret : ∀ k : Nat, k < 8 →
      readCell mem0c S ((⟨rStack, σK 5 + Fr + 8⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rRet, 0⟩ k) := by
    intro k hk8
    rw [plusI_nat, readCell_none]
    · obtain ⟨_, hret0, _, _⟩ := hw
      rw [show (⟨rStack, σK 5 + Fr + 8 + (k : Int)⟩ : Addr Int) = ⟨rStack, σ 9 + (k : Int)⟩ by
        congr 1; omega]
      rw [hret0 k (by omega) (by omega)]; rfl
    · show lookup _ (F.mem ++ (Lm ++ Lb)) = _
      rw [lookup_app_right _ _ _ (by
        intro p hp heq
        have hoff : p.1.off = σ 9 + (k : Int) := by rw [heq]; dsimp only; omega
        refine hFsep p hp ?_ ⟨by omega, by omega⟩
        rw [heq])]
      apply lookup_none_ne
      intro p hp heq
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨_, hlo, hhi⟩ := hLm p h
        have hoff : p.1.off = σ 9 + (k : Int) := by rw [heq]; dsimp only; omega
        rcases hsepM with hs | hs <;> omega
      · obtain ⟨_, hlo, hhi⟩ := hLb p h
        have hoff : p.1.off = σ 9 + (k : Int) := by rw [heq]; dsimp only; omega
        omega
  have h3S : S.getG 3 = .ptr ⟨rStack, σK 5⟩ := by
    show F.getG 3 = _
    rw [getG_of _ _ _ hr3]
  have h12S : S.getG 12 = .ptr ⟨rNum, σ 13⟩ := by
    show F.getG 12 = _
    rw [getG_of _ _ _ hr12]
    simp only [k7]
  obtain ⟨ph, pe, pt, pm, p4, p5, p8⟩ := post_runW mem0c orc S (σK 5) Fr ⟨rStack, σ 6⟩
    (.ptr ⟨rNum, σ 13⟩) rfl rfl hlen h3S h12S hbp hret
  have hw' : wrapRunWC Fr links mem0c orc c (mapState env σ wEntryW) =
      run (post Fr) 4 mem0c orc 5 S := by
    simp only [wrapRunWC]; rw [hcK]
  rw [hw']
  refine ⟨ph, pe.trans ke, pt, ?_, p5, p8, ?_, ?_, ?_⟩
  · rw [p4]; congr 2; omega
  · rw [pm]
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases kfoot p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, by rw [k1] at h2; exact h2, by rw [k1] at h3; exact h3⟩
      · exact Or.inr ⟨h1, Or.inl ⟨by rw [k9] at h2; exact h2, by rw [k9] at h3; exact h3⟩⟩
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨a, b, d⟩ := hLm p h'; exact Or.inr ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩
      · obtain ⟨a, b, d⟩ := hLb p h'; exact Or.inr ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩
  · rw [pm]
    intro n i b hn hi hb
    obtain ⟨x, hx, hv⟩ := kout n i b hn hi hb
    rw [k1] at hx
    exact ⟨x, lookup_app_left _ _ _ _ hx, hv⟩
  · intro h9
    refine ⟨f ((⟨rStack, l10 0⟩ : Addr Lin), Cell.pb ⟨rRet, Lin.ofInt 0⟩ 0), ?_, ?_, ?_⟩
    · rw [pm]
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hhead))
    · simp only [f, mapAddr]
    · simp only [f, mapAddr, l10_eval]; omega


/-- **The wrapper with a chain meeting `ChainSpecW`, fixed frame (`$2048`)**: the Go-facing
contract of `HashtreeHash` as for a single kernel (`wrapper_kernelW_fixed`), with the call
following the tail chain. -/
theorem wrapper_chainW_fixed (links : List Link) (D : Nat) (hk : ChainSpecW links D) (hD : D ≤ 2009)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW rodata4W argCells env σ mem0c) (he : EnvMem env σ mem0c) (hT : Tables mem0c)
    (hc : σ 2 = c) (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    let fin := wrapRunWC fixedFrame links mem0c orc c (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
      OutOk inp (σ 1) c fin.mem := by
  let eP := envAbs env (run (pre fixedFrame) 4 m0W (fun _ => false) 9 wEntryW)
  have hP := (slice_sound env σ m0W mem0c (m0W_rel rodata4W env σ mem0c hw he)
    (pre fixedFrame) 4 (fun _ => false) orc 9 wEntryW (KpreW fixedFrame) [] slicePreW_fixed rfl
    (fun p hp => by rw [KpreW_fixed_assume] at hp; cases hp)).1
  have hAe : alignStep mem0c orc (mapState eP σ (KpreW fixedFrame)) =
      mapState eP σ (KalW fixedFrame) := align_homW_fixed eP σ mem0c orc hA
  have hsepM : σ 10 + 8 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 := by left; omega
  have hsepK : σ 10 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 - (D : Int) := by left; omega
  have habi : σ 10 % 16 = 8 := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ :=
    wrapper_chainW_core fixedFrame links D hk (KpreW_fixed_len) KCW_shape_fixed
      KCW_mem_split_fixed markerW_facts_fixed markerW_lk_fixed bpW_facts_fixed bpW_lk_fixed
      KCW_head_fixed c inp env σ mem0c orc eP hP hAe hsepM hsepK hw he hT hc habi hin
  have hA1 : σ 10 + 8 ≤ σ 9 - 8 := by omega
  have hA2 : σ 9 - 47 ≤ σ 10 := by omega
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8⟩
  intro p hp
  rcases h7 p hp with ⟨ho, a, b⟩ | ⟨hs, h⟩
  · exact Or.inl ⟨ho, a, b⟩
  · rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨hs, by omega, by omega⟩
    · exact Or.inr ⟨hs, by omega, by omega⟩
    · exact Or.inr ⟨hs, by omega, by omega⟩

/-! ## `HashtreeHash` on the two chain dispatch targets -/

/-- **`HashtreeHash` (windows/amd64, fixed frame) on the avx512 dispatch target**: the `CALL`
enters `hashtree_sha256_avx512_x16`, the machine follows its tail calls through avx2_x8, avx_x4
and avx_x1 (each with its own table, `Tables`), and the wrapper returns with `rsp`, `rbp`, `r8`
restored, writes only output bytes and `[SPe - 2056, SPe)`, all `c` outputs SHA-256 of their
blocks.  Conditional only on R2c's output contracts of the two windows W-mode loops. -/
theorem wrapper_avx512_chain (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (hT4 : TurnOut4W)
    (hT4L : TurnOut4WLast)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW rodata4W argCells env σ mem0c) (he : EnvMem env σ mem0c) (hT : Tables mem0c)
    (hc : σ 2 = c) (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    let fin := wrapRunWC fixedFrame links512 mem0c orc c (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
      OutOk inp (σ 1) c fin.mem :=
  wrapper_chainW_fixed links512 DW (chainSpec512 hT8 hT8L hT4 hT4L) (by decide) c inp env σ mem0c
    orc hw he hT hc hin hA

/-- **`HashtreeHash` (windows/amd64, fixed frame) on the avx2 dispatch target**
(`hashtree_sha256_avx2_x8`, then avx_x4 and avx_x1). -/
theorem wrapper_avx2_chain (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (hT4 : TurnOut4W)
    (hT4L : TurnOut4WLast)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW rodata4W argCells env σ mem0c) (he : EnvMem env σ mem0c) (hT : Tables mem0c)
    (hc : σ 2 = c) (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    let fin := wrapRunWC fixedFrame links8 mem0c orc c (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
      OutOk inp (σ 1) c fin.mem :=
  wrapper_chainW_fixed links8 DW (chainSpec8 hT8 hT8L hT4 hT4L) (by decide) c inp env σ mem0c
    orc hw he hT hc hin hA

end Hashtree.Proofs.WinWrapperChain
