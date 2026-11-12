import Hashtree.Proofs.WrapperPre
import Hashtree.Proofs.ShaniW
import Hashtree.Proofs.AvxX1W
import Hashtree.Kernels.X86.Avx512X16
import Hashtree.Kernels.X86.Avx2X8
import Hashtree.Kernels.X86.AvxX1

/-!
# Our linux/amd64 wrapper `HashtreeHash` with its kernels

The wrapper's machine code (go1.26, `Kernels/X86/WrapperLinux.lean`) runs: the prefix `pre`
(symbolically, one checked slice), the alignment `ANDQ $-32, SP` (concretely, `alignStep`), the
dispatch on the three flag bytes, the call (`callK`: push a return marker, run the kernel until it
returns), and the epilogue `post` (concretely).  A kernel enters through its contract `KSpec`
(the shape of `ShaniW.correctW`: from the wrapper's call state `entryW`, with an entry-stack-
relative footprint of depth `D`).  `wrapper_correct`: for every kernel meeting its contract with
`D ≤ 2009`, the call returns to the caller with `RET`, rsp = `SPe + 8`, the caller's rbp restored,
every output byte the SHA-256 byte of its block, and every write either an output byte or a byte
of the wrapper's own 2048-byte frame plus its saved rbp, `[SPe - 2056, SPe)`.

Not modelled (each stated where it enters): the TLS load of g (`MOVQ FS:-8, R14`, a no-op under
ABIInternal), the stack check (assumed to pass; morestack is not covered), the `CMPB`/`JE` dispatch
(`pick`), the flags at the kernel entry (none — every kernel sets flags before reading them, which
its own proof checks), and `CALL` (`callK`).
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WrapperAmd64
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.WrapperLinux

/-! ## The kernel contract -/

/-- Every logged write is an output byte in `[ob, ob + len)` or a stack byte in `[sp - D, sp)`. -/
def Foot (sp : Int) (D : Nat) (ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ sp - D ≤ p.1.off ∧ p.1.off < sp)

/-- A kernel's contract at the wrapper's call state: for every count, from `entryW` on a memory with
its rodata, the return address at `σ 9` and the input bytes, it returns after `steps c` instructions
without a model error, its writes are output bytes and stack bytes `[σ 9 - D, σ 9)`, the outputs are
SHA-256 of the blocks, and the callee-saved registers and rsp are restored (`ShaniW.RegsOk`). -/
def KSpec (kprog : Array Instr) (rodata : List Nat) (steps : Nat → Nat) (D : Nat) : Prop :=
  ∀ (c : Nat) (inp : Nat → Spec.Byte) (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), WfMemW rodata [] env0 σ mem0c → EnvMem env0 σ mem0c → σ 2 = c →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let fin := run kprog 4 mem0c orcC (steps c) (mapState env0 σ entryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ Foot (σ 9) D (σ 1) (32 * c) fin.mem ∧
      ShaniW.OutOk inp (σ 1) c fin.mem ∧ ShaniW.RegsOk env0 σ fin

theorem shani_spec : KSpec Kernels.X86.Shani.prog Kernels.X86.Shani.rodata ShaniW.steps 88 := by
  intro c inp env0 σ mem0c orcC hw he hc hin
  exact ShaniW.correctW c inp env0 σ mem0c orcC hw he hc hin

/-! ## The composition -/

theorem lin10_eval (σ : Nat → Int) (l : Lin) (h : l.c = List.replicate 10 0 ++ [1]) : l.eval σ = l.k + σ 10 := by
  obtain ⟨k, c⟩ := l; simp only at h; subst h; exact l10_eval σ k

theorem linS_eval (σ : Nat → Int) (l : Lin) (h : l.c = stkC) : l.eval σ = l.k + σ 9 := by
  obtain ⟨k, c⟩ := l; simp only at h; subst h; exact sAt_eval σ k

theorem readCell_some (m : Addr Int → Cell W32 Int) (s : CState) (a : Addr Int) (c : Cell W32 Int)
    (h : lookup a s.mem = .ok (some c)) : readCell m s a = .ok c := by simp [readCell, h]

theorem readCell_none (m : Addr Int → Cell W32 Int) (s : CState) (a : Addr Int)
    (h : lookup a s.mem = .ok none) : readCell m s a = .ok (m a) := by simp [readCell, h]

theorem plusI_nat (r : Region) (o : Int) (k : Nat) : (⟨r, o⟩ : Addr Int).plusI k = ⟨r, o + k⟩ := by
  simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]

/-- **The wrapper with any kernel that meets its contract** (stack depth `D ≤ 2009`).  From the
wrapper's ABI0 entry (`wEntry`: rsp = `SPe` = `σ 9`, return address at `SPe`, arguments above it),
on a memory with the kernel's rodata and the input bytes, with `σ 10` naming the aligned call rsp:
`HashtreeHash` returns via `RET` with rsp = `SPe + 8` and the caller's rbp, every write is an output
byte or a byte of `[SPe - 2056, SPe)` (its frame and saved rbp; the caller's frame is untouched), and
every output byte is the SHA-256 byte of its block. -/
theorem wrapper_kernel (kprog : Array Instr) (rodata : List Nat) (steps : Nat → Nat) (D : Nat)
    (hk : KSpec kprog rodata steps D) (hD : D ≤ 2009)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (hw : WfMemW rodata argCells env σ mem0c) (he : EnvMem env σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).halted = true ∧
      (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).err = none ∧
      (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).tail = none ∧
      (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧
      (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).mem ∧
      ShaniW.OutOk inp (σ 1) c (wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry)).mem := by
  have hA1 : σ 10 + 8 ≤ σ 9 - 8 := by omega
  have hA2 : σ 9 - 47 ≤ σ 10 := by omega
  -- the prefix
  have h0 := m0W_rel rodata env σ mem0c hw he
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
  -- the kernel's memory
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
  have hwK : WfMemW rodata [] (ecomb eP σK mK) σK mK := by
    obtain ⟨hro, _, hinw, _⟩ := hw
    refine ⟨fun o => (hmK4 o).trans (hro o), hmKR, fun o => ?_, fun k c hl => by simp [plookup] at hl⟩
    rw [hmKI]; exact hinw o
  have hinK : ∀ o : Nat, mK ⟨rIn, σK 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
    intro o; rw [hmKI, k0]; exact hin o
  obtain ⟨kh, ke, kt, kfoot, kout, kregs⟩ :=
    hk c inp (ecomb eP σK mK) σK mK orc hwK (envMem_ecomb _ _ _) (by rw [k2]; exact hc) hinK
  generalize hF : run kprog 4 mK orc (steps c) (mapState (ecomb eP σK mK) σK entryW) = F at kh ke kt kfoot kout kregs
  have hcK : callK kprog (steps c) mem0c orc (alignStep mem0c orc (run pre 4 mem0c orc 9 (mapState env σ wEntry))) =
      { fr (Lm ++ Lb) F with pc := 0, halted := false } := by
    simp only [callK]
    rw [hcall, run_fr, mapState_nOnly eP (ecomb eP σK mK) σK (fun _ => rfl) entryW entryW_nOnly]
    show { fr (Lm ++ Lb) (run kprog 4 mK orc (steps c) _) with pc := 0, halted := false } = _
    rw [hF]
  -- the epilogue
  obtain ⟨hr3, hr5, hr12, hr14, hr13, hr15, hr4⟩ := kregs
  have hlen : 5 < F.gpr.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hr12; omega
  let S : CState := { fr (Lm ++ Lb) F with pc := 0, halted := false }
  have hFnot : ∀ (a : Addr Int), (a.region = rStack → σ 10 ≤ a.off) → a.region = rStack → ∀ p ∈ F.mem, p.1 ≠ a := by
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
  have hw' : wrapRun kprog (steps c) mem0c orc (mapState env σ wEntry) = run post 4 mem0c orc 4 S := by
    simp only [wrapRun]; rw [hcK]
  rw [hw']
  refine ⟨ph, pe.trans ke, pt.trans kt, ?_, p5, ?_, ?_⟩
  · rw [p4]; congr 2; omega
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

/-! ## The dispatch -/

def kprogOf : Kern → Array Instr
  | .shani => Kernels.X86.Shani.prog | .avx512 => Kernels.X86.Avx512X16.prog
  | .avx2 => Kernels.X86.Avx2X8.prog | .avx1 => Kernels.X86.AvxX1.prog

def krodataOf : Kern → List Nat
  | .shani => Kernels.X86.Shani.rodata | .avx512 => Kernels.X86.Avx512X16.rodata
  | .avx2 => Kernels.X86.Avx2X8.rodata | .avx1 => Kernels.X86.AvxX1.rodata

/-- The contract of a kernel with some step count and a stack depth that fits the wrapper's frame. -/
def Fits (k : Kern) : Prop := ∃ (steps : Nat → Nat) (D : Nat), D ≤ 2009 ∧ KSpec (kprogOf k) (krodataOf k) steps D

theorem fits_shani : Fits .shani := ⟨ShaniW.steps, 88, by decide, shani_spec⟩

theorem avx1_spec : KSpec Kernels.X86.AvxX1.prog Kernels.X86.AvxX1.rodata AvxX1W.steps 200 := by
  intro c inp env0 σ mem0c orcC hw he hc hin
  exact AvxX1W.correctW c inp env0 σ mem0c orcC hw he hc hin

theorem fits_avx1 : Fits .avx1 := ⟨AvxX1W.steps, 200, by decide, avx1_spec⟩

/-- **`HashtreeHash` (linux/amd64, go1.26) is correct** for whichever kernel the three feature bytes
select, given the contracts of the two kernels not yet proved at the wrapper's call state
(`hAvx512`, `hAvx2` — open assumptions; SHA-NI's and avx_x1's are proved, `fits_shani`, `fits_avx1`). -/
theorem wrapper_correct (hasShani hasAVX512 hasAVX2 : Bool)
    (hAvx512 : Fits .avx512) (hAvx2 : Fits .avx2) :
    let k := pick hasShani hasAVX512 hasAVX2
    ∃ steps : Nat → Nat, ∀ (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
      (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool),
      WfMemW (krodataOf k) argCells env σ mem0c → EnvMem env σ mem0c → σ 2 = c →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32 →
      let fin := wrapRun (kprogOf k) (steps c) mem0c orc (mapState env σ wEntry)
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧
        fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧ Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
        ShaniW.OutOk inp (σ 1) c fin.mem := by
  intro k
  have hf : Fits k := by
    simp only [k, pick]
    split
    · exact fits_shani
    · split
      · exact hAvx512
      · split
        · exact hAvx2
        · exact fits_avx1
  obtain ⟨steps, D, hD, hs⟩ := hf
  exact ⟨steps, fun c inp env σ mem0c orc hw he hc hin hA =>
    wrapper_kernel _ _ steps D hs hD c inp env σ mem0c orc hw he hc hin hA⟩

/-! ## The hypotheses are satisfiable -/

def argSpec (k : Int) : Cell E Lin :=
  if k < 16 then .pb ⟨rOut, Lin.sym 1⟩ (k - 8).toNat
  else if k < 24 then .pb ⟨rIn, Lin.sym 0⟩ (k - 16).toNat
  else .pb ⟨rNum, Lin.sym 2⟩ (k - 24).toNat

theorem argCells_spec : ∀ p ∈ argCells, 8 ≤ p.1 ∧ p.1 < 32 ∧ p.2 = argSpec p.1 := by decide +kernel

/-- A concrete memory meeting the wrapper's `WfMemW`: rodata, the return address at `SPe`, the three
argument slots, the input bytes. -/
def cmemWr (rodata : List Nat) (σ : Nat → Int) (inp : Int → W32) : Addr Int → Cell W32 Int := fun a =>
  if a.region = 4 then .dat (BitVec.ofNat 32 (rodata.getD a.off.toNat 0)) 0
  else if a.region = rStack then
    if σ 9 ≤ a.off ∧ a.off < σ 9 + 8 then .pb ⟨rRet, 0⟩ (a.off - σ 9).toNat
    else if σ 9 + 8 ≤ a.off ∧ a.off < σ 9 + 32 then
      mapCell (fun _ => 0) σ (argSpec (a.off - σ 9))
    else .dat 0 0
  else if a.region = rIn then .dat (inp a.off) 0
  else .dat 0 0

theorem wrapper_hyps_sat (rodata : List Nat) (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ0 : Nat → Int)
    (hc : σ0 2 = c) :
    let σ : Nat → Int := fun i => if i = 10 then (σ0 9 - 8) - (σ0 9 - 8) % 32 - 8 else σ0 i
    let m := cmemWr rodata σ (fun x => (inp (x - σ 0).toNat).zeroExtend 32)
    WfMemW rodata argCells (ecomb env σ m) σ m ∧ EnvMem (ecomb env σ m) σ m ∧ σ 2 = c ∧
      (∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) ∧
      σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32 := by
  intro σ m
  refine ⟨⟨fun o => ?_, fun k h1 h2 => ?_, fun o => ?_, fun k cl hl h8 _ => ?_⟩, envMem_ecomb _ _ _, ?_, fun o => ?_, ?_⟩
  · simp [m, cmemWr]
  · simp only [m, cmemWr, rStack, show (3 : Region) ≠ 4 from by decide, ite_false, ite_true]
    rw [if_pos ⟨by omega, by omega⟩]; congr 2; omega
  · simp only [m, cmemWr, rIn, rStack, show (1 : Region) ≠ 4 from by decide, show (1 : Region) ≠ 3 from by decide,
      ite_false, ite_true, cellX]
  · obtain ⟨h1, h2, h3⟩ := argCells_spec _ (plookup_mem k argCells cl hl)
    simp only at h1 h2 h3
    subst h3
    simp only [m, cmemWr, rStack, show (3 : Region) ≠ 4 from by decide, ite_false, ite_true]
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, show σ 9 + k - σ 9 = k by omega]
    simp only [argSpec]
    split <;> (try split) <;> simp [mapCell, mapAddr, Lin.eval_sym]
  · show σ0 2 = c; exact hc
  · simp only [m, cmemWr, rIn, rStack, show (1 : Region) ≠ 4 from by decide, show (1 : Region) ≠ 3 from by decide,
      ite_false, ite_true]
    congr 3; omega
  · simp only [σ, show (10 : Nat) = 10 from rfl, ite_true, show (9 : Nat) ≠ 10 from by decide, ite_false]; omega

end Hashtree.Proofs.WrapperAmd64
