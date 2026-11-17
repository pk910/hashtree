import Hashtree.Proofs.WinAvxX4Bridge
import Hashtree.Proofs.WinShaniBridge
import Hashtree.Asm.RunExit

/-!
# R5: the windows chain link `avx_x4 -> avx_x1` — the certificate-independent parts

The windows avx_x4 stream is not a renaming of the linux one (ten xmm saves/restores and one
inserted instruction at windows pc 705), so the link waits for a certificate *of the windows
stream* (`X4WinCert` below: the interface R2's W-mode certificate of
`Kernels.X86Win.AvxX4.prog` must provide).  Everything else is proved here against that
interface: the rodata prefix (`wf_linux_of_win`: the linux certificate's memory hypothesis from
the windows one), the `c = 0` early return (a four-instruction symbolic run from `entryWin`,
`x4_zero_run`, by `run_hom`), the hand-off to the avx_x1 link (`preLink_of_exit`), and the glue
(`KSpecC4_of_cert`): once the certificate exists, the link is one instantiation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Hashtree.Proofs.WinAvxX4Link

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.BodyReads
open Hashtree.Asm.RunAgree Hashtree.Asm.RunExit
open Hashtree.Proofs.X86Chain Hashtree.Proofs.WinChain
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink)
open Hashtree.Proofs.WinAvxX4Bridge (KSpecC4 L1)
open Hashtree.Proofs.WinShaniBridge (stW_len entryWin_gpr1 entryWin_gpr2 entryWin_gpr4 entryWin_gpr8
  entryWin_gpr3 entryWin_gpr5 entryWin_gpr12 entryWin_gpr13 entryWin_gpr14 entryWin_gpr15 getElem?_of_getG)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)

abbrev rodata4W : List Nat := Hashtree.Kernels.X86Win.AvxX4.rodata
abbrev rodata4L : List Nat := Hashtree.Kernels.X86.AvxX4.rodata

/-! ## The rodata prefix: the windows table is the linux table plus 48 zero bytes -/

theorem rodata4_prefix : rodata4W.take 2192 = rodata4L ∧ rodata4W.drop 2192 = List.replicate 48 0 ∧
    rodata4W.length = 2240 ∧ rodata4L.length = 2192 := by decide +kernel

theorem rodata4_getD (o : Nat) : rodata4W.getD o 0 = rodata4L.getD o 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := rodata4_prefix
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases ho : o < 2192
  · rw [← h1, List.getElem?_take_of_lt ho]
  · have hL : rodata4L[o]? = none := List.getElem?_eq_none (by rw [h4]; omega)
    rw [hL]
    by_cases ho' : o < 2240
    · have hd := congrArg (fun l => l[o - 2192]?) h2
      simp only [List.getElem?_drop, List.getElem?_replicate] at hd
      rw [show 2192 + (o - 2192) = o by omega] at hd
      rw [hd, ite_eq_left (by omega)]; rfl
    · rw [List.getElem?_eq_none (by rw [h3]; omega)]

/-- The linux certificate's memory hypothesis follows from the windows one. -/
theorem wf_linux_of_win (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (hw : WfMemW rodata4W [] env σ m) : WfMemW rodata4L [] env σ m := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  exact ⟨fun o => by rw [h1 o, rodata4_getD], h2, h3, h4⟩

/-! ## The `c = 0` path: `nop; cmp r8, 0; jne; ret` -/

abbrev m04 : Addr Lin → Cell E Lin := mem0sW 4 rodata4W []

/-- The symbolic state after the early return (four instructions from the call state). -/
def KZ4 : State E Lin := run p4 4 m04 (fun _ => false) 4 entryWin

theorem KZ4_err : KZ4.err = none := by decide +kernel
theorem KZ4_assume : KZ4.assume = [(.not (.eq ⟨0, [0, 0, 1]⟩ ⟨0, []⟩), false)] := by decide +kernel
theorem KZ4_pc : KZ4.pc = 3 := by decide +kernel
theorem KZ4_halted : KZ4.halted = true := by decide +kernel
theorem KZ4_tail : KZ4.tail = none := by decide +kernel
theorem KZ4_mem : KZ4.mem = [] := by decide +kernel
theorem KZ4_len : KZ4.gpr.length = 16 := by decide +kernel
theorem KZ4_gpr3 : KZ4.gpr[3]? = some (.ptr ⟨rStack, Lin.sym 5⟩) := by decide +kernel
theorem KZ4_gpr4 : KZ4.gpr[4]? = some (.ptr ⟨rStack, sAt 8⟩) := by decide +kernel
theorem KZ4_gpr5 : KZ4.gpr[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by decide +kernel
theorem KZ4_gpr12 : KZ4.gpr[12]? = some (.ptr ⟨rNum, Lin.sym 7⟩) := by decide +kernel
theorem KZ4_gpr13 : KZ4.gpr[13]? = some (.ptr ⟨rNum, Lin.sym 11⟩) := by decide +kernel
theorem KZ4_gpr14 : KZ4.gpr[14]? = some (.ptr ⟨rG, Lin.sym 8⟩) := by decide +kernel
theorem KZ4_gpr15 : KZ4.gpr[15]? = some (.ptr ⟨rNum, Lin.sym 12⟩) := by decide +kernel

/-- The recorded branch condition (`jne` not taken) holds when the count is zero. -/
theorem KZ4_assumeOk (σ : Nat → Int) (hc : σ 2 = 0) : AssumeOk σ KZ4 := by
  intro p hp
  rw [KZ4_assume] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  simp [mapCond, Cond.decideC, Lin.eval, dotC, hc, Ctl.sub]
  try rfl

/-- The windows avx_x4 kernel at count 0 returns after four instructions. -/
theorem x4_zero_run (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemW rodata4W [] env σ m0) (he : EnvMem env σ m0) (hc : σ 2 = 0) :
    run p4 4 m0 orcC 4 (mapState env σ entryWin) = mapState env σ KZ4 :=
  run_hom env σ m04 m0 (mem0RelW_of_wf rodata4W [] env σ m0 hw he) p4 4 (fun _ => false) orcC 4 entryWin
    rfl KZ4_err (KZ4_assumeOk σ hc)

theorem mapState_err' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) : (mapState e τ K).err = K.err := rfl
theorem mapState_tail' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) : (mapState e τ K).tail = K.tail := rfl
theorem mapState_halted' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) : (mapState e τ K).halted = K.halted := rfl
theorem mapState_mem' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (mapState e τ K).mem = K.mem.map (fun p => (mapAddr τ p.1, mapCell e τ p.2)) := rfl
theorem mapState_len' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (mapState e τ K).gpr.length = K.gpr.length := List.length_map ..

/-- The `c = 0` return meets `PostLink` at depth 0. -/
theorem postLink_zero (env : Key → W32) (σ : Nat → Int) (inp : Nat → Spec.Byte) :
    PostLink σ 0 inp 0 (mapState env σ KZ4) := by
  have hlen : (mapState env σ KZ4).gpr.length = 16 := by rw [mapState_len', KZ4_len]
  have hmem : (mapState env σ KZ4).mem = [] := by rw [mapState_mem', KZ4_mem]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mapState_halted', KZ4_halted]
  · intro p hp; rw [hmem] at hp; cases hp
  · intro n i b hn; exact absurd hn (Nat.not_lt_zero _)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getElem?_of_getG _ 3 (by omega), mapState_getG KZ4_gpr3]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 5 (by omega), mapState_getG KZ4_gpr5]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 12 (by omega), mapState_getG KZ4_gpr12]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 13 (by omega), mapState_getG KZ4_gpr13]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 14 (by omega), mapState_getG KZ4_gpr14]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 15 (by omega), mapState_getG KZ4_gpr15]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 4 (by omega), mapState_getG KZ4_gpr4]
      simp [mapVal, mapAddr, sAt_eval]
      omega

/-! ## The certificate interface -/

/-- What a certificate of the windows avx_x4 stream must provide for the link (R2's W-mode
tooling on `Kernels.X86Win.AvxX4.prog`): for every count `c ≠ 0`, from the wrapper call state the
run reaches, after `steps c` instructions, the tail call to avx_x1 with the registers the avx_x1
link reads (`L1`), the Win64 callee-saved registers untouched, a well-shaped vector file (its
contents free, U6-style), and a write log of the finished blocks' outputs and the kernel's own
frame (depth 568, below `σ 9`). -/
structure X4WinCert where
  steps : Nat → Nat
  spec : ∀ (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (c : Nat) (inp : Nat → Spec.Byte),
    WfMemW rodata4W [] env σ m0 → EnvMem env σ m0 → σ 2 = c → c ≠ 0 →
    (∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let f := run p4 4 m0 orcC (steps c) (mapState env σ entryWin)
    f.err = none ∧ f.tail = some "hashtree_sha256_avx_x1" ∧ f.gpr.length = 16 ∧
    f.getG 8 = .ptr ⟨rNum, ((c % 4 : Nat) : Int)⟩ ∧
    f.getG 1 = .ptr ⟨rOut, σ 1 + 32 * ((c - c % 4 : Nat) : Int)⟩ ∧
    f.getG 2 = .ptr ⟨rIn, σ 0 + 64 * ((c - c % 4 : Nat) : Int)⟩ ∧
    f.getG 4 = .ptr ⟨rStack, σ 9⟩ ∧
    (∀ j, j ∈ [3, 5, 6, 7, 12, 13, 14, 15] → f.getG j = (mapState env σ entryWin).getG j) ∧
    (f.vr.length = 32 ∧ ∀ v ∈ f.vr, v.length = 16) ∧
    OutLogW (σ 9) f.mem ∧ Foot (σ 9) 568 (σ 1) (32 * c) f.mem ∧ OutOk inp (σ 1) (c - c % 4) f.mem

/-! ## The hand-off to the avx_x1 link -/

section HandOff
variable (env : Key → W32) (σ : Nat → Int) (c : Nat) (inp : Nat → Spec.Byte)

theorem shift4_ge3 (d r i : Nat) (hi : 3 ≤ i) : shift σ d r i = σ i := by
  simp [shift, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]

/-- The comparison state of `PreLink`. -/
def cmpSt (d r : Nat) (V : List (List W32)) (M' : CLog) : CState :=
  fr M' { mapState env (shift σ d r) entryWin with vr := V }

theorem cmpSt_getG (d r : Nat) (V : List (List W32)) (M' : CLog) {j : Nat} {v : Val E Lin}
    (hj : entryWin.gpr[j]? = some v) : (cmpSt env σ d r V M').getG j = mapVal env (shift σ d r) v := by
  show (mapState env (shift σ d r) entryWin).getG j = _
  exact mapState_getG hj

theorem cmpSt_len (d r : Nat) (V : List (List W32)) (M' : CLog) : (cmpSt env σ d r V M').gpr.length = 16 :=
  stW_len env (shift σ d r)

/-- A preserved register (symbol ≥ 3) agrees with the advanced entry state. -/
theorem preserved_cmp (d r : Nat) (V : List (List W32)) (M' : CLog) (j : Nat)
    (hj : j ∈ [3, 5, 6, 7, 12, 13, 14, 15]) :
    (mapState env σ entryWin).getG j = (cmpSt env σ d r V M').getG j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr3, mapState_getG entryWin_gpr3]
    simp [mapVal, mapAddr, Lin.eval_sym, shift4_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr5, mapState_getG entryWin_gpr5]
    simp [mapVal, mapAddr, Lin.eval_sym, shift4_ge3]
  · have h6 : entryWin.gpr[6]? = some (.num (.var (.n (gId 6 0))) (.var (.n (gId 6 1)))) := by decide +kernel
    rw [cmpSt_getG env σ d r V M' h6, mapState_getG h6]
    rfl
  · have h7 : entryWin.gpr[7]? = some (.num (.var (.n (gId 7 0))) (.var (.n (gId 7 1)))) := by decide +kernel
    rw [cmpSt_getG env σ d r V M' h7, mapState_getG h7]
    rfl
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr12, mapState_getG entryWin_gpr12]
    simp [mapVal, mapAddr, Lin.eval_sym, shift4_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr13, mapState_getG entryWin_gpr13]
    simp [mapVal, mapAddr, Lin.eval_sym, shift4_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr14, mapState_getG entryWin_gpr14]
    simp [mapVal, mapAddr, Lin.eval_sym, shift4_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr15, mapState_getG entryWin_gpr15]
    simp [mapVal, mapAddr, Lin.eval_sym, shift4_ge3]

theorem L1_cases (r : Nat) (hr : r ∈ L1) : r ∈ [8, 4, 2, 1] ∨ r ∈ [3, 5, 6, 7, 12, 13, 14, 15] := by
  rw [show L1 = [4, 3, 8, 6, 7, 5, 12, 13, 14, 15, 1, 2] from Hashtree.Proofs.WinAvxX1Live.live_entry_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  omega

/-- A state with the certificate's exit facts satisfies the avx_x1 link's entry condition. -/
theorem preLink_of_exit (f : CState)
    (hlen : f.gpr.length = 16)
    (h8 : f.getG 8 = .ptr ⟨rNum, ((c % 4 : Nat) : Int)⟩)
    (h1 : f.getG 1 = .ptr ⟨rOut, σ 1 + 32 * ((c - c % 4 : Nat) : Int)⟩)
    (h2 : f.getG 2 = .ptr ⟨rIn, σ 0 + 64 * ((c - c % 4 : Nat) : Int)⟩)
    (h4 : f.getG 4 = .ptr ⟨rStack, σ 9⟩)
    (hcs : ∀ j, j ∈ [3, 5, 6, 7, 12, 13, 14, 15] → f.getG j = (mapState env σ entryWin).getG j)
    (hV : f.vr.length = 32 ∧ ∀ v ∈ f.vr, v.length = 16)
    (hlog : OutLogW (σ 9) f.mem) (hfoot : Foot (σ 9) 568 (σ 1) (32 * c) f.mem)
    (hout : OutOk inp (σ 1) (c - c % 4) f.mem) (herr : f.err = none) :
    PreLink env σ c (c - c % 4) (c % 4) inp 568 L1 (resume f) := by
  refine ⟨f.vr, f.mem, hV, ?_, hlog, hfoot, hout⟩
  show Agree L1 false (resume f) (cmpSt env σ (c - c % 4) (c % 4) f.vr f.mem)
  refine ⟨?_, ?_, rfl, (fun h => by cases h), ?_, rfl, rfl, rfl, ?_⟩
  · intro r hr
    show f.getG r = _
    rcases L1_cases r hr with hT | hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · rw [h8, cmpSt_getG env σ _ _ _ _ entryWin_gpr8]
        simp [mapVal, mapAddr, Lin.eval_sym, shift]
      · rw [h4, cmpSt_getG env σ _ _ _ _ entryWin_gpr4]
        simp [mapVal, mapAddr, sAt_eval, shift4_ge3]
      · rw [h2, cmpSt_getG env σ _ _ _ _ entryWin_gpr2]
        simp [mapVal, mapAddr, Lin.eval_sym, shift]
      · rw [h1, cmpSt_getG env σ _ _ _ _ entryWin_gpr1]
        simp [mapVal, mapAddr, Lin.eval_sym, shift]
    · rw [hcs r hp]; exact preserved_cmp env σ _ _ _ _ r hp
  · show f.gpr.length = _
    rw [hlen, cmpSt_len]
  · show f.mem = ([] : CLog) ++ f.mem
    rfl
  · show f.err = none
    exact herr

end HandOff

/-! ## The link from the interface -/

/-- **The avx_x4 link, from a certificate of the windows stream**: `KSpecC4` with the step
function `4` at `c = 0` (the early return) and the certificate's elsewhere. -/
theorem KSpecC4_of_cert (X : X4WinCert) (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) :
    KSpecC4 (fun c => if c = 0 then 4 else X.steps c) env σ m0 orcC c inp := by
  intro hw he hc hin s hs
  subst hs
  by_cases hc0 : c = 0
  · subst hc0
    simp only [↓reduceIte]
    rw [x4_zero_run env σ m0 orcC hw he hc]
    exact ⟨by rw [mapState_err', KZ4_err],
      Or.inl ⟨trivial, by rw [mapState_tail', KZ4_tail], postLink_zero env σ inp⟩⟩
  · simp only [hc0, ↓reduceIte]
    obtain ⟨herr, htail, hlen, h8, h1, h2, h4, hcs, hV, hlog, hfoot, hout⟩ :=
      X.spec env σ m0 orcC c inp hw he hc hc0 hin
    exact ⟨herr, Or.inr ⟨hc0, htail,
      preLink_of_exit env σ c inp _ hlen h8 h1 h2 h4 hcs hV hlog hfoot hout herr⟩⟩

end Hashtree.Proofs.WinAvxX4Link
