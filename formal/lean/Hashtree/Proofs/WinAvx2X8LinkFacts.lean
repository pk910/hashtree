import Hashtree.Proofs.WinAvx2X8WAll
import Hashtree.Proofs.WinAvx2X8WSmall
import Hashtree.Proofs.WinAvx2X8WOut
import Hashtree.Proofs.WinAvx2X8Bridge
import Hashtree.Proofs.WinAvxX4CertFacts

/-!
# R5: kernel facts for the windows avx2_x8 link (`WinAvx2X8Link`)

The `c = 0` early return of the windows avx2_x8 stream (`KZ8`, four instructions from the call
state), the exit registers of the loop cuts (`exitGprW`: the call registers with `rcx`, `rdx`,
`r8` advanced), and the vector-file shape and stack-only log of the small-path cut `x8Sm r`
(inside `[σ 9 - 1296, σ 9)`).  The vector-file shapes of the loop exit cuts `KTE r`/`KTEs r` are
one kernel evaluation each (`WinAvx2X8LinkVr*`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvx2X8Link

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.WinChain (p8)
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.WinAvx512Bridge (PostLink)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)
open Hashtree.Proofs.WinShaniBridge (getElem?_of_getG)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)
open Hashtree.Proofs.WinAvx2X8W (exitGprW)

abbrev rodata8 : List Nat := Hashtree.Kernels.X86Win.Avx2X8.rodata

/-! ## The `c = 0` path: `nop; cmp r8, 0; jne; ret` -/

abbrev m08 : Addr Lin → Cell E Lin := mem0sW 4 rodata8 []

/-- The symbolic state after the early return (four instructions from the call state). -/
def KZ8 : State E Lin := run p8 4 m08 (fun _ => false) 4 entryWin

theorem KZ8_err : KZ8.err = none := by decide +kernel
theorem KZ8_assume : KZ8.assume = [(.not (.eq ⟨0, [0, 0, 1]⟩ ⟨0, []⟩), false)] := by decide +kernel
theorem KZ8_halted : KZ8.halted = true := by decide +kernel
theorem KZ8_tail : KZ8.tail = none := by decide +kernel
theorem KZ8_mem : KZ8.mem = [] := by decide +kernel
theorem KZ8_len : KZ8.gpr.length = 16 := by decide +kernel
theorem KZ8_gpr3 : KZ8.gpr[3]? = some (.ptr ⟨rStack, Lin.sym 5⟩) := by decide +kernel
theorem KZ8_gpr4 : KZ8.gpr[4]? = some (.ptr ⟨rStack, sAt 8⟩) := by decide +kernel
theorem KZ8_gpr5 : KZ8.gpr[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by decide +kernel
theorem KZ8_gpr12 : KZ8.gpr[12]? = some (.ptr ⟨rNum, Lin.sym 7⟩) := by decide +kernel
theorem KZ8_gpr13 : KZ8.gpr[13]? = some (.ptr ⟨rNum, Lin.sym 11⟩) := by decide +kernel
theorem KZ8_gpr14 : KZ8.gpr[14]? = some (.ptr ⟨rG, Lin.sym 8⟩) := by decide +kernel
theorem KZ8_gpr15 : KZ8.gpr[15]? = some (.ptr ⟨rNum, Lin.sym 12⟩) := by decide +kernel

theorem KZ8_assumeOk (σ : Nat → Int) (hc : σ 2 = 0) : AssumeOk σ KZ8 := by
  intro p hp
  rw [KZ8_assume] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  simp [mapCond, Cond.decideC, Lin.eval, dotC, hc, Ctl.sub]
  try rfl

/-- The windows avx2_x8 kernel at count 0 returns after four instructions. -/
theorem x8_zero_run (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemW rodata8 [] env σ m0) (he : EnvMem env σ m0) (hc : σ 2 = 0) :
    run p8 4 m0 orcC 4 (mapState env σ entryWin) = mapState env σ KZ8 :=
  run_hom env σ m08 m0 (mem0RelW_of_wf rodata8 [] env σ m0 hw he) p8 4 (fun _ => false) orcC 4 entryWin
    rfl KZ8_err (KZ8_assumeOk σ hc)

theorem mapState_halted' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) : (mapState e τ K).halted = K.halted := rfl
theorem mapState_mem' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (mapState e τ K).mem = K.mem.map (fun p => (mapAddr τ p.1, mapCell e τ p.2)) := rfl
theorem mapState_len' (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (mapState e τ K).gpr.length = K.gpr.length := List.length_map ..

/-- The `c = 0` return meets `PostLink` at depth 0. -/
theorem postLink_zero8 (env : Key → W32) (σ : Nat → Int) (inp : Nat → Spec.Byte) :
    PostLink σ 0 inp 0 (mapState env σ KZ8) := by
  have hlen : (mapState env σ KZ8).gpr.length = 16 := by rw [mapState_len', KZ8_len]
  have hmem : (mapState env σ KZ8).mem = [] := by rw [mapState_mem', KZ8_mem]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mapState_halted', KZ8_halted]
  · intro p hp; rw [hmem] at hp; cases hp
  · intro n i b hn; exact absurd hn (Nat.not_lt_zero _)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getElem?_of_getG _ 3 (by omega), mapState_getG KZ8_gpr3]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 5 (by omega), mapState_getG KZ8_gpr5]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 12 (by omega), mapState_getG KZ8_gpr12]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 13 (by omega), mapState_getG KZ8_gpr13]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 14 (by omega), mapState_getG KZ8_gpr14]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 15 (by omega), mapState_getG KZ8_gpr15]; simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [getElem?_of_getG _ 4 (by omega), mapState_getG KZ8_gpr4]
      simp [mapVal, mapAddr, sAt_eval]
      omega

/-! ## The exit registers of the loop cuts -/

theorem eg1 : exitGprW[1]? = some (.ptr ⟨rOut, ⟨256, [0, 1]⟩⟩) := by decide +kernel
theorem eg2 : exitGprW[2]? = some (.ptr ⟨rIn, ⟨512, [1]⟩⟩) := by decide +kernel
theorem eg8 : exitGprW[8]? = some (.ptr ⟨rNum, ⟨-8, [0, 0, 1]⟩⟩) := by decide +kernel
theorem eg3 : exitGprW[3]? = some (.ptr ⟨rStack, Lin.sym 5⟩) := by decide +kernel
theorem eg4 : exitGprW[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel
theorem eg5 : exitGprW[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by decide +kernel
theorem eg6 : exitGprW[6]? = some (.num (.var (.n 12)) (.var (.n 13))) := by decide +kernel
theorem eg7 : exitGprW[7]? = some (.num (.var (.n 14)) (.var (.n 15))) := by decide +kernel
theorem eg12 : exitGprW[12]? = some (.ptr ⟨rNum, Lin.sym 7⟩) := by decide +kernel
theorem eg13 : exitGprW[13]? = some (.ptr ⟨rNum, Lin.sym 11⟩) := by decide +kernel
theorem eg14 : exitGprW[14]? = some (.ptr ⟨rG, Lin.sym 8⟩) := by decide +kernel
theorem eg15 : exitGprW[15]? = some (.ptr ⟨rNum, Lin.sym 12⟩) := by decide +kernel
theorem eg_len : exitGprW.length = 16 := by decide +kernel

theorem ew6 : entryWin.gpr[6]? = some (.num (.var (.n 12)) (.var (.n 13))) := by decide +kernel
theorem ew7 : entryWin.gpr[7]? = some (.num (.var (.n 14)) (.var (.n 15))) := by decide +kernel

/-! ## The small-path cut: vector file and stack-only log -/

/-- A stack-only log inside `[τ 9 - D, τ 9)`. -/
def stackLogD (D : Int) (K : State E Lin) : Bool :=
  K.mem.all (fun p => (p.1.region == rStack) && (p.1.off.c == stkC) && decide (-D ≤ p.1.off.k) &&
    decide (p.1.off.k < 0))

theorem stackLogD_sound (D : Int) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) (h : stackLogD D K = true) :
    ∀ p ∈ (mapState e τ K).mem, p.1.region = rStack ∧ τ 9 - D ≤ p.1.off ∧ p.1.off < τ 9 := by
  intro p hp
  simp only [mapState, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [stackLogD, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h q hq
  obtain ⟨⟨r, ⟨k, cs⟩⟩, cell⟩ := q
  simp only at h1 h2 h3 h4
  subst h1; subst h2
  have := sAt_eval τ k
  simp only [mapAddr]
  refine ⟨by first | rfl | trivial, ?_, ?_⟩ <;> simp only [sAt] at this <;>
    rw [show (⟨k, stkC⟩ : Lin) = sAt k from rfl, sAt_eval] <;> omega

open Hashtree.Proofs.WinAvx2X8WSmall (x8Sm)
open Hashtree.Proofs.WinAvxX4Cert (vrOk)

theorem x8Sm_8 : vrOk (x8Sm 8) = true ∧ stackLogD 1296 (x8Sm 8) = true := by
  constructor <;> decide +kernel
theorem x8Sm_24 : vrOk (x8Sm 24) = true ∧ stackLogD 1296 (x8Sm 24) = true := by
  constructor <;> decide +kernel

theorem x8Sm_abi (r : Nat) (hr : r = 8 ∨ r = 24) : vrOk (x8Sm r) = true ∧ stackLogD 1296 (x8Sm r) = true := by
  rcases hr with rfl | rfl
  · exact x8Sm_8
  · exact x8Sm_24

end Hashtree.Proofs.WinAvx2X8Link
