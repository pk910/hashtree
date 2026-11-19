import Hashtree.Proofs.WinAvxX1W
import Hashtree.Proofs.WinShaniBridge

/-!
# R5: the windows wrapper is correct on machines without AVX2/AVX-512

`WinWrapper.wrapper_correctW` takes the four windows kernel contracts as hypotheses.  Two of them
are now theorems: `WinShaniBridge.fitsW_shani` (`shani_x2`) and `WinAvxX1W.fitsW_avx1` (`avx_x1`,
from the windows-stream loop certificate `Gen/WinAvxX1LW`).  When the feature bytes select
neither AVX-512 nor AVX2, the wrapper picks one of these two, so its correctness no longer has a
hypothesis about a kernel (`wrapper_correctW_noavx2`).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinWrapperAvx1

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.WinWrapper Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Proofs.WrapperAmd64 (argCells)

/-- Without AVX-512 and AVX2 the wrapper picks `shani_x2` or `avx_x1`; both fit. -/
theorem fitsW_pick (hasShani : Bool) : FitsW (pick hasShani false false) := by
  cases hasShani
  · exact Hashtree.Proofs.WinAvxX1W.fitsW_avx1
  · exact Hashtree.Proofs.WinShaniBridge.fitsW_shani

/-- **`HashtreeHash` (windows/amd64, fixed frame) is correct** whenever the feature bytes select
`shani_x2` or `avx_x1` (no AVX-512, no AVX2): the statement of `WinWrapper.wrapper_correctW`
without any kernel hypothesis. -/
theorem wrapper_correctW_noavx2 (hasShani : Bool) :
    let k := pick hasShani false false
    ∃ steps : Nat → Nat, ∀ (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32)
      (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool),
      WfMemW (krodataOfW k) argCells env σ mem0c → EnvMem env σ mem0c → σ 2 = c →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32 →
      let fin := wrapRunW fixedFrame (kprogOfW k) (steps c) mem0c orc (mapState env σ wEntryW)
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
        fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
        Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
        OutOk inp (σ 1) c fin.mem := by
  intro k
  obtain ⟨steps, D, hD, hs⟩ := fitsW_pick hasShani
  exact ⟨steps, fun c inp env σ mem0c orc hw he hc hin hA =>
    wrapper_kernelW_fixed _ _ steps D hs hD c inp env σ mem0c orc hw he hc hin hA⟩

end Hashtree.Proofs.WinWrapperAvx1
