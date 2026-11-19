import Hashtree.Proofs.WinWrapperAvx1
import Hashtree.Proofs.WinShippedClobber

/-!
# R5: the shipped `$1024` windows wrapper on machines without AVX2/AVX-512

`WinWrapper.wrapper_kernelW_shipped` proves the shipped-frame wrapper for any kernel contract
whose stack depth stays above the wrapper's entry `rsp` (`hD9`); with the shipped alignment
(`σ 10 ≥ σ 9 + 977`) that is any depth `D ≤ 969`.  The two kernels the wrapper picks without
AVX-512 and AVX2 have proved contracts of depth 248 (`shani_x2`, `WinShaniBridge.shani_KSpecW`)
and 264 (`avx_x1`, `WinAvxX1W.kspecW`), so the binary as shipped is correct there:
`wrapper_noavx2_shipped` (no kernel hypothesis).  Its writes are output bytes and stack bytes
`[SPe - 8, σ10 + 8)` — above the entry `rsp`, in the caller's frame (the shipped frame's known
placement), and the linux-style footprint is false (`wrapper_kernelW_shipped`).

On AVX2/AVX-512 machines the shipped binary is *not* correct for `c ≥ 8`:
`WinShippedClobber.shipped_avx2x8_store_clobbers_go_frame` (the avx2_x8 loop's input-derived
store covers the Go caller's saved `rbp` and return address).  The fixed frame (`$2048`, PR #80)
is proved on every dispatch target: `WinWrapperAvx1.wrapper_correctW_noavx2`,
`WinWrapperChain.wrapper_avx512_chain`, `WinWrapperChain.wrapper_avx2_chain`.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinWrapperShipped

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.WinWrapper Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Proofs.WrapperAmd64 (argCells)

/-- Without AVX-512 and AVX2 the picked kernel has a proved contract of depth at most 969. -/
theorem fits_shipped (hasShani : Bool) :
    ∃ (steps : Nat → Nat) (D : Nat), D ≤ 969 ∧
      KSpecW (kprogOfW (pick hasShani false false)) (krodataOfW (pick hasShani false false)) steps D := by
  cases hasShani
  · exact ⟨Hashtree.Proofs.WinAvxX1W.steps, Hashtree.Proofs.WinAvxX1W.D, by decide,
      Hashtree.Proofs.WinAvxX1W.kspecW⟩
  · exact ⟨Hashtree.Proofs.WinShaniBridge.stepsW, 248, by decide,
      Hashtree.Proofs.WinShaniBridge.shani_KSpecW⟩

/-- **`HashtreeHash` as shipped (windows/amd64, `$1024`) is correct without AVX2/AVX-512**: for
the kernel the feature bytes select (`shani_x2` or `avx_x1`), every count, the wrapper returns
with `rsp`, `rbp`, `r8` restored, every write an output byte or a stack byte of
`[SPe - 8, σ10 + 8)`, and every output block SHA-256 of its input block. -/
theorem wrapper_noavx2_shipped (hasShani : Bool) :
    let k := pick hasShani false false
    ∃ steps : Nat → Nat, ∀ (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32)
      (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool),
      WfMemW (krodataOfW k) argCells env σ mem0c → EnvMem env σ mem0c → σ 2 = c →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      σ 10 + 8 = (σ 9 + 1016) - (σ 9 + 1016) % 32 →
      let fin := wrapRunW shippedFrame (kprogOfW k) (steps c) mem0c orc (mapState env σ wEntryW)
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
        fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
        (∀ p ∈ fin.mem, (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * c) ∨
          (p.1.region = rStack ∧ σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 10 + 8)) ∧
        OutOk inp (σ 1) c fin.mem := by
  intro k
  obtain ⟨steps, D, hD, hs⟩ := fits_shipped hasShani
  refine ⟨steps, fun c inp env σ mem0c orc hw he hc hin hA => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, _⟩ :=
    wrapper_kernelW_shipped _ _ steps D hs c inp env σ mem0c orc hw he hc hin hA (by omega)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end Hashtree.Proofs.WinWrapperShipped
