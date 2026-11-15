import Hashtree.Proofs.WinAvx512Link
import Hashtree.Proofs.Avx512X16WOut

/-!
# R5: the unconditional windows avx512_x16 chain link

R2c's `Avx512X16WOut.turnOut` proves the output-byte statement `TurnOut` (its text is
`WinAvx512Bridge.TurnOut` verbatim, with its own `OutOk` constant of the same text as
`WinWrapper.OutOk`), so the hypothesis of `WinAvx512Link.KSpecC512_of_turnOut` is discharged:
`KSpecC512_final` is the avx512_x16 link obligation without hypotheses, and `head512` is its
chain-aware form (the head clause of `KSpecC` for `winSpecs`, `WinAvx512Bridge.KSpecC512_head`).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinAvx512Final

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.X86Chain Hashtree.Proofs.WinChain
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinAvx512Bridge (KSpecC512 KSpecC512_head PostLink PreLink TurnOut L8)
open Hashtree.Proofs.WinAvx512Link (KSpecC512_of_turnOut)

/-- R2c's theorem, read at R5's `TurnOut` (the two `OutOk` constants unfold to the same text). -/
theorem turnOut512 : TurnOut := by
  intro mem0c orcC env0 σ c inp h0 hw h10 hc h16 hin
  have h := Hashtree.Proofs.Avx512X16WOut.turnOut mem0c orcC env0 σ c inp h0 hw h10 hc h16 hin
  unfold Hashtree.Proofs.Avx512X16WOut.OutOk at h
  unfold Hashtree.Proofs.WinWrapper.OutOk
  exact h

/-- **The avx512_x16 link, unconditional.** -/
theorem KSpecC512_final (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) :
    KSpecC512 Hashtree.Proofs.Avx512X16WLoop.steps env σ m0 orcC c inp :=
  KSpecC512_of_turnOut (env := env) (σ := σ) (m0 := m0) (orcC := orcC) turnOut512 c inp

/-- The chain-aware form: the head clause of `KSpecC` for `winSpecs` at the avx512_x16 link. -/
theorem head512 (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte)
    (hw : WfMemW Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0) (he : EnvMem env σ m0)
    (hc : σ 2 = c) (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, (fun s => s = mapState env σ entryWin) s →
      let f := step m0 orcC c (linkOf "hashtree_sha256_avx512_x16" p512 Hashtree.Proofs.Avx512X16WLoop.steps) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp 0 f) ∨
         (f.tail = some (linkOf "hashtree_sha256_avx2_x8" p8 (fun _ => 0)).name ∧
           PreLink env σ c (c - c % 16) (c % 16) inp 0 L8 (resume f))) :=
  KSpecC512_head Hashtree.Proofs.Avx512X16WLoop.steps env σ m0 orcC c inp hw he hc hin
    (KSpecC512_final env σ m0 orcC c inp)

end Hashtree.Proofs.WinAvx512Final
