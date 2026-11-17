import Hashtree.Proofs.WinAvxX4WOutInvW
import Hashtree.Proofs.WinAvxX4WOutInvS
import Hashtree.Proofs.WinAvxX4WOutChk1
import Hashtree.Proofs.WinAvxX4WOutChk2
import Hashtree.Gen.WinAvxX4P.P203

/-! R2c windows x4 — the pilot's last step (`K203 → K204`, the exit with the digest stores) lifted to the
four loop tails (generated). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4 Hashtree.Gen.WinAvxX4P
open Hashtree.Proofs.WinAvxX4W (m0W shiftKW orcB orcEx KT KTE)
open Hashtree.Proofs.WinAvxX4WStrip (m0WP stripKW KHs KH3s KTs KTEs)
open Hashtree.Proofs.Avx512X16WOut (invC_lift invC_lift')

namespace Hashtree.Proofs.WinAvxX4WOut

theorem w4stepT_turn (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W orcB 25 (shiftKW K203))) L204 :=
  invC_lift' inp env prog 4 m0q _ 37 K203 K204 m0W orcB 25 (shiftKW K203) KT T203 L204
    slice203 w4chkT_turn w4lab_203 (step203 inp env hI hm)

theorem w4stepT_exit (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W orcEx 37 (shiftKW K203))) L204 :=
  invC_lift inp env prog 4 m0q m0W _ _ 37 K203 K204 (shiftKW K203) KTE T203 L204
    slice203 w4chkT_exit w4lab_203 (step203 inp env hI hm)

theorem w4stepT_turnS (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0WP orcB 25 (stripKW K203))) L204 :=
  invC_lift' inp env prog 4 m0q _ 37 K203 K204 m0WP orcB 25 (stripKW K203) KTs T203 L204
    slice203 w4chkT_turnS w4lab_203 (step203 inp env hI hm)

theorem w4stepT_exitS (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0WP orcEx 37 (stripKW K203))) L204 :=
  invC_lift inp env prog 4 m0q m0WP _ _ 37 K203 K204 (stripKW K203) KTEs T203 L204
    slice203 w4chkT_exitS w4lab_203 (step203 inp env hI hm)

end Hashtree.Proofs.WinAvxX4WOut
