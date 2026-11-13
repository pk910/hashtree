-- Axiom audit for every final theorem.
--
-- `lake env lean Axioms.lean` after a full build prints the axioms each
-- theorem depends on.  Expected: Lean's standard axioms (propext,
-- Classical.choice, Quot.sound) plus, for generated `bv_decide` lemmas, the
-- per-lemma `..._native.bv_decide.ax_*` axioms (the proof checker runs
-- compiled code).  Anything else -- especially `sorryAx` -- is a problem.
import Hashtree.Proofs.ShaniAll
import Hashtree.Proofs.ShaniW
import Hashtree.Proofs.SseX1All
import Hashtree.Proofs.AvxX1All
import Hashtree.Proofs.AvxX1W
import Hashtree.Proofs.WrapperAmd64
import Hashtree.Proofs.Avx2X8Body
import Hashtree.Proofs.Avx512X16Body
import Hashtree.Proofs.AvxX4LoopTurn
import Hashtree.Proofs.AvxX4ToX1
import Hashtree.GoProof
import Hashtree.Glue
import Hashtree.Gen.AvxX4P.Final
import Hashtree.Gen.Avx2X8P.Final
import Hashtree.Gen.Avx512X16P.Final
import Hashtree.Gen.ArmShaX1P.Final
import Hashtree.Gen.ArmNeonX1P.Final
import Hashtree.Gen.ArmNeonX1P0.Final
import Hashtree.Gen.ArmNeonX4P.Final
import Hashtree.Gen.RvX1P.Final
import Hashtree.Gen.RvZbbX1P.Final
import Hashtree.Gen.RvCryptoP.Final

/- R2b: x8/x16 W-mode -/
import Hashtree.Proofs.Avx2X8WEntry
import Hashtree.Proofs.Avx512X16WLoop

#print axioms Hashtree.Proofs.Shani.shani_correct
#print axioms Hashtree.Proofs.ShaniW.correctW
#print axioms Hashtree.Proofs.SseX1L.correct
#print axioms Hashtree.Proofs.AvxX1L.correct
#print axioms Hashtree.Proofs.AvxX1W.correctW
#print axioms Hashtree.Proofs.WrapperAmd64.wrapper_correct
#print axioms Hashtree.Go.sha256_1_generic_eq
#print axioms Hashtree.Glue.Hash_spec
#print axioms Hashtree.Glue.HashByteSlice_spec
#print axioms Hashtree.Proofs.Avx2X8Body.body_run
#print axioms Hashtree.Proofs.Avx512X16Body.body_run
#print axioms Hashtree.Proofs.AvxX4LoopTurn.turn_run
#print axioms Hashtree.Proofs.AvxX4ToX1.x4_small_to_x1

#print axioms Hashtree.Gen.AvxX4P.out_final
#print axioms Hashtree.Gen.Avx2X8P.out_final
#print axioms Hashtree.Gen.Avx512X16P.out_final
#print axioms Hashtree.Gen.ArmShaX1P.out_final
#print axioms Hashtree.Gen.ArmNeonX1P.out_final
#print axioms Hashtree.Gen.ArmNeonX1P0.only_stack_writes_run
#print axioms Hashtree.Gen.ArmNeonX4P.out_final
#print axioms Hashtree.Gen.RvX1P.out_final
#print axioms Hashtree.Gen.RvZbbX1P.out_final
#print axioms Hashtree.Gen.RvCryptoP.out_final

/- R2b: x8/x16 W-mode -/
#print axioms Hashtree.Proofs.Avx2X8WEntry.x8_zero_run
#print axioms Hashtree.Proofs.Avx2X8WEntry.x8_zero_run_region
#print axioms Hashtree.Proofs.Avx2X8WEntry.x8_prologue_run
#print axioms Hashtree.Proofs.Avx2X8WEntry.x8_align_blocked
#print axioms Hashtree.Proofs.Avx2X8WEntry.x8_stuck
#print axioms Hashtree.Proofs.Avx512X16WBody.body_runW
#print axioms Hashtree.Proofs.Avx512X16WBody.body_memW
#print axioms Hashtree.Proofs.Avx512X16WEntry.sliceW_entry
#print axioms Hashtree.Proofs.Avx512X16WEntry.sliceW_zero
#print axioms Hashtree.Proofs.Avx512X16WEntry.sliceW_small
#print axioms Hashtree.Proofs.Avx512X16WEntry.sliceW_turn
#print axioms Hashtree.Proofs.Avx512X16WEntry.sliceW_exit
#print axioms Hashtree.Proofs.Avx512X16WEntry.mapState_wcutE
#print axioms Hashtree.Proofs.Avx512X16WEntry.KT_gpr
#print axioms Hashtree.Proofs.Avx512X16WEntry.KT_vr
#print axioms Hashtree.Proofs.Avx512X16WEntry.KT_shape
#print axioms Hashtree.Proofs.Avx512X16WEntry.KT_inst
#print axioms Hashtree.Proofs.Avx512X16WEntry.tau_count
#print axioms Hashtree.Proofs.Avx512X16WBodyV.bodyV_run
#print axioms Hashtree.Proofs.Avx512X16WBodyV.bodyV_mem
#print axioms Hashtree.Proofs.Avx512X16WTurn.turn1_run
#print axioms Hashtree.Proofs.Avx512X16WTurn.turn_run
#print axioms Hashtree.Proofs.Avx512X16WTurn.exit1_run
#print axioms Hashtree.Proofs.Avx512X16WTurn.exit_run
#print axioms Hashtree.Proofs.Avx512X16WTurn.turn_step
#print axioms Hashtree.Proofs.Avx512X16WTurn.iter_step
#print axioms Hashtree.Proofs.Avx512X16WTurn.exit_step
#print axioms Hashtree.Proofs.Avx512X16WLoop.sIt_count
#print axioms Hashtree.Proofs.Avx512X16WLoop.loop
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_zero_run
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_small_run
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_loop
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_all
#print axioms Hashtree.Proofs.Avx512X16WLoop.body_runW_region
#print axioms Hashtree.Proofs.Avx512X16WLoop.body_memW_region
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_run_region
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_all_region
#print axioms Hashtree.Proofs.Avx512X16WLoop.x16_chain_head
