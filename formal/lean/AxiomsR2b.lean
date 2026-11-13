/- R2b: x8/x16 W-mode -/
-- Standalone audit of the R2b block of Axioms.lean: lake env lean AxiomsR2b.lean

import Hashtree.Proofs.Avx2X8WEntry
import Hashtree.Proofs.Avx512X16WBody
import Hashtree.Proofs.Avx512X16WEntry
import Hashtree.Proofs.Avx512X16WBodyV
import Hashtree.Proofs.Avx512X16WTurn
import Hashtree.Proofs.Avx512X16WLoop

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
