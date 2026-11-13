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
/- R5: windows amd64 -/
import Hashtree.Proofs.WinAvx512
import Hashtree.Proofs.WinShani
import Hashtree.Proofs.WinSseX1
import Hashtree.Proofs.WinAvxX1

#print axioms Hashtree.Proofs.ShaniAll.shani_correct
#print axioms Hashtree.Proofs.ShaniW.correctW
#print axioms Hashtree.Proofs.SseX1All.correct
#print axioms Hashtree.Proofs.AvxX1All.correct
#print axioms Hashtree.Proofs.AvxX1W.correctW
#print axioms Hashtree.Proofs.WrapperAmd64.wrapper_correct
#print axioms Hashtree.GoProof.sha256_1_generic_eq
#print axioms Hashtree.Glue.Hash_spec
#print axioms Hashtree.Glue.HashByteSlice_spec
#print axioms Hashtree.Proofs.Avx2X8Body.body_run
#print axioms Hashtree.Proofs.Avx512X16Body.body_run
#print axioms Hashtree.Proofs.AvxX4LoopTurn.turn_run

#print axioms Hashtree.Gen.AvxX4P.Final.out_final
#print axioms Hashtree.Gen.Avx2X8P.Final.out_final
#print axioms Hashtree.Gen.Avx512X16P.Final.out_final
#print axioms Hashtree.Gen.ArmShaX1P.Final.out_final
#print axioms Hashtree.Gen.ArmNeonX1P.Final.out_final
#print axioms Hashtree.Gen.ArmNeonX1P0.Final.only_stack_writes_run
#print axioms Hashtree.Gen.ArmNeonX4P.Final.out_final
#print axioms Hashtree.Gen.RvX1P.Final.out_final
#print axioms Hashtree.Gen.RvZbbX1P.Final.out_final
#print axioms Hashtree.Gen.RvCryptoP.Final.out_final

/- R5: windows amd64 -/
#print axioms Hashtree.Proofs.WinAvx512.win_run
#print axioms Hashtree.Proofs.WinAvx512.win_out
#print axioms Hashtree.Proofs.WinAvx512.win_no_rsp
#print axioms Hashtree.Proofs.WinAvx512.win_no_stack_access
#print axioms Hashtree.Proofs.WinAvx512.u6_witness
#print axioms Hashtree.Proofs.WinShani.shani_body_correspondence
#print axioms Hashtree.Proofs.WinShani.shani_stack_footprint
#print axioms Hashtree.Proofs.WinShani.shani_callee_gpr_untouched
#print axioms Hashtree.Proofs.WinShani.shani_rsp_balanced
#print axioms Hashtree.Proofs.WinShani.shani_prologue_saves
#print axioms Hashtree.Proofs.WinShani.shani_epilogue_restores
#print axioms Hashtree.Proofs.WinShani.shani_save_slots_untouched
#print axioms Hashtree.Proofs.WinSseX1.sse_body_correspondence
#print axioms Hashtree.Proofs.WinSseX1.sse_stack_footprint
#print axioms Hashtree.Proofs.WinSseX1.sse_body_footprint
#print axioms Hashtree.Proofs.WinSseX1.sse_prologue_pushes
#print axioms Hashtree.Proofs.WinSseX1.sse_epilogue_pops
#print axioms Hashtree.Proofs.WinSseX1.sse_callee_saved_covered
#print axioms Hashtree.Proofs.WinSseX1.sse_rsp_balanced
#print axioms Hashtree.Proofs.WinSseX1.sse_prologue_saves
#print axioms Hashtree.Proofs.WinSseX1.sse_epilogue_restores
#print axioms Hashtree.Proofs.WinSseX1.sse_save_slots_untouched
#print axioms Hashtree.Proofs.WinSseX1.sse_callee_vec_split
#print axioms Hashtree.Proofs.WinSseX1.sse_no_xmm14_15
#print axioms Hashtree.Proofs.WinSseX1.renPerm
#print axioms Hashtree.Proofs.WinAvxX1.avx_body_correspondence
#print axioms Hashtree.Proofs.WinAvxX1.avx_stack_footprint
#print axioms Hashtree.Proofs.WinAvxX1.avx_body_footprint
#print axioms Hashtree.Proofs.WinAvxX1.avx_prologue_pushes
#print axioms Hashtree.Proofs.WinAvxX1.avx_epilogue_pops
#print axioms Hashtree.Proofs.WinAvxX1.avx_callee_saved_covered
#print axioms Hashtree.Proofs.WinAvxX1.avx_rsp_balanced
#print axioms Hashtree.Proofs.WinAvxX1.avx_prologue_saves
#print axioms Hashtree.Proofs.WinAvxX1.avx_epilogue_restores
#print axioms Hashtree.Proofs.WinAvxX1.avx_save_slots_untouched
#print axioms Hashtree.Proofs.WinAvxX1.avx_callee_vec_split
#print axioms Hashtree.Proofs.WinAvxX1.avx_no_xmm14_15
#print axioms Hashtree.Proofs.WinAvxX1.renPerm
