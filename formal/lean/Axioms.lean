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
/- R4: riscv64 -/
import Hashtree.Proofs.RvX1All
import Hashtree.Proofs.RvZbbX1All
import Hashtree.Proofs.RvCryptoAll
import Hashtree.Proofs.RvRegs
import Hashtree.Proofs.RvDispatch
import Hashtree.Proofs.RvWrapperLinux
import Hashtree.Proofs.RvDispatchInit
import Hashtree.Proofs.RvChain

#print axioms Hashtree.Proofs.ShaniAll.shani_correct
#print axioms Hashtree.Proofs.ShaniW.correctW
#print axioms Hashtree.Proofs.SseX1All.correct
#print axioms Hashtree.Proofs.AvxX1All.correct
#print axioms Hashtree.Proofs.AvxX1W.correctW
#print axioms Hashtree.Proofs.WrapperAmd64.wrapper_correct
#print axioms Hashtree.GoProof.sha256_1_generic_eq
#print axioms Hashtree.Glue.Hash_spec
#print axioms Hashtree.Glue.HashByteSlice_spec

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

/- R4: riscv64 -/
#print axioms Hashtree.Proofs.RvX1L.correct
#print axioms Hashtree.Proofs.RvZbbX1L.correct
#print axioms Hashtree.Proofs.RvCryptoL.correct
#print axioms Hashtree.Proofs.RvRegs.correct_regs_x1
#print axioms Hashtree.Proofs.RvRegs.correct_regs_zbb
#print axioms Hashtree.Proofs.RvRegs.correct_regs_crypto
#print axioms Hashtree.Proofs.RvRegs.all_x1
#print axioms Hashtree.Proofs.RvRegs.all_zbb
#print axioms Hashtree.Proofs.RvRegs.all_crypto
#print axioms Hashtree.Proofs.RvRegs.run_gpr
#print axioms Hashtree.Proofs.RvRegs.exec_gpr
#print axioms Hashtree.Proofs.RvDispatch.stub_correct
#print axioms Hashtree.Proofs.RvDispatch.cmem_rel
#print axioms Hashtree.Proofs.RvWrapperLinux.wrapper_prefix
#print axioms Hashtree.Proofs.RvWrapperLinux.stub_at_call
#print axioms Hashtree.Proofs.RvWrapperLinux.wrapper_epilogue
#print axioms Hashtree.Proofs.RvWrapperLinux.b7_entry
#print axioms Hashtree.Proofs.RvWrapperLinux.b7_callee
#print axioms Hashtree.Proofs.RvWrapperLinux.prefixC
#print axioms Hashtree.Proofs.RvWrapperLinux.wrapper_end2end
#print axioms Hashtree.Proofs.RvDispatchInit.classOfNat_ext
#print axioms Hashtree.Proofs.RvDispatchInit.selName_eq_classOf
#print axioms Hashtree.Proofs.RvDispatchInit.ih_syscall_fail_x1
#print axioms Hashtree.Proofs.RvDispatchInit.ih_probe_crypto
#print axioms Hashtree.Proofs.RvDispatchInit.ih_probe_zbb
#print axioms Hashtree.Proofs.RvDispatchInit.ih_probe_x1
#print axioms Hashtree.Proofs.RvDispatchInit.ih_select_bits
#print axioms Hashtree.Proofs.RvDispatchInit.hi_override
#print axioms Hashtree.Proofs.RvDispatchInit.hi_syscall_fail_x1
#print axioms Hashtree.Proofs.RvDispatchInit.hi_select_bits

/- R4: riscv64 — the chain composition and the return/epilogue composition -/
#print axioms Hashtree.Proofs.RvChain.return_transition
#print axioms Hashtree.Proofs.RvChain.chain_sound
#print axioms Hashtree.Proofs.RvChain.chainRun_none
#print axioms Hashtree.Proofs.RvChain.chainRun_zbb
#print axioms Hashtree.Proofs.RvChain.chainRun_crypto
#print axioms Hashtree.Proofs.RvChain.specs_KSpecC_none
#print axioms Hashtree.Proofs.RvChain.specs_KSpecC_zbb
#print axioms Hashtree.Proofs.RvChain.specs_KSpecC_crypto
#print axioms Hashtree.Proofs.RvChain.chain_sound_none
#print axioms Hashtree.Proofs.RvChain.chain_sound_zbb
#print axioms Hashtree.Proofs.RvChain.chain_sound_crypto
#print axioms Hashtree.Proofs.RvChain.chain_none
#print axioms Hashtree.Proofs.RvChain.chain_zbb
#print axioms Hashtree.Proofs.RvChain.chain_crypto
#print axioms Hashtree.Proofs.RvChain.loadVal_congr
#print axioms Hashtree.Proofs.RvChain.loadLane_congr
#print axioms Hashtree.Proofs.RvChain.pbRest_congr
#print axioms Hashtree.Proofs.RvChain.readCell_congr
#print axioms Hashtree.Proofs.RvChain.readCell_post
#print axioms Hashtree.Proofs.RvChain.inRange_ne_slot
#print axioms Hashtree.Proofs.RvChain.ra_slot_go_none
#print axioms Hashtree.Proofs.RvChain.ra_slot_go_zbb
#print axioms Hashtree.Proofs.RvChain.ra_slot_go_crypto
#print axioms Hashtree.Proofs.RvChain.ra_slot_post
#print axioms Hashtree.Proofs.RvChain.kerRun_len
#print axioms Hashtree.Proofs.RvChain.end2end_of
#print axioms Hashtree.Proofs.RvChain.end2end_none
#print axioms Hashtree.Proofs.RvChain.end2end_zbb
#print axioms Hashtree.Proofs.RvChain.end2end_crypto
