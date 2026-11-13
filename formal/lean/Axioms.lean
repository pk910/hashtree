import Hashtree.Proofs.WinSseRun
import Hashtree.Proofs.WinSseBody
import Hashtree.Proofs.WinAvxBody
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
import Hashtree.Proofs.WinChain
import Hashtree.Proofs.WinFrame
import Hashtree.Proofs.WinFrameStack
import Hashtree.Proofs.WinSafeScan
import Hashtree.Proofs.WinShaniTransfer
import Hashtree.Proofs.WinShaniFront
import Hashtree.Proofs.WinShaniFlags
import Hashtree.Proofs.WinShaniEpi
import Hashtree.Proofs.WinShaniCall
import Hashtree.Proofs.WinShaniWrite
import Hashtree.Proofs.WinShaniExit
import Hashtree.Proofs.WinAvxX4
import Hashtree.Proofs.WinAvx2X8
import Hashtree.Proofs.WinWrapperPre
import Hashtree.Proofs.WinWrapperMach
import Hashtree.Proofs.WinWrapper
import Hashtree.Proofs.WinWrapperSat
import Hashtree.Proofs.WinShippedClobber
import Hashtree.Proofs.WinShaniSeedAlign
import Hashtree.Asm.RunAgree

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
#print axioms Hashtree.Proofs.WinChain.win_chain_names
#print axioms Hashtree.Proofs.WinChain.win_chain_tails
#print axioms Hashtree.Proofs.WinChain.win_small_exit
#print axioms Hashtree.Asm.X86.exec_shiftPc
#print axioms Hashtree.Asm.X86.run_shift
#print axioms Hashtree.Proofs.WinChain.win_chainRun_returns
#print axioms Hashtree.Proofs.WinChain.win_callChain_returns
#print axioms Hashtree.Proofs.WinChain.win_callChain_fr
#print axioms Hashtree.Proofs.WinAvxX1.renPerm

/- R5: windows amd64 -/
#print axioms Hashtree.Asm.X86.effAddr_mv
#print axioms Hashtree.Asm.X86.exec_frame
#print axioms Hashtree.Asm.X86.run_comb
#print axioms Hashtree.Asm.X86.frameSafeB_iff
#print axioms Hashtree.Asm.X86.safeB_and
#print axioms Hashtree.Proofs.WinShaniTransfer.body_safe
#print axioms Hashtree.Proofs.WinShaniTransfer.body_hmap
#print axioms Hashtree.Proofs.WinShaniTransfer.body_hside
#print axioms Hashtree.Proofs.WinShaniTransfer.shani_body_transfer
#print axioms Hashtree.Proofs.WinShaniFront.storeLanes_rec
#print axioms Hashtree.Proofs.WinShaniFront.mem_storeLanes
#print axioms Hashtree.Proofs.WinShaniFront.exec_sub_rsp
#print axioms Hashtree.Proofs.WinShaniFront.exec_vstore_rsp
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_stack_footprint
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_body_footprint
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_callee_gpr_untouched
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_rsp_balanced
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_prologue_saves
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_epilogue_restores
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_save_slots_untouched
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_callee_vec_covered
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_sites
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_targets_in_range
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_tails
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_site_pc_shifts
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_target_pairs
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_stack_footprint
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_body_footprint
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_callee_gpr_untouched
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_callee_saved_covered
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_rsp_chain
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_rsp_balanced
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_prologue_gpr_saves
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_epilogue_gpr_restores
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_prologue_vec_saves
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_epilogue_vec_restores
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_save_slots_untouched
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_callee_vec_covered
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_frame_below
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_sites
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_tails
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_site_pc_shifts
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_target_pairs
-- R5: body correspondence of the windows avx_x4 / avx2_x8 streams (the linux body under a
-- register substitution and the non-constant pc / target maps).
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_bodyTgt_values
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_bodyPc_values
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_body_lo_scan
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_body_hi_scan
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_body_correspondence_lo
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_body_correspondence_hi
#print axioms Hashtree.Proofs.WinAvxX4.avx_x4_body_correspondence
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_bodyTgt_values
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_bodyPc_values
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_body_lo_scan
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_body_hi_scan
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_body_correspondence_lo
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_body_correspondence_hi
#print axioms Hashtree.Proofs.WinAvx2X8.avx2x8_body_correspondence

-- R5: the stack-memory shift of the sse_x1/avx_x1 frame transfer (foundation)
#print axioms Hashtree.Asm.X86.shAddr_region
#print axioms Hashtree.Asm.X86.shAddr_plusI
#print axioms Hashtree.Asm.X86.shAddr_same
#print axioms Hashtree.Asm.X86.lookup_sh
#print axioms Hashtree.Asm.X86.readCell_sh

-- R5: stack-memory shift engine, layer 2 (operand and load/store commutation)
#print axioms Hashtree.Asm.X86.emap_bind
#print axioms Hashtree.Asm.X86.ebind_ok
#print axioms Hashtree.Asm.X86.ebind_error
#print axioms Hashtree.Asm.X86.emap_ok
#print axioms Hashtree.Asm.X86.emap_error
#print axioms Hashtree.Asm.X86.emap_pure
#print axioms Hashtree.Asm.X86.emap_throw
#print axioms Hashtree.Asm.X86.emap_bind_congr
#print axioms Hashtree.Asm.X86.emap_bind_map
#print axioms Hashtree.Asm.X86.getD_map_shVal
#print axioms Hashtree.Asm.X86.getG_sh
#print axioms Hashtree.Asm.X86.setG_sh
#print axioms Hashtree.Asm.X86.getV_sh
#print axioms Hashtree.Asm.X86.setV_sh
#print axioms Hashtree.Asm.X86.next_sh
#print axioms Hashtree.Asm.X86.clearFlags_sh
#print axioms Hashtree.Asm.X86.setFlags_sh
#print axioms Hashtree.Asm.X86.setData32_sh
#print axioms Hashtree.Asm.X86.halt_sh
#print axioms Hashtree.Asm.X86.fail_sh
#print axioms Hashtree.Asm.X86.okOr_sh
#print axioms Hashtree.Asm.X86.branch_sh
#print axioms Hashtree.Asm.X86.shAddr_plus
#print axioms Hashtree.Asm.X86.regPtr_sh
#print axioms Hashtree.Asm.X86.baseAddr_sh
#print axioms Hashtree.Asm.X86.effAddr_sh
#print axioms Hashtree.Asm.X86.cellData_sh
#print axioms Hashtree.Asm.X86.lanePat_sh
#print axioms Hashtree.Asm.X86.loadLane_sh
#print axioms Hashtree.Asm.X86.loadLanes_sh
#print axioms Hashtree.Asm.X86.storeLane_sh
#print axioms Hashtree.Asm.X86.storeLanes_sh
#print axioms Hashtree.Asm.X86.isPb_sh
#print axioms Hashtree.Asm.X86.pbRest_sh
#print axioms Hashtree.Asm.X86.loadVal_sh
#print axioms Hashtree.Asm.X86.pbList_sh
#print axioms Hashtree.Asm.X86.storeVal_sh
#print axioms Hashtree.Asm.X86.gData32_sh
#print axioms Hashtree.Asm.X86.gCtl_sh
#print axioms Hashtree.Asm.X86.readVSrc_sh

-- R5: the stack-memory shift engine (exec_sh, one instruction over all 39 constructors)
#print axioms Hashtree.Asm.X86.shVal_id
#print axioms Hashtree.Asm.X86.getG_sh_id
#print axioms Hashtree.Asm.X86.gCtl_ok_region
#print axioms Hashtree.Asm.X86.gCtl_sh_id
#print axioms Hashtree.Asm.X86.setVec_sh
#print axioms Hashtree.Asm.X86.setG_ptr_sh
#print axioms Hashtree.Asm.X86.okOr_pure_sh
#print axioms Hashtree.Asm.X86.okOr_bind_sh
#print axioms Hashtree.Asm.X86.okOr_bind2_sh
#print axioms Hashtree.Asm.X86.okOr_throw_sh
#print axioms Hashtree.Asm.X86.okOr_bind_err_sh
#print axioms Hashtree.Asm.X86.exec_sh

-- R5: the windows body run (renaming + pc re-basing + stack shift compose)
#print axioms Hashtree.Asm.X86.shSt_shiftPc
#print axioms Hashtree.Asm.X86.shSt_renSt
#print axioms Hashtree.Asm.X86.hns_ren
#print axioms Hashtree.Asm.X86.hns_shiftPc
#print axioms Hashtree.Asm.X86.frameSafe_shiftTgt
#print axioms Hashtree.Asm.X86.okI_shiftTgt
#print axioms Hashtree.Asm.X86.exec_wx
#print axioms Hashtree.Asm.X86.run_wx

-- R5: the NoStackVal engine and the run_wx body-slice composition
#print axioms Hashtree.Asm.X86.nsSafeB_iff
#print axioms Hashtree.Asm.X86.exec_ns
#print axioms Hashtree.Asm.X86.run_ns
#print axioms Hashtree.Asm.X86.run_wx_body
#print axioms Hashtree.Proofs.WinSseBody.sse_body_run
#print axioms Hashtree.Proofs.WinAvxBody.avx_body_run

-- R5: flags-insensitivity of the shani_x2 body entry (linux sub rsp,88 vs windows sub rsp,248)
#print axioms Hashtree.Proofs.WinShaniFlags.exec_vload_ok
#print axioms Hashtree.Proofs.WinShaniFlags.exec_lea_ok
#print axioms Hashtree.Proofs.WinShaniFlags.exec_cmp64_ok
#print axioms Hashtree.Proofs.WinShaniFlags.run_four_flags
#print axioms Hashtree.Proofs.WinShaniFlags.run_flags

-- R5: shani epilogue replay (12 exec steps: 10 vload restores, add rsp, ret) and the
-- save-log readback used to identify what each restore loads.
#print axioms Hashtree.Proofs.WinShaniEpi.lookup_laneLog_lane
#print axioms Hashtree.Proofs.WinShaniEpi.readCell_laneLog_pre
#print axioms Hashtree.Proofs.WinShaniEpi.loadLane_laneLog
#print axioms Hashtree.Proofs.WinShaniEpi.loadLanes_laneLog
#print axioms Hashtree.Proofs.WinShaniEpi.lookup_saveLog_from
#print axioms Hashtree.Proofs.WinShaniEpi.loadLanes_save
#print axioms Hashtree.Proofs.WinShaniEpi.readVSrc_save
#print axioms Hashtree.Proofs.WinShaniEpi.epi_lookup
#print axioms Hashtree.Proofs.WinShaniEpi.exec_add64_rsp
#print axioms Hashtree.Proofs.WinShaniEpi.exec_ret_ok
#print axioms Hashtree.Proofs.WinShaniEpi.loadVal_mem_eq
#print axioms Hashtree.Proofs.WinShaniEpi.epiSt_getV_after
#print axioms Hashtree.Proofs.WinShaniEpi.run_epi
#print axioms Hashtree.Proofs.WinShaniEpi.run_epilogue
#print axioms Hashtree.Proofs.WinShaniEpi.run_epilogue_getV
#print axioms Hashtree.Proofs.WinShaniEpi.epiFinal_getG_rsp

-- R5: the shani_x2 complete-call composition (prologue + flags + seed + body transfer +
-- epilogue).  The body-exit facts are hypotheses of the composition, not axioms.
#print axioms Hashtree.Proofs.WinShaniCall.seedSt_getG
#print axioms Hashtree.Proofs.WinShaniCall.renSt_getG16
#print axioms Hashtree.Proofs.WinShaniCall.saveSt_getG
#print axioms Hashtree.Proofs.WinShaniCall.shani_seed_eq
#print axioms Hashtree.Proofs.WinShaniCall.bodyExit_getG_rsp
#print axioms Hashtree.Proofs.WinShaniCall.shani_call_run
#print axioms Hashtree.Proofs.WinShaniCall.shani_call
#print axioms Hashtree.Proofs.WinShaniCall.shani_call_getV
#print axioms Hashtree.Proofs.WinShaniCall.shani_call_halted
#print axioms Hashtree.Proofs.WinShaniCall.shani_call_rsp

-- R5: the body-exit stack footprint of the windows shani_x2 body (write log outside the save
-- area, rsp invariance, kernel scans of the linux body) and the call composition with
-- hW/hmem/hrsp discharged.  U6 (avx512_x16 xmm6-xmm15 clobbers) is still deferred.
#print axioms Hashtree.Proofs.WinShaniWrite.wSafeB_iff
#print axioms Hashtree.Proofs.WinShaniWrite.exec_write_log
#print axioms Hashtree.Proofs.WinShaniWrite.run_write_log
#print axioms Hashtree.Proofs.WinShaniExit.exec_rsp_ns
#print axioms Hashtree.Proofs.WinShaniExit.run_rsp
#print axioms Hashtree.Proofs.WinShaniExit.shani_linux_ns
#print axioms Hashtree.Proofs.WinShaniExit.shani_linux_ws
#print axioms Hashtree.Proofs.WinShaniExit.shani_hnsI
#print axioms Hashtree.Proofs.WinShaniExit.shani_hwsI
#print axioms Hashtree.Proofs.WinShaniExit.f_ne4
#print axioms Hashtree.Proofs.WinShaniExit.seed_ns
#print axioms Hashtree.Proofs.WinShaniExit.seed_rsp
#print axioms Hashtree.Proofs.WinShaniExit.shani_body_log
#print axioms Hashtree.Proofs.WinShaniExit.shani_call_mem

-- R5: the windows/amd64 wrapper `HashtreeHash` (Kernels/X86Win/WrapperWindows): the symbolic
-- prefix and call state, the ANDQ alignment, the CALL marker, the epilogue, and the composition
-- with a kernel contract at the windows call state `entryWin`.  Both the shipped frame ($1024;
-- the text's ADDQ $2048 puts the call stack above the entry rsp, so the composition needs the
-- kernel-write separation hD9) and the fixed frame ($2048; linux-like footprint) are proved.
#print axioms Hashtree.Proofs.WinWrapper.slicePreW_shipped
#print axioms Hashtree.Proofs.WinWrapper.slicePreW_fixed
#print axioms Hashtree.Proofs.WinWrapper.KCW_shape_shipped
#print axioms Hashtree.Proofs.WinWrapper.KCW_shape_fixed
#print axioms Hashtree.Proofs.WinWrapper.KCW_head_shipped
#print axioms Hashtree.Proofs.WinWrapper.KCW_mem_split_shipped
#print axioms Hashtree.Proofs.WinWrapper.markerW_lk_shipped
#print axioms Hashtree.Proofs.WinWrapper.bpW_lk_shipped
#print axioms Hashtree.Proofs.WinWrapper.align_homW_shipped
#print axioms Hashtree.Proofs.WinWrapper.align_homW_fixed
#print axioms Hashtree.Proofs.WinWrapper.push_homW
#print axioms Hashtree.Proofs.WinWrapper.post_runW
#print axioms Hashtree.Proofs.WinWrapper.wrapper_kernelW_core
#print axioms Hashtree.Proofs.WinWrapper.wrapper_kernelW_fixed
#print axioms Hashtree.Proofs.WinWrapper.wrapper_kernelW_shipped
#print axioms Hashtree.Proofs.WinWrapper.wrapper_correctW
#print axioms Hashtree.Proofs.WinWrapper.argCells_specW
#print axioms Hashtree.Proofs.WinWrapper.wrapper_hyps_satW
#print axioms Hashtree.Proofs.WinWrapper.wrapper_hyps_satW_fixed
#print axioms Hashtree.Proofs.WinWrapper.wrapper_hyps_satW_shipped

-- R5: the concrete corruption witness for the shipped $1024 frame.  The avx2_x8 loop body is
-- sequential from the guard (pc 24) to the loop-back (pc 6085), so it executes the input-derived
-- 32-byte store at pc 442; with the shipped frame the body rsp is E-264 or E-280, so the store
-- interval covers the Go saved-BP word [E-8,E) and return address [E,E+8) that post F reads.
#print axioms Hashtree.Proofs.WinShippedClobber.avx2x8_input_load_pc
#print axioms Hashtree.Proofs.WinShippedClobber.avx2x8_store_pc
#print axioms Hashtree.Proofs.WinShippedClobber.avx2x8_loop_guard
#print axioms Hashtree.Proofs.WinShippedClobber.avx2x8_body_sequential_scan
#print axioms Hashtree.Proofs.WinShippedClobber.avx2x8_body_sequential
#print axioms Hashtree.Proofs.WinShippedClobber.shippedCallRsp_cases
#print axioms Hashtree.Proofs.WinShippedClobber.shippedBodyRsp_cases
#print axioms Hashtree.Proofs.WinShippedClobber.shippedBodyRsp_store_covers_go_frame
#print axioms Hashtree.Proofs.WinShippedClobber.shipped_avx2x8_store_clobbers_go_frame
#print axioms Hashtree.Proofs.WinShippedClobber.shipped_avx2x8_store_clobbers_go_frame_sigma

-- R5: seed alignment against the linux certificates.  The windows shani_x2 body run starts from
-- WinShaniCall.seedSt; a linux functional certificate would have to start from that same state.
-- The seed at the windows call state entryWin has rbx = ptr (rStack, sigma 6) (the Win64 rbp),
-- rbp = a number (the Win64 rdi), r8 = ptr (rStack, sigma 5) (the Win64 rbx), while
-- X86Sym.entryS (ShaniAll) has rbx a number and X86SymW.entryW (ShaniW) has rbp a stack pointer
-- and r8 a number; mapVal preserves the constructor, so no symbol choice aligns the states.
#print axioms Hashtree.Proofs.WinShaniSeedAlign.mapState_getG
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryWin_gpr5
#print axioms Hashtree.Proofs.WinShaniSeedAlign.seed_gpr3
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryS24_gpr3
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryS_gpr3
#print axioms Hashtree.Proofs.WinShaniSeedAlign.seed_ne_entryS
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryW_gpr5
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryW_gpr8
#print axioms Hashtree.Proofs.WinShaniSeedAlign.seed_gpr5
#print axioms Hashtree.Proofs.WinShaniSeedAlign.seed_gpr8
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryW_getG5
#print axioms Hashtree.Proofs.WinShaniSeedAlign.entryW_getG8
#print axioms Hashtree.Proofs.WinShaniSeedAlign.seed_ne_entryW
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_body_rbw_linux
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_body_rbw_windows

-- R5: the run-invariance engine (Asm/RunAgree).  `Agree R s1 s2`: equal on everything but the
-- general registers outside R and the branch assumptions; `exec_agree` is the one-step lemma over
-- the completed `srcs`/`dsts` scan of Asm/BodyReads (every Instr constructor), `run_agree` the
-- fetch-execute lift with a per-pc live-set certificate `Cert` (decided by `certB`, computed by
-- `live`).  The shani instances: both programs certified, and the body entry live sets are the
-- rbw tables ([2,6,4,7] linux pc 1, [8,2,4,1] windows pc 11).
#print axioms Hashtree.Asm.RunAgree.exec_agree
#print axioms Hashtree.Asm.RunAgree.run_agree
#print axioms Hashtree.Asm.RunAgree.Cert_of_certB
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_linux_certB
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_windows_certB
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_linux_cert
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_windows_cert
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_linux_live_entry
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_windows_live_entry
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_linux_live_entry_eq
#print axioms Hashtree.Proofs.WinShaniSeedAlign.shani_windows_live_entry_eq
