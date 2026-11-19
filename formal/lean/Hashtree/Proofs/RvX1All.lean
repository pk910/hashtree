import Hashtree.Gen.RvX1L.It.Final
import Hashtree.Gen.RvX1L.T0.Final
import Hashtree.Proofs.RvAll
import Hashtree.Asm.RiscvReach

/-!
# `hashtree_sha256_riscv_x1` is correct for every count

Segments: the prologue from the entry to the loop head (one slice; its saves stay in the log handed
to the loop), one block iteration `KH → KH` under the substitution `It.tauE`, and the exit from `KH`
at count 0.  `rv_loop` (the induction) starts on the prologue's log and moves it into the frame at
every iteration; `mem0sT` reads the save slots back as memory keys at the exit.

Glued by induction: started on any well-formed memory whose input buffer holds `inp`, the kernel
returns via `ret` without a model error after `H + c * IT + EX` instructions, writes only the
`32 c` output bytes and bytes of its 80-byte frame, and output byte `32 n + 4 i + b` is byte
`4 i + b` of SHA-256 of block `n`.

The count's range (`0 ≤ σ 2`, `32 * σ 2 < 2 ^ 63`) is required by the prologue's `slli` (the RV64
model records the no-wrap condition as an assumption).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.RvX1L
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym Hashtree.Kernels.Riscv.X1
  Hashtree.Asm.SpecQ Hashtree.Spec Hashtree.Proofs.Rv Hashtree.Gen.RvX1L

/-- The instruction count of a call with `c` blocks. -/
def steps (c : Nat) : Nat := H + c * IT + EX

theorem IT_eq : IT = It.NS := by decide +kernel

theorem EX_eq : EX = T0.NS := by decide +kernel

/-- The prologue's slice check: `H` steps from the entry reach `KP`. -/
theorem proSlice : rvSliceCheck prog pe M0 (fun _ => false) H (entryS 0) KP [] = true := by
  decide +kernel

theorem tau0 (σ : Nat → Int) : sigmaOf It.tauE σ 0 = 64 + σ 0 := by
  simp only [sigmaOf, tauAt, It.tauE, List.getD_cons_zero, Lin.eval, dotC, Lin.sym]
  simp

theorem tau1 (σ : Nat → Int) : sigmaOf It.tauE σ 1 = 32 + σ 1 := by
  simp only [sigmaOf, tauAt, It.tauE, List.getD_cons_zero, List.getD_cons_succ, Lin.eval, dotC,
    Lin.sym]
  simp

theorem tau2 (σ : Nat → Int) : sigmaOf It.tauE σ 2 = -1 + σ 2 := by
  simp only [sigmaOf, tauAt, It.tauE, List.getD_cons_zero, List.getD_cons_succ, Lin.eval, dotC,
    Lin.sym]
  simp

/-- The iteration's end cut, restarted as the loop head under `It.tauE`. -/
theorem itReach (e : Key → W32) (σ : Nat → Int) :
    mapState (It.EF e) σ It.KF =
      X86.fr (It.Rlast.mem.map (fun p => (mapAddr σ p.1, mapCell (It.E129 e) σ p.2)))
        (mapState (It.EF e) (sigmaOf It.tauE σ) KH) := by
  simp only [It.EF, It.KF]
  rw [It.KF_eq]
  exact mapState_reached_vars (It.E129 e) σ It.Rlast KH It.tauE It.KF_cutok KH_len
    (gprLiveRel_sound It.KF_live)
    It.KF_pc It.KF_halted It.KF_err It.KF_tail It.KF_vr KH_vr It.KF_flags KH_fl KH_mem

/-- **`hashtree_sha256_riscv_x1` is correct for every count.**  Called (LP64D) with `c` blocks, on
any well-formed memory whose input buffer holds `inp`: it returns via `ret` without a model error
after `steps c` instructions, it wrote only the `32 c` output bytes and bytes of its stack frame,
and output byte `32 n + 4 i + b` is byte `4 i + b` of SHA-256 of block `n`. -/
theorem correct (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemR 10 11 rodata gotT mem0c) (he : X86Sym.EnvMem env0 σ mem0c) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := Riscv.run prog pe mem0c orcC (steps c) (mapState env0 σ (entryS 0))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧
      ∀ r ∈ [2], fin.getG r = (mapState env0 σ (entryS 0)).getG r := by
  have hrel : Mem0Rel env0 σ (mem0s 10 11 rodata gotT) mem0c :=
    mem0RelR_of_wf 10 11 rodata gotT env0 σ mem0c hw he
  have hPr := (rvSlice_sound env0 σ (mem0s 10 11 rodata gotT) mem0c hrel prog pe
    (fun _ => false) orcC H (entryS 0) KP [] proSlice rfl
    (assumeOk_of σ KP Ahead KP_assume (asmHead σ hσ0 hb))).1
  have hR : InRange (σ 1) 0
      (KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 Rhead) σ p.2))) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := head_addrs q hq
    right
    simp only [mapAddr, Lin.eval, dotC, h2, h1]
    refine ⟨trivial, ?_, ?_⟩ <;> omega
  have hO : OutOk inp (σ 1) 0
      (KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 Rhead) σ p.2))) :=
    fun n _ _ hn => by omega
  have hsave : ∀ o ∈ SAVES, ∃ x,
      X86.view (KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 Rhead) σ p.2))) mem0c
        ⟨rStack, o⟩ = .dat x (((o + 16) % 4).toNat) := by
    intro o ho
    obtain ⟨x, hx⟩ := saveOk (envAbs env0 Rhead) σ o ho
    refine ⟨x, ?_⟩
    rw [KP_mem]
    simp only [X86.view, hx]
  simp only [steps]
  have hidx : H + c * IT + EX = H + (c * It.NS + T0.NS) := by
    rw [IT_eq, EX_eq]; omega
  have hPr' : run prog pe mem0c orcC H (mapState env0 σ (entryS 0)) =
      mapState (envAbs env0 Rhead) σ KP := hPr
  rw [hidx, rvRun_add, hPr', KH_map (envAbs env0 Rhead) σ]
  obtain ⟨hh, he', ht, hR', hO', hreg'⟩ :=
    rv_loop prog pe rodata gotT SAVES KH It.KF It.Rlast It.tauE It.EF It.E129 It.NS T0.NS
      KH_len KH_vr tau0 tau1 tau2 SAVES_lo KH_fl KH_mem KH_nOnly
      (fun e σ m o hm h2 => It.run_final e σ m o (by simpa only [M0] using hm) (by omega))
      itReach
      (fun inp e σ hm => It.out_final inp e σ hm)
      It.log_final
      [2] (entryS 0)
      (by
        intro e σ r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rw [hr, getG_hom, getG_hom]
        simp only [State.getG, entryS, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.map_cons, List.map_nil,
          mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC]
        rfl)
      (by
        intro e σ₁ σ₂ σ₃ m r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rw [hr, getG_hom, getG_hom]
        simp only [State.getG, entryS, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.map_cons, List.map_nil,
          mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC]
        rfl)
      (fun e σ m o hm h2 =>
        ⟨_, T0.run_final e σ m o (by simpa only [T0.M0T] using hm) h2,
          by simpa only [T0.KF, mapState] using T0.KF_halted,
          by simpa only [T0.KF, mapState] using T0.KF_err,
          by simpa only [T0.KF, mapState] using T0.KF_tail,
          by
            simp only [T0.KF, mapState]
            rw [show T0.K1.mem = [] from T0.KF_mem]
            rfl,
          by
            intro r hr
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
            rw [hr, getG_hom]
            have hk : T0.K1.getG 2 = (.ptr (⟨rStack, Lin.ofInt 0⟩ : Addr Lin)) := by rfl
            rw [hk]
            simp only [getG_hom, State.getG, entryS, List.getD_eq_getElem?_getD,
              List.getElem?_map, List.getElem?_cons_zero, List.getElem?_cons_succ, List.map_cons,
              List.map_nil, mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC]
            rfl⟩)
      inp mem0c hw (σ 0) (σ 1) hin orcC c 0 σ (envAbs env0 Rhead)
      (KP.mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs env0 Rhead) σ p.2)))
      (by omega) (by omega) hc hR hO hsave
  refine ⟨hh, he', ht, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_zero, Nat.zero_add] using hR'
  · simpa only [Nat.zero_add] using hO'
  · intro r hr
    have h2 := hreg' r hr
    have hmap : (mapState (envAbs env0 Rhead) σ (entryS 0)).getG 2 =
        (mapState env0 σ (entryS 0)).getG 2 := by
      rw [getG_hom, getG_hom]
      simp only [State.getG, entryS, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.map_cons, List.map_nil,
        mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC]
      rfl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    subst hr
    simpa only [Nat.zero_add] using h2.trans hmap

end Hashtree.Proofs.RvX1L
