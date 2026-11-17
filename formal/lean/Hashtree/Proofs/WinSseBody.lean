import Hashtree.Proofs.WinNs
import Hashtree.Proofs.WinSseX1

/-!
# R5: the `run_wx` composition over the body slice of the windows `sse_x1` kernel

`run_wx_body` (`Proofs/WinNs.lean`) turns the instruction-for-instruction correspondence of the
two shipped streams into a statement about whole runs of the shared body slice, given five side
conditions on the slice.  This module discharges all five for `sse_x1` (linux body pcs
`7..4186`, windows body pcs `18..4197`, 4180 instructions, pc shift 11):

* `hmap`   -- `sse_hmap`, from the shipped correspondence `sse_body_correspondence`;
* `hokI`   -- `sse_hokI`, from a kernel-checked `safeB` scan of the linux body;
* `hnsI`   -- `sse_hnsI`, from a kernel-checked `nsSafeB` scan of the linux body;
* `hframe` -- `sse_hframe`, from a kernel-checked `frameSafeB` scan of the windows body;
* `hG4`    -- `sse_hG4`, the sixteen-register inverse-permutation check.

The scans are `decide +kernel` (no `native_decide`), chunked 2048 instructions at a time.
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinScan
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinSseBody

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.SseX1.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.SseX1.prog
abbrev F : Nat → Nat := Hashtree.Proofs.WinSseX1.F
abbrev G : Nat → Nat := Hashtree.Proofs.WinSseX1.G

/-! ## The permutation side condition -/

theorem sse_hG4 : ∀ j, j < 16 → j ≠ 4 → G j ≠ 4 := by
  apply Hashtree.Proofs.WinSseX1.all_fin
  decide

theorem sse_renPerm : RenPerm F G := Hashtree.Proofs.WinSseX1.renPerm

/-! ## The body correspondence in the shared `shiftTgt` -/

/-- The kernel module's local `shiftTgt` is the shared one. -/
theorem shiftTgt_eq (p : Nat) (i : Instr) :
    Hashtree.Proofs.WinSseX1.shiftTgt p i = shiftTgt p i := by
  cases i <;> rfl

theorem bodyI_eq (i : Instr) :
    Hashtree.Proofs.WinSseX1.bodyI F 11 i = shiftTgt 11 (rlI F i) := by
  unfold Hashtree.Proofs.WinSseX1.bodyI
  exact shiftTgt_eq 11 (rlI F i)

/-- The instruction at linux body pc `pc` corresponds to the windows instruction at `pc + 11`. -/
theorem sse_hmap : ∀ pc i, 7 ≤ pc → pc < 7 + 4180 → linuxProg[pc]? = some i →
    winProg[pc + 11]? = some (shiftTgt 11 (rlI F i)) := by
  intro pc i h1 h2 hp
  have h := Hashtree.Proofs.WinSseX1.sse_body_correspondence (pc - 7) (by simp only [Hashtree.Proofs.WinSseX1.bodyLen]; omega)
  have hidx1 : 18 + (pc - 7) = pc + 11 := by omega
  have hidx2 : 7 + (pc - 7) = pc := by omega
  rw [hidx2, hp, hidx1] at h
  simp only [Option.map_some] at h
  rw [h, bodyI_eq]

/-! ## The three kernel-checked slice scans -/

/-- Every instruction of the linux body is `okI` (the vector-shift and frame model applies). -/
theorem sse_linux_safe :
    ((linuxProg.toList.drop 7).take 4180).all safeB = true := by
  apply all_take_drop _ ((linuxProg.toList.drop 7).take 4180) 2048
  · decide +kernel
  apply all_take_drop _ (((linuxProg.toList.drop 7).take 4180).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- Every instruction of the linux body preserves the "no stack pointer in a register" invariant. -/
theorem sse_linux_ns :
    ((linuxProg.toList.drop 7).take 4180).all nsSafeB = true := by
  apply all_take_drop _ ((linuxProg.toList.drop 7).take 4180) 2048
  · decide +kernel
  apply all_take_drop _ (((linuxProg.toList.drop 7).take 4180).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- Every instruction of the windows body is frame-safe. -/
theorem sse_win_frame :
    ((winProg.toList.drop 18).take 4180).all frameSafeB = true := by
  apply all_take_drop _ ((winProg.toList.drop 18).take 4180) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 18).take 4180).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-! ## Pointwise side conditions -/

theorem sse_hokI : ∀ pc i, 7 ≤ pc → pc < 7 + 4180 → linuxProg[pc]? = some i → okI i := by
  intro pc i h1 h2 hp
  have hget : safeB i = true :=
    all_slice_get linuxProg.toList 7 4180 safeB sse_linux_safe (pc - 7) (by omega) i (by
      rw [show 7 + (pc - 7) = pc from by omega]
      simpa using hp)
  exact safeB_ok hget

theorem sse_hnsI : ∀ pc i, 7 ≤ pc → pc < 7 + 4180 → linuxProg[pc]? = some i → nsSafe i := by
  intro pc i h1 h2 hp
  have hget : nsSafeB i = true :=
    all_slice_get linuxProg.toList 7 4180 nsSafeB sse_linux_ns (pc - 7) (by omega) i (by
      rw [show 7 + (pc - 7) = pc from by omega]
      simpa using hp)
  exact (nsSafeB_iff i).mp hget

theorem sse_hframe : ∀ pc i, 7 ≤ pc → pc < 7 + 4180 → linuxProg[pc]? = some i →
    frameSafe (rlI F i) := by
  intro pc i h1 h2 hp
  have hx := sse_hmap pc i h1 h2 hp
  have hget : frameSafeB (shiftTgt 11 (rlI F i)) = true :=
    all_slice_get winProg.toList 18 4180 frameSafeB sse_win_frame (pc - 7) (by omega)
      (shiftTgt 11 (rlI F i)) (by
        rw [show 18 + (pc - 7) = pc + 11 from by omega]
        simpa using hx)
  exact (frameSafe_shiftTgt 11 (rlI F i)).mp ((frameSafeB_iff _).mp hget)

/-! ## The body-slice run -/

/-- `n` steps of the windows `sse_x1` stream started from the shifted state `winSt F G μ 11 s`
are the shifted image of the linux run, as long as the linux run stays inside the body slice
(or has halted).  This is the windows counterpart of the linux body lemma; only the prologue,
the epilogue and the functional contract remain to be composed around it. -/
theorem sse_body_run {ro : Region} (hro : ro ≠ rStack)
    {mem0w mem0l : Addr Int → Cell W32 Int} {orc : Nat → Bool} (μ : Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (n : Nat) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (hns0 : ∀ j, j ≠ 4 → NoStackVal (s.getG j))
    (hcond : ∀ k, k < n → (run linuxProg ro mem0l orc k s).halted = true ∨
      (7 ≤ (run linuxProg ro mem0l orc k s).pc ∧
        (run linuxProg ro mem0l orc k s).pc < 7 + 4180)) :
    run winProg ro mem0w orc n (winSt F G μ 11 s)
      = winSt F G μ 11 (run linuxProg ro mem0l orc n s) :=
  run_wx_body (F := F) (G := G) (linuxProg := linuxProg) (winProg := winProg)
    (p := 11) (base := 7) (L := 4180) μ sse_renPerm sse_hG4 hro h0 sse_hmap sse_hokI
    sse_hframe sse_hnsI (by decide +kernel) n s hlen hns0 hcond

end Hashtree.Proofs.WinSseBody
