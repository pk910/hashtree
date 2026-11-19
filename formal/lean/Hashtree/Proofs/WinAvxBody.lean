import Hashtree.Proofs.WinNs
import Hashtree.Proofs.WinAvxX1

/-!
# R5: the `run_wx` composition over the body slice of the windows `avx_x1` kernel

The `avx_x1` analogue of `Proofs/WinSseBody.lean` (linux body pcs `8..4056`, windows body pcs
`19..4067`, 4049 instructions, pc shift 11); see that module for the shape of the argument.
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinScan
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvxBody

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.AvxX1.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.AvxX1.prog
abbrev F : Nat → Nat := Hashtree.Proofs.WinAvxX1.F
abbrev G : Nat → Nat := Hashtree.Proofs.WinAvxX1.G

/-! ## The permutation side condition -/

theorem avx_hG4 : ∀ j, j < 16 → j ≠ 4 → G j ≠ 4 := by
  apply Hashtree.Proofs.WinAvxX1.all_fin
  decide

theorem avx_renPerm : RenPerm F G := Hashtree.Proofs.WinAvxX1.renPerm

/-! ## The body correspondence in the shared `shiftTgt` -/

theorem shiftTgt_eq (p : Nat) (i : Instr) :
    Hashtree.Proofs.WinAvxX1.shiftTgt p i = shiftTgt p i := by
  cases i <;> rfl

theorem bodyI_eq (i : Instr) :
    Hashtree.Proofs.WinAvxX1.bodyI F 11 i = shiftTgt 11 (rlI F i) := by
  unfold Hashtree.Proofs.WinAvxX1.bodyI
  exact shiftTgt_eq 11 (rlI F i)

/-- The instruction at linux body pc `pc` corresponds to the windows instruction at `pc + 11`. -/
theorem avx_hmap : ∀ pc i, 8 ≤ pc → pc < 8 + 4049 → linuxProg[pc]? = some i →
    winProg[pc + 11]? = some (shiftTgt 11 (rlI F i)) := by
  intro pc i h1 h2 hp
  have h := Hashtree.Proofs.WinAvxX1.avx_body_correspondence (pc - 8) (by simp only [Hashtree.Proofs.WinAvxX1.bodyLen]; omega)
  have hidx1 : 19 + (pc - 8) = pc + 11 := by omega
  have hidx2 : 8 + (pc - 8) = pc := by omega
  rw [hidx2, hp, hidx1] at h
  simp only [Option.map_some] at h
  rw [h, bodyI_eq]

/-! ## The three kernel-checked slice scans -/

theorem avx_linux_safe :
    ((linuxProg.toList.drop 8).take 4049).all safeB = true := by
  apply all_take_drop _ ((linuxProg.toList.drop 8).take 4049) 2048
  · decide +kernel
  apply all_take_drop _ (((linuxProg.toList.drop 8).take 4049).drop 2048) 2048
  · decide +kernel
  decide +kernel

theorem avx_linux_ns :
    ((linuxProg.toList.drop 8).take 4049).all nsSafeB = true := by
  apply all_take_drop _ ((linuxProg.toList.drop 8).take 4049) 2048
  · decide +kernel
  apply all_take_drop _ (((linuxProg.toList.drop 8).take 4049).drop 2048) 2048
  · decide +kernel
  decide +kernel

theorem avx_win_frame :
    ((winProg.toList.drop 19).take 4049).all frameSafeB = true := by
  apply all_take_drop _ ((winProg.toList.drop 19).take 4049) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 19).take 4049).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-! ## Pointwise side conditions -/

theorem avx_hokI : ∀ pc i, 8 ≤ pc → pc < 8 + 4049 → linuxProg[pc]? = some i → okI i := by
  intro pc i h1 h2 hp
  have hget : safeB i = true :=
    all_slice_get linuxProg.toList 8 4049 safeB avx_linux_safe (pc - 8) (by omega) i (by
      rw [show 8 + (pc - 8) = pc from by omega]
      simpa using hp)
  exact safeB_ok hget

theorem avx_hnsI : ∀ pc i, 8 ≤ pc → pc < 8 + 4049 → linuxProg[pc]? = some i → nsSafe i := by
  intro pc i h1 h2 hp
  have hget : nsSafeB i = true :=
    all_slice_get linuxProg.toList 8 4049 nsSafeB avx_linux_ns (pc - 8) (by omega) i (by
      rw [show 8 + (pc - 8) = pc from by omega]
      simpa using hp)
  exact (nsSafeB_iff i).mp hget

theorem avx_hframe : ∀ pc i, 8 ≤ pc → pc < 8 + 4049 → linuxProg[pc]? = some i →
    frameSafe (rlI F i) := by
  intro pc i h1 h2 hp
  have hx := avx_hmap pc i h1 h2 hp
  have hget : frameSafeB (shiftTgt 11 (rlI F i)) = true :=
    all_slice_get winProg.toList 19 4049 frameSafeB avx_win_frame (pc - 8) (by omega)
      (shiftTgt 11 (rlI F i)) (by
        rw [show 19 + (pc - 8) = pc + 11 from by omega]
        simpa using hx)
  exact (frameSafe_shiftTgt 11 (rlI F i)).mp ((frameSafeB_iff _).mp hget)

/-! ## The body-slice run -/

theorem avx_body_run {ro : Region} (hro : ro ≠ rStack)
    {mem0w mem0l : Addr Int → Cell W32 Int} {orc : Nat → Bool} (μ : Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (n : Nat) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (hns0 : ∀ j, j ≠ 4 → NoStackVal (s.getG j))
    (hcond : ∀ k, k < n → (run linuxProg ro mem0l orc k s).halted = true ∨
      (8 ≤ (run linuxProg ro mem0l orc k s).pc ∧
        (run linuxProg ro mem0l orc k s).pc < 8 + 4049)) :
    run winProg ro mem0w orc n (winSt F G μ 11 s)
      = winSt F G μ 11 (run linuxProg ro mem0l orc n s) :=
  run_wx_body (F := F) (G := G) (linuxProg := linuxProg) (winProg := winProg)
    (p := 11) (base := 8) (L := 4049) μ avx_renPerm avx_hG4 hro h0 avx_hmap avx_hokI
    avx_hframe avx_hnsI (by decide +kernel) n s hlen hns0 hcond

end Hashtree.Proofs.WinAvxBody
