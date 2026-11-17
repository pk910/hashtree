import Hashtree.Proofs.WinShani
import Hashtree.Proofs.WinFrameStack
import Hashtree.Proofs.WinSafeScan

/-!
# R5: the `shani_x2` windows body transfer

The windows `shani_x2` stream is the linux stream with a Win64 prologue, the general registers
renamed (`Proofs.WinShani.F`/`G`), the body re-based by ten instructions and every `rsp`-relative
displacement grown by `160` (`Proofs.WinShani.shani_body_correspondence`):

```
linux   : sub rsp,88 ; <body at pc 1, 668 instructions>
windows : sub rsp,248 ; 10 xmm6-xmm15 saves at [rsp, rsp+160) ; <body at pc 11, 668 instructions>
```

The two frames sit at the same addresses: the windows `rsp` is `160` lower and every displacement
is `160` larger, so `δ + d = 0` and `Proofs.WinFrameStack.effAddr_mv` applies.

This module instantiates the composed transfer engine on the shipped arrays:

* `body_safe` -- kernel-checked scan: every instruction of the linux body slice
  (`linuxProg.toList.drop 1 |>.take 668`) satisfies `okI` and `frameSafe`.  The frame side
  condition is decided through the Boolean mirror `Proofs.WinSafeScan.frameSafeB`, because the
  `Decidable` instance of `frameSafe` is not kernel-reducible (`mSafe` branches);
* `body_hmap` -- the pointwise correspondence at windows index `10 + j` (from
  `shani_body_correspondence`);
* `shani_body_transfer` -- **the body contract**: `n` steps of the windows program from the
  translated body-entry state are exactly the translation of the `n` linux steps, as long as the
  linux run stays inside the body slice (`hcond`).

What is *not* proved here (recorded in `formal/notes/R5.md`): the prologue/epilogue link (that
running the eleven windows prologue instructions from an ABI state reached by a Go call lands in
the translated body-entry state, and the epilogue returns the mirrored registers), and the
functional contract itself.
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinShani
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinShaniTransfer

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Shani.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

/-! ## The body slice of the shipped streams -/

/-- Kernel-checked: every instruction of the 668-instruction linux body slice is `okI` and
`frameSafe`.  No `native_decide`; the scan is a list fold over the sliced streams (no array
indexing, see `Proofs.WinScan`). -/
theorem body_safe : ((linuxProg.toList.drop 1).take 668).all safeB = true := by
  decide +kernel

/-- A member of the body slice satisfies the side condition of the transfer engine. -/
theorem body_safe_mem {i : Instr} (hm : i ∈ (linuxProg.toList.drop 1).take 668) :
    okI i ∧ frameSafe i :=
  safeB_and (List.all_eq_true.mp body_safe i hm)

/-- The body correspondence at windows index `10 + j`, in the form `run_comb` wants. -/
theorem body_hmap : ∀ j, 1 ≤ j → j < 669 →
    winProg[10 + j]? = (linuxProg[j]?).map (bodyI F 160 10) := by
  intro j h1 h2
  have hbl : bodyLen = 668 := rfl
  have h := shani_body_correspondence (j - 1) (by omega)
  have e1 : 11 + (j - 1) = 10 + j := by omega
  have e2 : 1 + (j - 1) = j := by omega
  rwa [e1, e2] at h

/-- Every instruction of the linux body slice is `okI` and `frameSafe`. -/
theorem body_hside : ∀ (pc : Nat), 1 ≤ pc → pc < 669 → ∀ (x : Instr),
    linuxProg[pc]? = some x → okI x ∧ frameSafe x := by
  intro pc h1 h2 x hx
  have hj : pc - 1 < 668 := by omega
  have hmem : x ∈ (linuxProg.toList.drop 1).take 668 := by
    refine List.mem_iff_getElem?.mpr ⟨pc - 1, ?_⟩
    rw [List.getElem?_take, if_pos hj, List.getElem?_drop]
    rw [show 1 + (pc - 1) = pc from by omega]
    simpa only [Array.getElem?_toList] using hx
  exact body_safe_mem hmem

/-- The body slice ends before the end of the linux stream. -/
theorem hi_le : 669 ≤ linuxProg.size := by decide +kernel

/-! ## The body contract -/

/-- **The `shani_x2` body transfer.**  `n` steps of the windows stream from the translated
body-entry state are the translation of the `n` steps of the linux body, for as long as the linux
run stays inside its body slice (the body is a loop; `hcond` is the usual slice invariant). -/
theorem shani_body_transfer (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (n : Nat) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k s).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k s).pc ∧ (run linuxProg ro mem0 orc k s).pc < 669)) :
    run winProg ro mem0 orc n (shiftPc 10 (renSt F G (spSt (-160) s)))
      = shiftPc 10 (renSt F G (spSt (-160) (run linuxProg ro mem0 orc n s))) :=
  run_comb (F := F) (G := G) renPerm (-160) 160 (by omega) 1 669 hi_le
    body_hmap body_hside n s hlen hcond

end Hashtree.Proofs.WinShaniTransfer
