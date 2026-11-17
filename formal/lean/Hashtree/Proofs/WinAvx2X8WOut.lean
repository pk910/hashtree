import Hashtree.Proofs.WinAvx2X8WLoop
import Hashtree.Proofs.WinWrapper

/-!
# R5: the output contract of the windows avx2_x8 W-mode loop — the statement

`TurnOut8W` / `TurnOut8WLast` (for R2c): the windows counterparts of
`WinAvx2X8Bridge.TurnOut8` / `TurnOut8Last`, over the windows-stream W-mode loop
`WinAvx2X8WAll.x8w_runW_abi` / `x8w_runW_last_abi` (built on the pilot `Gen/WinAvx2X8P`, started
at the wrapper call state `entryWin`), stated against exactly their runs (the step counts are
the literals of those statements, `x8wRunSteps_eq`).  Footprint: the caller log, the finished
output blocks, and the kernel frame `[σ 9 - D8, σ 9)` (`D8 = 1296`: `push rbp; push rsi`, the
alignment residue `r ∈ {8, 24}`, `sub rsp,1248`; the `r12..r15` and `ymm6..15` saves are inside
it).  With the exit-register facts of `KTE r`/`KTEs r` (`exitGprW`) they give the avx2_x8
link `KSpecC8`.  Statements only: nothing here is proved.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinAvx2X8WOut

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.WinWrapper (entryWin OutOk)

/-- The step count of `x8w_runW_abi` for `j` further turns. -/
def x8wRunSteps (j : Nat) : Nat :=
  24 + (Hashtree.Proofs.WinAvx2X8WLoop.TURNLEN + (j * Hashtree.Proofs.WinAvx2X8WLoop.TURNLEN +
    (Hashtree.Proofs.WinAvx2X8W.BODYLEN + 42)))

/-- The step count of `x8w_runW_last_abi` (`8 ≤ c < 16`). -/
def x8wLastSteps : Nat := 24 + (Hashtree.Proofs.WinAvx2X8W.BODYLEN + 42)

/-- The stack depth of the windows avx2_x8 frame below the return marker. -/
def D8 : Nat := 1296

/-- **`TurnOut8W` (to be proved by R2c):** at `c = 8 (j + 1) + s`, `8 ≤ s < 16`. -/
def TurnOut8W : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 8 ≤ s → s < 16 →
    σ 2 = 8 * ((j : Int) + 1) + (s : Int) → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC (x8wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - D8 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC (x8wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem

/-- **`TurnOut8WLast` (to be proved by R2c):** at `8 ≤ c < 16` (one pass, 8 blocks). -/
def TurnOut8WLast : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 8 ≤ σ 2 → σ 2 < 16 → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC x8wLastSteps
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - D8 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC x8wLastSteps
        (fr M (mapState env0 σ entryWin))).mem

/-- The runs above are the runs of `x8w_runW_abi` / `x8w_runW_last_abi` (same literals). -/
theorem x8wRunSteps_eq (j : Nat) : x8wRunSteps j =
    24 + (Hashtree.Proofs.WinAvx2X8WLoop.TURNLEN + (j * Hashtree.Proofs.WinAvx2X8WLoop.TURNLEN +
      (Hashtree.Proofs.WinAvx2X8W.BODYLEN + 42))) := rfl

theorem x8wLastSteps_eq : x8wLastSteps = 24 + (Hashtree.Proofs.WinAvx2X8W.BODYLEN + 42) := rfl

end Hashtree.Proofs.WinAvx2X8WOut
