import Hashtree.Proofs.WinAvxX4WAll
import Hashtree.Proofs.WinWrapper

/-!
# R5: the output contract of the windows avx_x4 W-mode loop — the statement

`TurnOut4W` / `TurnOut4WLast` (for R2c): the windows counterparts of `WinAvxX4Bridge.TurnOut4`,
over R2's windows-stream W-mode loop `WinAvxX4WAll.x4w_runW_all` / `x4w_runW_last_all` (built on
the pilot `Gen/WinAvxX4P`, started at the wrapper call state `entryWin`), stated against exactly
their runs.  Footprint: the caller log, the finished output blocks, the kernel frame
`[σ 9 - 568, σ 9)` (`sub rsp,568`; the `xmm6..15` saves at `[rsp+384, rsp+544)` are inside it).
With the exit-register facts of `KTE`/`KTEs`/`KSmW` they give the avx_x4 link's `X4WinCert`.
Statements only: nothing here is proved.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinAvxX4WOut

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.WinWrapper (entryWin OutOk)

/-- The step count of `x4w_runW_all` for `j` further turns. -/
def x4wRunSteps (j : Nat) : Nat :=
  16 + (Hashtree.Proofs.WinAvxX4WLoop.TURNLEN + (j * Hashtree.Proofs.WinAvxX4WLoop.TURNLEN +
    (Hashtree.Proofs.WinAvxX4WBody.BODYLEN + 37)))

/-- The step count of `x4w_runW_last_all` (`4 ≤ c < 8`). -/
def x4wLastSteps : Nat := 16 + (Hashtree.Proofs.WinAvxX4WBody.BODYLEN + 37)

/-- **`TurnOut4W` (to be proved by R2c):** at `c = 4 (j + 1) + s`, `4 ≤ s < 8`. -/
def TurnOut4W : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 4 ≤ s → s < 8 →
    σ 2 = 4 * ((j : Int) + 1) + (s : Int) →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC (x4wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (4 * (j + 2))
      (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC (x4wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem

/-- **`TurnOut4WLast` (to be proved by R2c):** at `4 ≤ c < 8` (one pass, 4 blocks). -/
def TurnOut4WLast : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 4 ≤ σ 2 → σ 2 < 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC x4wLastSteps
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 4
      (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC x4wLastSteps
        (fr M (mapState env0 σ entryWin))).mem

/-- The runs above are the runs of `x4w_runW_all` / `x4w_runW_last_all` (same literals). -/
theorem x4wRunSteps_eq (j : Nat) : x4wRunSteps j =
    16 + (Hashtree.Proofs.WinAvxX4WLoop.TURNLEN + (j * Hashtree.Proofs.WinAvxX4WLoop.TURNLEN +
      (Hashtree.Proofs.WinAvxX4WBody.BODYLEN + 37))) := rfl

end Hashtree.Proofs.WinAvxX4WOut
