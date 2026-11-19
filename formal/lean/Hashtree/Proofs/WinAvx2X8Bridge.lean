import Hashtree.Proofs.WinAvxX4Bridge
import Hashtree.Kernels.X86.Avx2X8

/-!
# R5: the windows chain link `avx2_x8 -> avx_x4` — the statement

`KSpecC8`: the per-link obligation in the shape of `KSpecC512`/`KSpecC4`: from the wrapper's call
state, after `s8 c` steps the link has no error and either returned (`c = 0`, at pc 3, no
writes) or tail-called `hashtree_sha256_avx_x4` with `c - c % 8` blocks done and `c % 8`
remaining, on the avx_x4 entry live set `L4 = [8, 4, 2, 1]`.  Depth `D8 = 1296`: `push rbp`,
`push rsi`, `and rsp,-32` (at most 24 more bytes at `σ 9 % 16 = 8`) and `sub rsp,1248`; the
loop never touches the save slots `[896, 1248)` (R5.md section 11).

`TurnOut8` / `TurnOut8Last` (for R2c): the output bytes of R2's W-mode avx2_x8 loop
`Avx2X8WAll.x8_runW_abi` / `x8_runW_last_abi` (linux stream, rodata region 4, `σ 9 % 16 = 8`),
stated against exactly their runs.  The step counts are the literals of those statements
(`BODYLEN = 6035`, `TURNLEN = BODYLEN + 27 = 6062`); the `rfl` link to R2's names lands when
`research/formal-r2-amd64` is merged here.  Statements only: nothing here is proved.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinAvx2X8Bridge

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.X86Chain Hashtree.Proofs.WinChain
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink)

/-- The entry live set of the avx_x4 link (`[8, 4, 2, 1]`). -/
abbrev L4 : List Nat := Hashtree.Proofs.WinAvxX4Live.liveT.getD 0 []

/-- The stack depth of the avx2_x8 link's hand-off log. -/
def D8 : Nat := 1296

/-- **The avx2_x8 link obligation** (windows stream `p8`). -/
def KSpecC8 (s8 : Nat → Nat) (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) : Prop :=
  WfMemW Hashtree.Kernels.X86Win.Avx2X8.rodata [] env σ m0 → EnvMem env σ m0 → σ 2 = c →
  σ 9 % 16 = 8 →
  (∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
  ∀ s, s = mapState env σ entryWin →
    let f := run p8 4 m0 orcC (s8 c) s
    f.err = none ∧
      ((c = 0 ∧ f.tail = none ∧ PostLink σ c inp 0 f) ∨
       (c ≠ 0 ∧ f.tail = some "hashtree_sha256_avx_x4" ∧
         PreLink env σ c (c - c % 8) (c % 8) inp D8 L4 (resume f)))

/-- The step count of `Avx2X8WAll.x8_runW_abi` for `j` further turns:
`16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))`. -/
def x8RunSteps (j : Nat) : Nat := 16 + (6062 + (j * 6062 + (6035 + 31)))

/-- The step count of `Avx2X8WAll.x8_runW_last_abi` (`8 ≤ c < 16`): `16 + (BODYLEN + 31)`. -/
def x8LastSteps : Nat := 16 + (6035 + 31)

/-- The linux avx2_x8 frame below the return marker: `push rbp`, `and rsp,-32`, `sub rsp,928`
(generous bound). -/
def D8L : Nat := 984

/-- **`TurnOut8` (to be proved by R2c):** under the hypotheses of `Avx2X8WAll.x8_runW_abi` and the
input bytes, the final write log of the linux avx2_x8 loop at `c = 8 (j + 1) + s`, `8 ≤ s < 16`,
over the caller log `M`, holds only cells of `M`, output cells of the finished `8 (j + 2)` blocks,
or the kernel's own frame below `σ 9`, and the finished blocks hold their SHA-256 bytes. -/
def TurnOut8 : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 8 ≤ s → s < 16 →
    σ 2 = 8 * ((j : Int) + 1) + (s : Int) → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC (x8RunSteps j)
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC (x8RunSteps j)
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem

/-- **`TurnOut8Last` (to be proved by R2c):** the same for `x8_runW_last_abi`, `8 ≤ c < 16`
(one pass, 8 blocks). -/
def TurnOut8Last : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 8 ≤ σ 2 → σ 2 < 16 → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC x8LastSteps
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC x8LastSteps
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem

end Hashtree.Proofs.WinAvx2X8Bridge
