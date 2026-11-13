import Hashtree.Proofs.Avx512X16WBodyV
import Hashtree.Proofs.Avx512X16WEntry
import Hashtree.Asm.X86Loop
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
  Hashtree.Kernels.X86.Avx512X16

namespace Hashtree.Proofs.Avx512X16WTurn
open Hashtree.Gen.Avx512X16P
open Hashtree.Proofs.Avx512X16WBody
open Hashtree.Proofs.Avx512X16WEntry
open Hashtree.Proofs.Avx512X16WBodyV

/-!
# One turn of the `avx512_x16` loop

A turn is the 3218-instruction body followed by the 22-instruction tail
(`vpshufb`/`vmovdqu32`/`add`/`sub`/`jmp`/`cmp`/`jb`), i.e. `(8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22)` instructions.

* `turn1_run` — the first turn, from the entry path's body head `wcutH K1` (whose four scratch
  vector registers still hold the caller's data);
* `turn_run` — any later turn, from the loop head `KH` (`wfixS` fixes the four scratch
  registers to the values the body leaves them);
* `exit1_run` / `exit_run` — the same runs with `jb` taken, reaching the `avx2_x8` tail cut
  `KTE` instead of the head;
* `turn_step` — a turn's end cut is the loop head under the substitution `tau`, behind the
  turn's write log;
* `iter_step` — one framed turn at an arbitrary count `c >= 32` (the `jb` is not taken);
* `exit_step` — the framed final turn, `16 <= c < 32`.
-/

/-! ## The body heads are numbered-variable states -/

/-- The entry path's body head only carries numbered variables, so its meaning does not depend
on the memory part of the environment: `mapState G1 σ` is `mapState e σ`. -/
theorem wcutH_K1_nOnly : (wcutH K1).nOnly = true := by decide +kernel

/-- The environment after one continuing turn from head environment `e`. -/
def turnE (e : Key → W32) : Key → W32 :=
  envAbs (Hashtree.Proofs.Avx512X16WBodyV.G216 e) (run prog 4 mW orcNone 22 (wcutH K216))

/-- The environment after the exit turn. -/
def exitE (e : Key → W32) : Key → W32 :=
  envAbs (Hashtree.Proofs.Avx512X16WBodyV.G216 e) (run prog 4 mW orcExit 22 (wcutH K216))

/-- The environment after the first turn (whose body chain starts at `wcutH K1`). -/
def turnE1 (e : Key → W32) : Key → W32 :=
  envAbs (Hashtree.Proofs.Avx512X16WBody.G216 e) (run prog 4 mW orcNone 22 (wcutH K216))

/-- The environment after the exit turn of the first pass. -/
def exitE1 (e : Key → W32) : Key → W32 :=
  envAbs (Hashtree.Proofs.Avx512X16WBody.G216 e) (run prog 4 mW orcExit 22 (wcutH K216))

/-- The two entry conditions of the pilot, and the `jb` not taken: `32 <= c`. -/
theorem asmTurn (σ : Nat → Int) (hge : 32 ≤ σ 2) :
    ∀ p ∈ (((.lt (⟨-16, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), false) :: A0),
      (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · exact asmge σ (by omega) p hp

/-- The two entry conditions and the `jb` taken: `16 <= c < 32`. -/
theorem asmExit (σ : Nat → Int) (hge : 16 ≤ σ 2) (hlt : σ 2 < 32) :
    ∀ p ∈ (((.lt (⟨-16, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), true) :: A0),
      (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · exact asmge σ (by omega) p hp

/-- **The first turn.**  From the entry path's body head, at any count `c >= 32` (so the `jb`
is not taken), the body and the tail reach the turn cut `KT`. -/
theorem turn1_run (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel e σ mW mem0c) (hge : 32 ≤ σ 2) :
    run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (mapState e σ (wcutH K1)) = mapState (turnE1 e) σ KT := by
  have hm : Mem0Rel (Hashtree.Proofs.Avx512X16WBody.G216 e) σ mW mem0c := body_memW e σ mem0c h0
  have ht := (slice_sound (Hashtree.Proofs.Avx512X16WBody.G216 e) σ mW mem0c hm prog 4 orcNone orcC
    22 (wcutH K216) KT [] sliceW_turn K216_err
    (assumeOk_of σ KT _ KT_assume (asmTurn σ hge))).1
  have hgn : mapState (Hashtree.Proofs.Avx512X16WBody.G1 e) σ (wcutH K1) =
      mapState e σ (wcutH K1) :=
    mapState_nOnly _ _ σ (fun i => rfl) _ wcutH_K1_nOnly
  rw [run_add, ← hgn, body_runW e σ mem0c orcC h0 (by omega)]
  exact ht

/-- **Any later turn**, from the loop head, `c >= 32`. -/
theorem turn_run (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel e σ mW mem0c) (hge : 32 ≤ σ 2) :
    run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (mapState e σ KH) = mapState (turnE e) σ KT := by
  have hm : Mem0Rel (Hashtree.Proofs.Avx512X16WBodyV.G216 e) σ mW mem0c := bodyV_mem e σ mem0c h0
  have ht := (slice_sound (Hashtree.Proofs.Avx512X16WBodyV.G216 e) σ mW mem0c hm prog 4 orcNone orcC
    22 (wcutH K216) KT [] sliceW_turn K216_err
    (assumeOk_of σ KT _ KT_assume (asmTurn σ hge))).1
  have hgn : mapState (Hashtree.Proofs.Avx512X16WBodyV.G1 e) σ KH = mapState e σ KH :=
    mapState_nOnly _ _ σ (fun i => rfl) _ KH_nOnly
  rw [run_add, ← hgn, bodyV_run e σ mem0c orcC h0 (by omega)]
  exact ht

/-- **The exit after the first pass**, `16 <= c < 32`: the residual blocks tail into
`avx2_x8`. -/
theorem exit1_run (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel e σ mW mem0c) (hge : 16 ≤ σ 2) (hlt : σ 2 < 32) :
    run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (mapState e σ (wcutH K1)) = mapState (exitE1 e) σ KTE := by
  have hm : Mem0Rel (Hashtree.Proofs.Avx512X16WBody.G216 e) σ mW mem0c := body_memW e σ mem0c h0
  have ht := (slice_sound (Hashtree.Proofs.Avx512X16WBody.G216 e) σ mW mem0c hm prog 4 orcExit orcC
    22 (wcutH K216) KTE [] sliceW_exit K216_err
    (assumeOk_of σ KTE _ KTE_assume (asmExit σ hge hlt))).1
  have hgn : mapState (Hashtree.Proofs.Avx512X16WBody.G1 e) σ (wcutH K1) =
      mapState e σ (wcutH K1) :=
    mapState_nOnly _ _ σ (fun i => rfl) _ wcutH_K1_nOnly
  rw [run_add, ← hgn, body_runW e σ mem0c orcC h0 (by omega)]
  exact ht

/-- **The exit after the loop**, from the loop head, `16 <= c < 32`. -/
theorem exit_run (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel e σ mW mem0c) (hge : 16 ≤ σ 2) (hlt : σ 2 < 32) :
    run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (mapState e σ KH) = mapState (exitE e) σ KTE := by
  have hm : Mem0Rel (Hashtree.Proofs.Avx512X16WBodyV.G216 e) σ mW mem0c := bodyV_mem e σ mem0c h0
  have ht := (slice_sound (Hashtree.Proofs.Avx512X16WBodyV.G216 e) σ mW mem0c hm prog 4 orcExit orcC
    22 (wcutH K216) KTE [] sliceW_exit K216_err
    (assumeOk_of σ KTE _ KTE_assume (asmExit σ hge hlt))).1
  have hgn : mapState (Hashtree.Proofs.Avx512X16WBodyV.G1 e) σ KH = mapState e σ KH :=
    mapState_nOnly _ _ σ (fun i => rfl) _ KH_nOnly
  rw [run_add, ← hgn, bodyV_run e σ mem0c orcC h0 (by omega)]
  exact ht

/-! ## The turn's write log -/

/-- Structural check on the addresses of the turn's log: output cells only. -/
def logOkB (p : Addr Lin × Cell E Lin) : Bool :=
  if p.1.region = rOut then true
  else if p.1.region = rStack then
    decide (p.1.off.c = ([] : List Int) ∧ p.1.off.k < 24)
  else false

theorem KT_logB : KT.mem.all logOkB = true := by decide +kernel

/-- Every write of one turn is an output byte. -/
theorem KT_log (p : Addr Lin × Cell E Lin) (hp : p ∈ KT.mem) :
    p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off.c = [] ∧ p.1.off.k < 24) := by
  have h : logOkB p = true := List.all_eq_true.mp KT_logB p hp
  by_cases h1 : p.1.region = rOut
  · exact Or.inl h1
  by_cases h2 : p.1.region = rStack
  · right
    have hd : decide (p.1.off.c = ([] : List Int) ∧ p.1.off.k < 24) = true := by
      rw [logOkB, if_neg h1, if_pos h2] at h
      exact h
    exact ⟨h2, of_decide_eq_true hd⟩
  · exfalso
    rw [logOkB, if_neg h1, if_neg h2] at h
    cases h

/-- The turn's log, after substituting the concrete symbols, still satisfies `OutLog`. -/
theorem outLog_map_KT (σ : Nat → Int) (e : Key → W32) :
    OutLog (KT.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases KT_log q hq with h | ⟨h, hc, hk⟩
  · left
    simpa [mapAddr] using h
  · right
    have hreg : (mapAddr σ q.1).region = rStack := by simpa [mapAddr] using h
    refine ⟨hreg, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k := by simp [Lin.eval, hc, dotC]
    show q.1.off.eval σ < 24
    rw [hoff]
    exact hk

/-- **One turn ends in a substitution instance of the loop head**, behind its write log. -/
theorem turn_step (env0 : Key → W32) (σ : Nat → Int) :
    mapState (envAbs env0 (run prog 4 mW orcNone 22 (wcutH K216))) σ KT =
      fr (KT.mem.map (fun p =>
            (mapAddr σ p.1, mapCell (envAbs env0 (run prog 4 mW orcNone 22 (wcutH K216))) σ p.2)))
        (mapState (envAbs env0 (run prog 4 mW orcNone 22 (wcutH K216))) (sigmaOf tau σ) KH) := by
  rw [KT_inst env0 σ]
  exact mapState_reached (envAbs env0 (run prog 4 mW orcNone 22 (wcutH K216))) σ _ KH tau KT_shape

/-- `OutLog` is preserved by appending. -/
theorem outLog_app'' {L M : CLog} (hL : OutLog L) (hM : OutLog M) : OutLog (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- Appending a log after another. -/
theorem fr_fr' (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

/-- With nothing on the push stack the memory relation does not depend on the environment:
the only environment-dependent clause is vacuous. -/
theorem wfMemW_push_nil (rodata : List Nat) (e e' : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int)
    (h : WfMemW rodata [] e σ m) : WfMemW rodata [] e' σ m := by
  obtain ⟨hro, hret, hin, _⟩ := h
  refine ⟨hro, hret, hin, ?_⟩
  intro k c hl h8 hok
  rw [show plookup k ([] : List (Int × Cell E Lin)) = none from rfl] at hl
  cases hl

/-- The `WfMemW` relation survives a frame of output writes (the entry stack pointer is above
the protected zone; the kernel never reads stack it did not write).  The kernel pushes nothing,
so the push clause is vacuous. -/
theorem wfMemW_view (rodata : List Nat) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (M : CLog) (hM : OutLog M) (hsp : 24 ≤ σ 9)
    (hw : WfMemW rodata [] env σ m) : WfMemW rodata [] env σ (view M m) := by
  obtain ⟨hro, hret, hin, _⟩ := hw
  have v4 : ∀ o, view M m ⟨4, o⟩ = m ⟨4, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show (4 : Region) ≠ rOut by decide,
      fun h => absurd (show (4 : Region) = rStack from h) (by decide)⟩)
  have vI : ∀ o, view M m ⟨rIn, o⟩ = m ⟨rIn, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
      fun h => absurd (show rIn = rStack from h) (by decide)⟩)
  have vS : ∀ k : Int, 0 ≤ k → view M m ⟨rStack, σ 9 + k⟩ = m ⟨rStack, σ 9 + k⟩ := by
    intro k hk
    apply view_other
    intro p hp heq
    rcases hM p hp with h | ⟨h1, h2⟩
    · rw [heq] at h
      have hr : rStack = rOut := h
      exact absurd hr (by decide)
    · rw [heq] at h2
      have hlt : σ 9 + k < 24 := h2
      omega
  refine ⟨fun o => by rw [v4]; exact hro o,
    fun k h1 h2 => by rw [vS k h1]; exact hret k h1 h2,
    fun o => by rw [vI]; exact hin o, ?_⟩
  intro k c hl h8 hok
  rw [show plookup k ([] : List (Int × Cell E Lin)) = none from rfl] at hl
  cases hl

/-- **One framed turn** at any count `c >= 32`: the head under `sigmaOf tau σ`, behind the
turn's writes. -/
theorem iter_step (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (e : Key → W32) (σ : Nat → Int) (hw : WfMemW rodata [] e σ mem0c) (M : CLog)
    (hM : OutLog M) (hge : 32 ≤ σ 2) (hsp : 24 ≤ σ 9) :
    ∃ e' M',
      run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (fr M (mapState e σ KH)) =
        fr M' (mapState e' (sigmaOf tau σ) KH) ∧ OutLog M' := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ mW (view M mem0c) := by
    rw [show mW = mem0sW 4 rodata [] from rfl]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfMemW_push_nil rodata e E σ (view M mem0c) (wfMemW_view rodata e σ mem0c M hM hsp hw))
      (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (fr M (mapState e σ KH)) =
      fr M (mapState (turnE E) σ KT) := by
    rw [run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KH KH_nOnly]
    exact congrArg (fr M) (turn_run E σ (view M mem0c) orcC hrel hge)
  refine ⟨turnE E, KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE E) σ p.2)) ++ M, ?_, ?_⟩
  · have hstep : mapState (turnE E) σ KT =
        fr (KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE E) σ p.2)))
          (mapState (turnE E) (sigmaOf tau σ) KH) :=
      turn_step (Hashtree.Proofs.Avx512X16WBodyV.G216 E) σ
    rw [hrun, hstep, fr_fr']
  · exact outLog_app'' (outLog_map_KT σ (turnE E)) hM

/-- **The framed final turn**: `16 <= c < 32`, `jb` taken, reaching the `avx2_x8` tail. -/
theorem exit_step (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (e : Key → W32) (σ : Nat → Int) (hw : WfMemW rodata [] e σ mem0c) (M : CLog)
    (hM : OutLog M) (hge : 16 ≤ σ 2) (hlt : σ 2 < 32) (hsp : 24 ≤ σ 9) :
    ∃ e' M',
      run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (fr M (mapState e σ KH)) =
        fr M' (mapState e' σ KTE) ∧ OutLog M' := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ mW (view M mem0c) := by
    rw [show mW = mem0sW 4 rodata [] from rfl]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfMemW_push_nil rodata e E σ (view M mem0c) (wfMemW_view rodata e σ mem0c M hM hsp hw))
      (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) (fr M (mapState e σ KH)) =
      fr M (mapState (exitE E) σ KTE) := by
    rw [run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KH KH_nOnly]
    exact congrArg (fr M) (exit_run E σ (view M mem0c) orcC hrel hge hlt)
  exact ⟨exitE E, M, hrun, hM⟩

end Hashtree.Proofs.Avx512X16WTurn
