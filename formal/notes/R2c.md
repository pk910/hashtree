# R2c — output correctness of the `avx512_x16` W-mode loop (`TurnOut`)

Branch `research/formal-r2c-x16out` (from R2b `ebe04b6`).  Own files: `Hashtree/Proofs/Avx512X16WOut*.lean`,
this note, the marked `R2c` block of `Axioms.lean`.

## Statement

`Hashtree.Proofs.Avx512X16WOut.TurnOut` is the text fixed by R5 (`WinAvx512Bridge.TurnOut` at `ec067bb`, no `24 ≤ σ 9` binder,
copied verbatim; `OutOk` is this module's constant with the text of `ShaniW.OutOk` /
`WinWrapper.OutOk`, so the two statements are definitionally equal up to unfolding `OutOk`):
under the hypotheses of `Avx512X16WLoop.x16_loop` (`Mem0Rel env0 σ mW mem0c`, `WfMemW rodata []
env0 σ mem0c`, `σ 10 = σ 1`, `σ 2 = c`, `16 ≤ c`) and the input bytes
`∀ o, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0`, the write log of
`run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW)` consists of output cells of the
finished blocks only, `[σ 1, σ 1 + 32 (c - c % 16))`, and `OutOk inp (σ 1) (c - c % 16)` holds
on it (byte `32 n + 4 i + b` is byte `4 i + b` of SHA-256 of input block `n`).

`theorem turnOut : TurnOut` — proved; `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` and the generated `*_native.bv_decide.ax_*` of `Hashtree.Asm.byte_bswap` and of the
pilot's `Gen.Avx512X16P.shape*` lane lemmas (through `step_k`); no `sorryAx`, no
`native_decide` / `ofReduceBool`.

## Route: lift the pilot's invariant chain to the W cuts

R2b's W-mode body slices are already checked with the pilot's tree lists
(`Avx512X16WBody.sliceW_k` / `WBodyV.sliceV_k` use `Gen.Avx512X16P.T_k`); only the two
22-instruction tails (`sliceW_turn`/`sliceW_exit`) use `[]`.  So no slice is regenerated and no
renaming simulation is needed:

* `Avx512X16WOutBase` — `OutOk`; `invC_congr`, `agree_of_trees`, **`invC_lift`** (two slices
  checked with the same trees `T` give the same labelled values, so `InvC … L` after the pilot
  slice is `InvC … L` after the W slice); write-log lemmas (`lookup_append_notin/found/none`,
  `view_rIn`, `outOk_append_left/right`, `outOk_glue`, `outOk_step`, `blk_shift`); the input
  bytes as `HMem` for the entry environment (`hmem_entry`, via `Mem0Rel`) and for the turn
  environments (`hmem_view`, via `ecomb` / `EnvMem`, transparent on `rIn` because the loop
  writes only `rOut`).
* `Avx512X16WOutLab` (generated) — `lab_k : T_k.map fst = L_{k+1}.map fst`, k = 1..216.
* `Avx512X16WOutInv` (generated) — `stepW_k` / `stepV_k` := `invC_lift … slice_k sliceW_k/sliceV_k
  lab_k (step_k …)` and the chains `invW_body` / `invV_body : HMem 1024 inp env1 → InvC inp (G216 env1) L216`
  for the first pass (`WBody.G216`) and the loop-head replay (`WBodyV.G216`).
* `Avx512X16WOutTail` (generated) — the two tails re-checked **with** the pilot trees
  (`sliceT_turn : sliceCheck prog 4 mW orcNone 22 (wcutH K216) KT T216 = true`, `sliceT_exit`
  with `KTE`; `abstract` numbers variables by position, so `T216` is valid on the W cut) and the
  lifted last step `stepT_turn`/`stepT_exit : InvC … L216 → InvC … L217`; the shape of a turn's
  log (`outShape`: exactly output cells at `sym 1 + o`, `o < 512` — the pilot's body writes
  nothing, the whole 512-byte digest store is in the tail); `outOk_KT` / `outOk_KTE`: the 16
  digests from `InvC … L217`, the pilot's `out_final` case table (512 cases) with the W cut and a
  generic environment, the cell facts checked once per cut (`KT_cells`/`KTE_cells`, one
  `decide +kernel` over the 512 `(o, id, b)` triples; 512 separate `decide`s re-evaluated the cut
  each time and did not finish in 50 min).
* `Avx512X16WOut` — symbols (`tau_in/out`, `sIt_in/out`: the input pointer advances 1024 and the
  output pointer 512 per turn), `iter_out` / `exit_out` (one continuing / final turn from `KH` with
  its log exposed and its 16 digests), `loop_out` (j turns, blocks `0 .. 16 j - 1` at
  `[σ 1, σ 1 + 512 j)`), `turnOut`.

## Cost

Base/Lab/Inv: seconds (Lab 23 s, Inv 6 s).  Tail: 199 s (two tail tree-checks + two table checks
+ 1024 cases).  Out: 22 s.  The R2b chain it sits on (`WBody` 4224 s, `WBodyV` 3768 s under load)
was rebuilt from source in this worktree (real copies, no hardlinks).

Gotchas: core Lean only — no `ring`/`set`; `omega` does not look inside structure projections of
literals (`show` the goal first) nor through `σ (0 + 1)` (normalise the index); conjunctions with
a non-arithmetic conjunct must be split before `omega`.

## avx_x4 W-mode loop (`TurnOut4`)

`Hashtree.Proofs.AvxX4LoopWOut.TurnOut4` / `x4RunSteps` are R5's text (`WinAvxX4Bridge`), copied
verbatim: under `WfMemW rodata [] env0 σ mem0c`, `OutLogW σ M`, `σ 2 = 4 (j + 1) + s` with
`4 ≤ s < 8` and the input bytes at `σ 0`, every cell of the log of
`run prog 4 mem0c orcC (x4RunSteps j) (fr M (mapState env0 σ entryW))` is in `M`, an output cell in
`[σ 1, σ 1 + 128 (j + 2))` or a cell of the kernel's own stack frame `[σ 9 - 568, σ 9)`, and
`OutOk inp (σ 1) (4 (j + 2))` holds on it.

`theorem turnOut4 : TurnOut4` — proved; `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` and generated `*_native.bv_decide.ax_*` (134 of `Gen.AvxX4P`, the rest of
`Asm.byte_bswap` / `Asm.SpecQ`); no `sorryAx`, no `native_decide` / `ofReduceBool`.

Same route as x16: the W slices re-checked with the pilot's (`Gen.AvxX4P`) trees
(`AvxX4LoopWOutChk1..8`), labels (`…Lab`), the lifted invariant chains (`…Inv`, via the new
`invC_lift'`, which allows S and W slices of different lengths), the two tails with the turn's log
shape and the 128 digest cases (`…Tail`); `AvxX4LoopWOut` composes entry pass (72 + body + 23), `j`
framed turns (`loop_out4`) and the final pass (68 + body + 27) along `AvxX4LoopWAll.x4_runW`.
Generator: `tools/gen_r2c_x4.py <slice table> <pilot out_final text>` writes Lab/Chk/Inv/Tail.
Cost: Tail 60 s, Out 114 s (1 thread).  Gotcha: `funext o; congr 1; omega` on
`inp (256 (j+1) + o) = inp (64 (4 (j+1)) + o)` never finished (`congr`'s closing `rfl` unfolds
`Nat.mul` on a variable); `exact congrArg inp (by omega)` is instant.

## avx2_x8 W-mode loop (`TurnOut8`, `TurnOut8Last`)

`Hashtree.Proofs.Avx2X8WOut.TurnOut8` / `TurnOut8Last` (with `x8RunSteps`, `x8LastSteps`, `D8L = 984`)
are R5's text (`WinAvx2X8Bridge`), copied verbatim; `Avx2X8WOutBridge.turnOut8_R5` / `turnOut8Last_R5`
prove R5's own constants by unfolding `TurnOut8*` and `WinWrapper.OutOk`.  Under the hypotheses of
`Avx2X8WAll.x8_runW_abi` (`c = 8 (j + 1) + s`, `8 ≤ s < 16`) / `x8_runW_last_abi` (`8 ≤ c < 16`),
`σ 9 % 16 = 8` and the input bytes at `σ 0`, every cell of the final log is in `M`, an output cell in
`[σ 1, σ 1 + 256 (j + 2))` (resp. `+ 256`) or a stack cell in `[σ 9 - 984, σ 9)`, and
`OutOk inp (σ 1) (8 (j + 2))` (resp. `8`) holds on it.

`theorem turnOut8 : TurnOut8`, `theorem turnOut8Last : TurnOut8Last` — proved; `#print axioms`:
`propext`, `Classical.choice`, `Quot.sound` and 144 generated `*_native.bv_decide.ax_*` (pilot
`Gen.Avx2X8P.shape*`, `Asm.byte_bswap`, `Asm.loadLane_hom`, `Asm.SpecQ.qW_*`); no `sorryAx`, no
`native_decide` / `ofReduceBool`.

Route (generator `tools/gen_r2c_x8.py <pilot Final.lean> <pilot D210.lean>` writes Lab/Tab/Cut*/Inv*):

* R2's body slices (first pass `Avx2X8WBodyR{r}.sliceW_k`, later pass `Avx2X8WBodyR{r}S.sliceV2s`,
  `sliceV3s`, `sliceS_k`) are already checked with the pilot's trees and lengths, and the pilot's
  labels `L0 = L1 = L2 = []`, so the entry/head replays need nothing: `Avx2X8WOutInvR{0,16}` lift
  `step2 .. step209` by `invC_lift` (chains `invW{r}_body`, `invS{r}_body` from `True`).
* Only the four tails per residue are re-checked with trees (`Avx2X8WOutCut{T,X,TS,XS}{r}`, one
  `decide +kernel` each for the slice, the 256 output cells, and the log shape).  **Gotcha:** the
  turn tails (`KT r`, `KTs r`, 27 steps) reload the IV into the two vector registers that hold the
  digests of blocks 0/1 in the pilot's exit cut, so `sliceCheck … (KT 0) T210` is false (16 trees,
  ids 100..107 / 116..123).  `Avx2X8WOutTab` drops them: `T210t`/`L211t` (`L211t` literal,
  `L211t_eq` to the filter by `decide +kernel`), `slice210t` from `slice210` (`sliceCheck_filter`),
  `invC_sub : InvC L211 → InvC L211t`; the output cells are memory labels and stay.
* `outOk_tab`: one generic proof (any cut whose `tab8` cells check, at `InvC … L211t`) of the 8
  digests from the pilot's `out_final` case table (256 cases); the per-cut cell facts are the
  single-table `decide +kernel`s in the Cut files.
* `Avx2X8WOut`: `OutR r B` bundles the four lifted tails and the cut facts; `first_out` /
  `iter_out` / `first_exit_out` / `final_out` mirror `first_turnW` / `iter_stepS` / `first_exitW`
  / `final_runW` with the pass's log exposed, `loop_out` (j later passes), `turnOut8_r` /
  `turnOut8Last_r` compose along `x8_runW` / `x8_runW_last`; the residue is selected by
  `residue_cases`.

Cost (VM, 1-4 threads, shared box): Lab 34 s, Tab 53 s, each Cut file 264-355 s, Inv 7 s each,
Out 3 s, Bridge 3 s.  R2's prerequisites rebuilt from source in this worktree (`Avx2X8WShift`
3183 s, body parts 1900-4500 s each).

Gotcha (elaboration): `exact outShape8_sound (KT r) …` against a goal stated with
`(KT r).mem.map …` instead of `(mapState e σ (KT r)).mem` never finished (the unifier unfolds the
computed cut `KT r`); stating `mapState_mem` once for a variable cut and `rw [mapState_mem] at h`
is instant.  Also `x8RunSteps_eq` is by `unfold …; omega`, not `rfl`.
