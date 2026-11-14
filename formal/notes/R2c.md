# R2c — output correctness of the `avx512_x16` W-mode loop (`TurnOut`)

Branch `research/formal-r2c-x16out` (from R2b `ebe04b6`).  Own files: `Hashtree/Proofs/Avx512X16WOut*.lean`,
this note, the marked `R2c` block of `Axioms.lean`.

## Statement

`Hashtree.Proofs.Avx512X16WOut.TurnOut` is the text fixed by R5 (`WinAvx512Bridge.TurnOut`,
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
