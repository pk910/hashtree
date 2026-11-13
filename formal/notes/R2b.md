# R2b — `avx2_x8` and `avx512_x16` at the wrapper's call state (`entryW`)

Branch `research/formal-r2b-x8x16`.  R2 owns the x4 chain and the wrapper
(`AvxX4*`, `Avx2X8Body`, `Avx512X16Body`, `WrapperAmd64`, `WrapperPre`, `tools/avx_counts.py`,
`formal/notes/R2.md`); this workstream owns the two wider kernels at the state the Go wrapper
calls them in, and the `Avx2X8W*` / `Avx512X16W*` files, `tools/avx_lane_counts.py`,
this note, and the marked `R2b` block of `Axioms.lean`.

## 1. What is proved

Everything is proved at `entryW` (`Hashtree/Asm/X86SymW`), i.e. with the argument registers
pointing into the wrapper's frame and the stack cells addressed relative to symbol `9`
(`sAt k = ⟨k, stkC⟩`), not at the constant-offset system-V state `entryS 24`.  The rodata
table sits in region `4` throughout (the fresh-region lift is in §5).

### `avx512_x16` — every count

| theorem | statement |
| --- | --- |
| `Avx512X16WBody.body_runW` | the 215-slice body (3218 instructions) from `wcutH K1` to `wcutH K216`, any count `σ 2 ≥ 16`, at `entryW`'s scratch registers |
| `Avx512X16WBody.body_memW` | the env/mem side of the same run (`Mem0Rel (G216 e) σ mW mem0c`) |
| `Avx512X16WEntry.sliceW_entry` | the 8-instruction entry slice `nop; cmp; jne(taken); lea×3; cmp; jb(not taken)` |
| `Avx512X16WEntry.sliceW_zero` / `sliceW_small` | the count-0 path (4 instructions to `ret`) and the `0 < c < 16` path (8 instructions to the `avx2_x8` tail) |
| `Avx512X16WEntry.sliceW_turn` / `sliceW_exit` | the 22-instruction loop tail, `jb` not taken (loop continues) and taken (tail call) |
| `Avx512X16WEntry.mapState_wcutE` | the entry cut is the loop head when `σ 10 = σ 1` (`rax` holds the output base on the untouched symbol `10`) |
| `Avx512X16WEntry.KT_shape` | one turn's end cut, stripped of log and assumptions, is `KH.substL tau` |
| `Avx512X16WTurn.turn1_run` / `turn_run` | one turn from the entry body head and from the loop head, `σ 2 ≥ 32` |
| `Avx512X16WTurn.exit1_run` / `exit_run` | the final turn, `16 ≤ σ 2 < 32`, `jb` taken |
| `Avx512X16WTurn.turn_step` | a turn ends in `fr (turn log) (mapState e (sigmaOf tau σ) KH)` |
| `Avx512X16WTurn.iter_step` | one framed turn at `σ 2 ≥ 32` (`WfMemW` + `OutLog` frame) |
| `Avx512X16WTurn.exit_step` | the framed final turn, `16 ≤ σ 2 < 32` |
| `Avx512X16WLoop.loop` | `j` framed turns: `σ 2 = 16j + s`, `16 ≤ s < 32` ⇒ `run (j*turnSteps) (fr M (mapState e σ KH)) = fr M' (mapState e' (sIt j σ) KH)` |
| `Avx512X16WLoop.x16_zero_run` | count 0: 4 instructions, `halted`, `tail = none`, `err = none` |
| `Avx512X16WLoop.x16_small_run` | `0 < c < 16`: 8 instructions, `tail = some "hashtree_sha256_avx2_x8"` |
| `Avx512X16WLoop.x16_loop` | `c ≥ 16`: `steps c` instructions, `tail = some "hashtree_sha256_avx2_x8"`, residual `c % 16` |
| `Avx512X16WLoop.x16_all` | the post-condition `x16post c` at `run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW)` for every `c` |
| `Avx512X16WLoop.x16_chain_head` | the `X86Chain` per-link obligation for the link `x16link` |

The step function (`Avx512X16WLoop.steps`), where `turnSteps` is the exact literal
`(SUM + 22)` (`SUM` = the 215-slice body count, 3210; the tail adds 22, i.e. 3232
instructions per turn):

```lean
def turnSteps : Nat := (<215 slice sums> + 22)          -- 3232
def steps (c : Nat) : Nat :=
  if c = 0 then 4 else if c < 16 then 8 else 8 + turnSteps * (c / 16)
```

Hypotheses of `x16_all` (all of them named in the statement):

* `h0 : Mem0Rel env0 σ mW mem0c` — the concrete memory is the symbolic one under `(env0, σ)`;
* `hw : WfMemW rodata [] env0 σ mem0c` — the concrete memory has the kernel's rodata in region
  4, the wrapper's return marker at `[σ 9, σ 9+8)`, and input bytes (`mem0sW 4 rodata []`;
  the kernel pushes and pops its own frame, so no stack bytes are assumed);
* `hsp : 24 ≤ σ 9` — the return marker is above the 24 stack bytes `OutLog` protects; this is
  what makes the turn frames harmless;
* `h10 : σ 10 = σ 1` — `rax` carries the output base on the loop-invariant symbol `10`, which
  is the same address as the entry's `sym 1`;
* `hc : σ 2 = c` — the count.

Post-condition `x16post c f`:

* `f.err = none`;
* `c = 0` ⇒ `f.tail = none` and `f = mapState e σ KZ` (plain return, no writes);
* `0 < c < 16` ⇒ `f.tail = some "hashtree_sha256_avx2_x8"` and `f = mapState e σ KSm`
  (no writes: the residual blocks go to x8 with the entry registers);
* `16 ≤ c` ⇒ `f.tail = some "hashtree_sha256_avx2_x8"` and `x8Pre (resume f)`.

## 2. The interface R2 must consume

`x16link : X86Chain.Link` — `{ name := "hashtree_sha256_avx512_x16", prog := prog, ro := 4,
steps := steps }` — and `x16spec env0 σ c : X86Chain.Spec` with
`pre := fun s => s = mapState env0 σ entryW`, `post := x16post c`.

**The tail's pre-condition is a named predicate, not R2's `entryW`-shaped `x1spec.pre`.**
At the tail call the x16 exit cut `KTE` differs from a fresh `entryW` call in three ways: the
count register already holds the residual `c % 16` (`σ 2 - 16` in `KTE`), the input/output
pointers (symbols `0`, `1`) have been advanced by the turns, and the state carries the loop's
write log.  The predicate

```lean
def x8Pre (f : CState) : Prop :=
  ∃ e σ M, OutLog M ∧ 0 ≤ σ 2 - 16 ∧ σ 2 - 16 < 16 ∧
    f = fr M (resume (mapState e σ KTE))
```

is what `x16post` produces (on `resume f`, the state the chain hands to the next link).
The x8 link needs a pre-condition implied by `x8Pre`; `x16_chain_head` takes exactly such an
implication, plus the small-path form (the `0 < c < 16` branch tails with the untouched entry
registers, `f = mapState e σ KSm`, which is *not* an `x8Pre` instance):

```lean
theorem x16_chain_head (...) (sp' : Spec)
    (hname : sp'.link.name = "hashtree_sha256_avx2_x8")
    (hpreS : ∀ (e : Key → W32) (σ' : Nat → Int), sp'.pre (resume (mapState e σ' KSm)))
    (hpre : ∀ f, x8Pre f → sp'.pre f) :
    ∀ s, (x16spec env0 σ c).pre s →
      let f := step mem0c orcC c (x16spec env0 σ c).link s
      f.err = none ∧
        ((f.tail = none ∧ (x16spec env0 σ c).post f) ∨
         (f.tail = some sp'.link.name ∧ sp'.pre (resume f)))
```

so composing x16 with the x8 link is
`x16_chain_head … x8spec (by rfl) (by intro e σ; …) (by intro f hf; …)`, where the last two
steps derive the x8 link's own pre-condition from `x8Pre` (loop path) and from `KSm` (small
path).  If R2 publishes a
different x8 entry predicate, `x8Pre` is the only definition to bridge; nothing inside the
x16 proof depends on the x8 side.  The σ-adjustment at symbol 2 (`σ 2 - 16`) and the fact that
symbols `0`/`1` have moved are both visible in `x8Pre`: the next link must not assume that
`σ` is the caller's original valuation.

`x16post`'s first two branches (count 0 and the small path) are `entryW`-shaped states with no
log, so they compose with a next link whose pre is the plain `entryW` form (modulo
`mapState`/`envAbs`).

## 3. `avx2_x8` at `entryW` — the entry segment and the blocker

`Avx2X8WEntry`:

* `x8_zero_run` — **count 0 is fully proved**: `nop; cmp rdx,0; jne` not taken, `ret`; four
  instructions, `halted = true`, `tail = none`, `err = none`, no writes (`x8Z.mem = []`).
* `x8_prologue_run` — for `0 < c`, the `jne` is taken and the five instructions
  `nop; cmp rdx,0; jne; push rbp; mov rbp,rsp` run, reaching `pc = 6` with `err = none`.
* `x8_align_blocked` / `x8_stuck` — **the seventh instruction fails**:
  `and rsp,-32` at the wrapper's call state gives
  `err = some "and on symbolic pointer"`.  Cause: after `push`, `rsp = ⟨-8, stkC⟩`, whose
  `Ctl` offset has coefficient `1` on symbol `9`; `Ctl.asInt` is `none` on it
  (`asInt_sAt'`), so the `.alu .and` case of `exec` (`Hashtree/Asm/X86.lean`, the
  `| _, _ => throw "and on symbolic pointer"` arm) throws.

So the x8 small path (`0 < c < 8`, which tails into `avx_x4`) and the x8 loop path cannot be
proved from `entryW` as it stands: the alignment of the caller's stack is genuinely missing
from the call-state model.  The fix is the shape of `WrapperPre.align_hom`: add the alignment
premise `σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32` (the post-`push` stack pointer aligned mod 32)
and model the aligned stack pointer as a *fresh* aligned address symbol, not as `sAt k`.  That
changes `mem0sW`'s `stackRel` table (which recognizes stack cells only as `sAt k` /
`trimC l.c = stkC`), so it is a change to the W-mode memory model rather than a local proof,
and it belongs with the wrapper's own alignment argument.  This is reported rather than
silently weakened: **the x8 counts `1 … 7` and the x8 loop are not proved at `entryW`, with
the exact failing goal `(exec 4 m8 orcNZ (prog[6]!) x8P).err = some "and on symbolic pointer"`
proved above.**

Count 0 needs no alignment (the path jumps over the frame setup), which is why it is complete.

## 4. Region

All theorems are stated with the rodata table in region `4`
(`Avx512X16WBody.mW = mem0sW 4 rodata []`, `Avx2X8WEntry.m8`).  The fresh-region form is a
corollary through `Hashtree/Asm/X86Ren.lean`:

```lean
X86Ren.run_swap_chain (r) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet) prog m orc n s :
  run prog r m orc n ((swap 4 r).state s) = (swap 4 r).state (run prog 4 ((swap 4 r).mem m) orc n s)
```

Corollaries (all in `Avx512X16WLoop`, plus `x8_zero_run_region` in `Avx2X8WEntry`):

* `body_runW_region` — the 215-slice body at region `r` (the region-4 run, renamed);
* `body_memW_region` — its env/mem side (`Mem0Rel` is region-agnostic, so this is the
  region-4 statement on the renamed memory);
* `x16_run_region` — `run_swap_chain` for the kernel's whole step function `steps c`;
* `x16_all_region` — the post-condition `x16postR r c` (an existential rename of
  `x16post`, `def x16postR r c f := ∃ g, f = (swap 4 r).state g ∧ x16post c g`).

A link at region `r` uses `hrNum : r ≠ rNum`, `hrRet : r ≠ rRet` and states its
`Mem0Rel`/`WfMemW` hypotheses over `(swap 4 r).mem m0c`; that is the whole region hypothesis.
Alternatively, `Hashtree/Asm/X86Region.lean` gives the region-parametric memory predicate
`WfMemAtW ro` and its bridge `mem0RelW_of_wfAt` (`WfMemW = WfMemAtW 4`), so a link whose rodata
lives in region `ro` can state `Mem0Rel env σ (mem0sW ro rodata []) m0c` directly and use
`mem0RelW_of_wfAt` in place of `mem0RelW_of_wf`.  The `swap`-transport above and the
`WfMemAtW` route are interchangeable; the x16 proof itself is region-4 throughout.

## 5. Timings and gate

(filled in after the target builds; see the log `results/r2b-x8x16-log.md`)
