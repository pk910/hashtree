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
| `Avx512X16WBodyV.bodyV_run` | the same 215 slices replayed from the loop-invariant head `KH`, to the pilot's end cut `wcutH K216` — this is the second and every later pass |
| `Avx512X16WBodyV.bodyV_mem` | its env/mem side (`Mem0Rel (G216 e) σ mW mem0c`) |
| `Avx512X16WEntry.sliceW_entry` | the 8-instruction entry slice `nop; cmp; jne(taken); lea×3; cmp; jb(not taken)` |
| `Avx512X16WEntry.sliceW_zero` / `sliceW_small` | the count-0 path (4 instructions to `ret`) and the `0 < c < 16` path (8 instructions to the `avx2_x8` tail) |
| `Avx512X16WEntry.sliceW_turn` / `sliceW_exit` | the 22-instruction loop tail, `jb` not taken (loop continues) and taken (tail call) |
| `Avx512X16WEntry.mapState_wcutE` | the entry cut is the loop head when `σ 10 = σ 1` (`rax` holds the output base on the untouched symbol `10`) |
| `Avx512X16WEntry.KT_gpr` / `KT_vr` | the loop shape register by register: the turn's end cut has the head's general registers (up to their location variables) and the head's vector registers |
| `Avx512X16WEntry.KT_shape` | one turn's end cut, with the head's registers installed and stripped of log and assumptions, is `KH.substL tau` |
| `Avx512X16WEntry.KT_inst` | the same at the concrete level, by `mapState_inst` over the tail's slice check |
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
`(SUM + 22)` (`SUM` = the 215-slice body count, 3218; the tail adds 22, i.e. 3240
instructions per turn):

```lean
def turnSteps : Nat := (<215 slice sums> + 22)          -- 3240
def steps (c : Nat) : Nat :=
  if c = 0 then 4 else if c < 16 then 8 else 8 + turnSteps * (c / 16)
```

The loop-carried head is `KH := wfixS [13, 14, 15, 24] (wcutH K1)` (`Avx512X16WEntry`).  The
body uses `zmm13, zmm14, zmm15, zmm24` as scratch: it writes `zmm24` first in slice 3 (a
256-bit load of block data, upper lanes zeroed), `zmm13`/`zmm14` in slice 7 (256-lane rodata
index constants) and `zmm15` in slice 13, and it reads none of them before writing it
(`#eval` scan of the program).  A second pass therefore starts with the values the first pass
leaves in those four registers (`K216`'s lanes, `wfixS` with all four), and at each cut the
replay fixes exactly the registers not yet written by then — `[13,14,15,24]` on cuts `1..3`,
`[13,14,15]` on `4..7`, `[15]` on `8..13` and none from cut `14` on.  `KH`'s four registers
are the turn-end values, which is what makes `KT_vr` hold (`vrRel 0 KH.vr KT.vr`); with the
pilot head's untouched abstract variables it would not.

The loop substitution is `tau : List Lin := [⟨1024, [1]⟩, ⟨512, [0, 1]⟩, ⟨-16, [0, 0, 1]⟩]`
(symbol `0` = input pointer, `1` = output pointer, `2` = count), so `sIt j σ` advances the
input by `1024j` and the output by `512j` and lowers the count by `16j`.  The output base in
`rax` sits on the untouched symbol `10`.

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
path).  The conclusion is literally the first clause of `X86Chain.KSpecC` for
`[x16spec env0 σ c, sp']` (`Hashtree/Proofs/X86Chain.lean`), so it slots into `chain_sound`
without any reshaping.  If R2 publishes a
different x8 entry predicate, `x8Pre` is the only definition to bridge; nothing inside the
x16 proof depends on the x8 side.  The σ-adjustment at symbol 2 (`σ 2 - 16`) and the fact that
symbols `0`/`1` have moved are both visible in `x8Pre`: the next link must not assume that
`σ` is the caller's original valuation.

*Status of the x4 side (checked 2026-11-13, read-only).*  R2's published link specs are
`AvxX4ToX1.x4spec` with `pre := fun s => s = {mapState env0 σ entryW with pc := 0}` and
`AvxX4ToX1.x1spec` with `pre := fun s => ∃ fl, s = {mapState env' σ entryW with flags := fl}`
(`Hashtree/Proofs/AvxX4ToX1.lean:52-66`): both are plain `entryW`-shaped and neither admits
the x16 tail state (advanced pointers, residual count, accumulated write log).  R2's file is
the x4 -> x1 small-count bridge, so no x4 link at an arbitrary count (and no
`x4Pre`-style predicate) exists yet.  `x8Pre` in this workstream is therefore the *assumed*
shape the wrapper-side x8 link must publish; when R2's x8 all-count spec lands, the only
obligation is `x8Pre f → x8spec.pre f`, plus the small-path form `KSm`.  The count-0 branch
of `x16post` is already exactly R2's plain `entryW` shape.

`x16post`'s first two branches are log-free `mapState` states (the count-0 return cut `KZ`
and the small-path tail cut `KSm`), so they compose with a next link whose pre-condition is
that cut up to `resume` (the small path is the `hpreS` argument above; the count-0 branch
returns and needs no next link).

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
from the call-state model.  Note that `WrapperPre.align_hom` does *not* cover this
instruction: it executes the wrapper's own `ANDQ $-32, SP` (`alignI`) on the *concrete*
`mapState env σ Kpre`, where `Ctl.asInt` sees the integer `σ 9 - 8`, and hands the kernel
`KC = entryW.substL tauC`; the kernel's copy of the same instruction has to be replayed from
the *symbolic* cut `x8P`, whose rsp is `⟨-8, stkC⟩` for every valuation, and
`asInt_sAt' : Ctl.asInt (⟨-8, stkC⟩) = none` holds *unconditionally* — no alignment premise
about `σ 9` can make the symbolic executor see it.  The fix is therefore a model change: add
the alignment premise `σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32` (the post-`push` stack pointer
aligned mod 32) and model the aligned stack pointer as a *fresh* aligned address symbol (a
`Ctl`/`Lin`-level notion of `w & -32`), not as `sAt k`.  That changes `mem0sW`'s `stackRel`
table (which recognizes stack cells only as `sAt k` / `trimC l.c = stkC`) and `Lin` in
`Hashtree/Asm/Core.lean`, so it is a change to the shared W-mode model rather than a local
proof and belongs with the wrapper's own alignment argument.  This is reported rather than
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

All heavy Lean ran on VM1, target builds only (`lake build <module>`, never `make all`, never
`-j`), with the toolchain's plain `lean` (`/root/.elan/toolchains/leanprover--lean4---v4.35.0`).

| target | wall clock | jobs | notes |
| --- | --- | --- | --- |
| `Hashtree.Proofs.Avx512X16WBody` | 3062 s (51 min) | 237 | includes the 215 `Gen.Avx512X16P` modules |
| `Hashtree.Proofs.Avx512X16WEntry` | 72 s | 241 | the three count cuts, the turn/exit cuts, `KT_gpr`/`KT_vr`/`KT_shape` |
| `Hashtree.Proofs.Avx512X16WBodyV` | 4105 s (68 min) | 244 | 215 slice re-checks from the loop head, 3218 instructions; run at load ~20 (a concurrent x4 build on the same VM), previously 65 min alone |
| `Hashtree.Proofs.Avx512X16WTurn` / `WLoop` | 10 s / 10 s | 245, 246 | after the 68-minute replay; 17 s / 17 s each in the rehearsal |

Rehearsal before the replay build: `Avx512X16WTurn` and `Avx512X16WLoop` were elaborated
first against a scratch copy of `Avx512X16WBodyV` in which only `bodyV_run`/`bodyV_mem` were
axiomatised (a 17 s turn build + 17 s loop build), because the real replay takes an hour.  That
found and fixed four errors in `Avx512X16WTurn` — `decide`/`omega` were being handed goals
whose `Addr` projections had not been reduced by the rewrite, and the `hrel` in `iter_step` /
`exit_step` asked `mem0RelW_of_wf` for the memory-derived environment `E := ecomb e σ mem` while
`WfMemW` was known for `e`; since the kernel pushes nothing the only environment-dependent
clause of `WfMemW` is vacuous, which is the new lemma
`Avx512X16WTurn.wfMemW_push_nil (rodata) (e e' : Key → W32) ... : WfMemW rodata [] e σ m →
WfMemW rodata [] e' σ m` — and three in `Avx512X16WLoop` (`getD_ge` had to be generalised from
a default `Lin.sym i` to an arbitrary default; the zero-turn run is `rfl`, not `simp`; and the
`steps_small` rewrite in `x16_all` had to happen inside the existential witness).  The tail of
`bodyV_run` was checked on its own in 5 s by axiomatising the 215 slice equations and replaying
the identical rewrite chain (`run_add`, the `KH` bridge, r1..r214, `← wfix_end`, `exact r215`);
all three scratch files were deleted.

The 215 `decide +kernel` slice checks dominate the build.  `Avx512X16WBodyV` imports
`Avx512X16WEntry`, so any change to the entry file (the cuts, `tau`, `wfix`, `KH`) forces a
full re-elaboration of the ~50-minute body chain as well; the entry file was therefore frozen
before the last build.

Gate: no `sorry` anywhere, every cut check is `decide +kernel` (no `native_decide`), and the
standalone audit `lake env lean AxiomsR2b.lean` (the same list as the `R2b` block of
`Axioms.lean`) reports only Lean's standard axioms for every theorem: exit code 0, all 38
`#print axioms` lines printed, no `sorryAx`; the 19 theorems that rest on a slice check also
carry the pre-existing generated `Hashtree.Asm.loadLane_hom._native.bv_decide.ax_1_6`
(the other 19 are pure `propext`/`Classical.choice`/`Quot.sound`).  The `R2b` block was
inserted into `Axioms.lean` with `r2b_axioms_block.py` (idempotent: it adds the two imports
after the last leading import and the `#print axioms` lines at the end of the file).
`Axioms.lean` itself is not elaborated in this worktree — it imports `ShaniAll`, `GoProof`,
`Glue`, `WrapperAmd64` and the three `Gen.*.Final` modules, whose oleans belong to the other
worktrees and are not built here; the audit file is the same list, so the gate ran there.

Two contract gaps found and reported (not weakened):

* the x8 alignment (§3) — a shared-model change, not a local proof;
* `InRange`/`OutOk`/`RegsOk` are *not* part of `x16post`: the link carries `err`, `tail`, the
  write log (`OutLog`, inside `x8Pre`) and the step function, but not the byte-level output
  statement nor a register-restoration statement.  `OutOk` (output byte `32 n + j` is byte `j`
  of the block's SHA-256) is the semantic content of the 16-lane body, which this workstream
  has not assembled; the x1 side gets it from `AvxX1All`'s `OutOk`/`InRange` machinery.
  `RegsOk` (callee-saved registers restored) is not reachable from this workstream either: the
  `avx512_x16` object never saves or restores a register — it has no prologue or epilogue at
  all (instructions `4..8` are the three `lea`s and the `jb`; the 22-instruction tail ends in
  the `jmp avx2_x8`), so the callee-saved registers are restored by whichever kernel at the end
  of the tail chain does it (x1, in R2's chain).  Stating `RegsOk` here would be stating a
  property of the tail, not of this link.  These are the remaining items on the x16 link.
