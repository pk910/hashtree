# Formal verification of the hashtree kernels (Lean 4)

Machine-code-level proofs for the SHA-256 implementations shipped in this
repository's `.syso` archives, written in Lean 4 (toolchain pinned to
`leanprover/lean4:v4.35.0`). The project was developed against the artifacts
pinned by `hashtree-bindings` and is published here so it can be reviewed and
maintained next to `src/`.

**Status: research branch, not yet a complete proof of the library.** There are
no `sorry`s and no axioms beyond Lean's standard ones plus `bv_decide`'s native
certificates, but the coverage is uneven: several kernels are proved for every
block count, others for a single count; the amd64 wrapper is proved only under
two kernel contracts; the arm64, riscv64 and Windows wrappers, the C dispatcher
and the C fallback are not proved yet. The exact gaps and the work required to
close them are listed below.

## Layout

```
formal/lean/
  Hashtree/Spec.lean            SHA-256 (FIPS 180-4), K/H0 derived by kernel evaluation
  Hashtree/GoGeneric.lean       transliteration of sha256_1_generic.go
  Hashtree/GoProof.lean         generic fallback = spec
  Hashtree/Glue.lean            Hash / HashByteSlice / hashChunked contract (callSpec)
  Hashtree/Asm/                 machine models: x86-64, AArch64, RV64 + soundness
                                (exec_hom / run_hom), symbolic execution, frames
  Hashtree/Kernels/{X86,X86Win,Arm,ArmMac,Riscv}/
                                instruction streams of the shipped objects
  Hashtree/Gen/                 generated proof files (restored by `make gen`)
  Hashtree/Proofs/              all-counts proofs and the amd64 wrapper composition
  tools/                        object -> Lean translators and test harnesses
  X86Check.lean ArmCheck.lean RvCheck.lean
                                differential checks of every model against hardware
  X86Proof*.lean X86Loop*.lean ArmProof.lean RvProof.lean
                                proof generators (regenerate Hashtree/Gen)
```

The models are *instruction streams extracted from the shipped objects*; the
proofs quantify over those streams. `Hashtree/Kernels/*` therefore is the trust
anchor that ties the proofs to the `.syso` files; see
[`provenance/`](provenance/).

## Generated proofs

`Hashtree/Gen` holds about 2.6M lines (420 MB) of generated Lean terms: for
every symbolic slice, the abstract post-state as a literal (`K{c}`), the
kernel-checked equality `slice{c} : sliceCheck ... = true` (`decide +kernel`),
one `bv_decide` lemma per tracked lane, and a `Final.lean` that composes them
into the output theorem. None of it is hand-written: the generators in this
directory produce it deterministically from the committed instruction streams
(fixed seeds, no external input, no artifacts read).

It is therefore not committed as plain text. It ships as `Gen.tar.zst` (4.0 MB,
about 100x smaller), `make gen` restores it and checks the per-file hashes in
`Gen.files.sha256`, and `make regen` rebuilds the whole tree from source (CI
runs that to verify the archive). Everything outside `Gen` is about 100k lines
/ 6.5 MB: 78k lines of disassembled instruction streams (the trust anchor),
8.7k lines of machine models and their soundness proofs, 2.4k lines of
all-counts/wrapper proofs, and the spec, generators and tooling.

## What is proved

All statements are over the shipped machine code, for arbitrary input bytes and
arbitrary initial memory satisfying `WfMem`/`EnvMem`, with satisfiability
witnesses where noted. `OutOk` means every one of the `32*c` output bytes is the
corresponding SHA-256 node byte; `InRange` bounds the writes; `RegsOk`/`Foot` are
the Go ABI register and stack-footprint contracts.

| Platform | Object | Blocks | Theorem | Content |
|---|---|---|---|---|
| linux/amd64 | `sha256_shani.o` (shani_x2) | every `c` | `ShaniAll.shani_correct` (+ `shani_hyps_sat`) | halts, outputs correct, writes only the 32c output bytes + 88-byte frame, callee-saved registers and `rsp+8` per ABI |
| linux/amd64 | `sha256_sse_x1.o` | every `c` | `SseX1All.correct` (+ `hyps_sat`) | outputs correct (all counts) |
| linux/amd64 | `sha256_avx_x1.o` | every `c` | `AvxX1All.correct` (+ `hyps_sat`), `AvxX1W.correctW` | outputs correct; the `W` form starts at the wrapper's call state and includes `RegsOk` |
| linux/amd64 | `sha256_avx_x4.o` | `c = 4` | `Gen.AvxX4P.Final.out_final` | outputs correct |
| linux/amd64 | `sha256_avx_x8.o` (avx2_x8) | `c = 8` | `Gen.Avx2X8P.Final.out_final` | outputs correct |
| linux/amd64 | `sha256_avx_x16.o` (avx512_x16) | `c = 16` | `Gen.Avx512X16P.Final.out_final` | outputs correct |
| linux/amd64 | Go wrapper | — | `WrapperAmd64.wrapper_correct` (+ `wrapper_hyps_sat`) | for the kernel selected by the feature bytes: halts, outputs correct, frame footprint `Foot`, dispatch follows the three feature flags. **Hypotheses:** `Fits .avx2`, `Fits .avx512` (`Fits .shani` and `Fits .avx1` are proved, `fits_shani`, `fits_avx1`) |
| linux/arm64 | `sha256_armv8_crypto.o` (sha_x1) | `c = 2` | `Gen.ArmShaX1P.Final.out_final` | outputs correct; stack use 32 B |
| linux/arm64 | `sha256_armv8_neon_x1.o` | `c = 2`, `c = 0` | `Gen.ArmNeonX1P.{Final.out_final, ArmNeonX1P0.Final.only_stack_writes_run}` | outputs correct; stack use 64 B; the `c = 0` case proves only stack writes and halt |
| linux/arm64 | `sha256_armv8_neon_x4.o` | `c = 4` | `Gen.ArmNeonX4P.Final.out_final` | outputs correct; stack use 1024 B; the tail jump to `neon_x1` is modelled but not chained into a proof |
| darwin/arm64 | all three kernels | — | — | models validated by execution; instruction streams are identical to linux/arm64 except the leading `_` in the tail symbol (`bTail`), so the ARM theorems transfer with a rename lemma. No proof object is built separately |
| windows/amd64 | all six kernels | — | — | models validated by execution (1680 runs); the code differs from linux/amd64 (calling convention, shadow space), no functional proof yet |
| linux/riscv64 | `sha256_riscv_{x1,zbb_x1,crypto}.o` | `c = 2` | `Gen.Rv{X1,ZbbX1,Crypto}P.Final.out_final` (+ `hyps_sat`) | outputs correct; no alignment assumptions needed |
| linux/riscv64 | dispatcher `hashtree_hash` | — | — | only concrete validation (9 probe answers); no symbolic proof |
| Go | `sha256_1_generic` | any length | `GoProof.sha256_1_generic_eq` | = FIPS 180-4 |
| Go API | `Hash`, `HashByteSlice`, `hashChunked` | any `n` | `Glue.Hash_spec`, `Glue.HashByteSlice_spec`, `Glue.hashChunked_spec` | = SHA-256 of the concatenated blocks under the aliasing contract |

Not proved: `src/sha256_generic.c`, the C dispatcher and feature detection,
`hashtree_init`/`hashtree_override`, the arm64, riscv64 and Windows Go
wrappers, the morestack path, and the AVX-512/AVX2 tails needed to discharge the
two `Fits` hypotheses of the amd64 wrapper. The Go feature gating that drives
the wrappers (`hasShani`, `hasAVX512`, `hasAVX2`) is not yet connected to a
proved ISA census.

## Compatibility with the shipped library

The proofs are over instruction streams, not over archive bytes, so what matters
is whether the models still describe the shipped objects.

- The proof basis is `hashtree` commit `76c54d6` (v0.2.6), the commit pinned by
  `hashtree-bindings`' `lib/HASHTREE_VERSION`. The objects were taken from
  `lib/*/libhashtree.a`.
- The kernel instruction streams in those archives are **identical to the ones
  in the upstream `.syso` archives** for every kernel on all five platforms
  (21 objects). This includes the macOS and Windows archives. The check is in
  [`provenance/check_instruction_identity.sh`](provenance/check_instruction_identity.sh),
  last output in [`provenance/instruction-identity.log`](provenance/instruction-identity.log).
- The upstream `.syso` blobs are unchanged between `76c54d6` and the current
  `main` (`42836eb`, 2026-11-12); see
  [`provenance/artifacts.sha256`](provenance/artifacts.sha256).
- Since `76c54d6`, upstream changed only `wrapper_arm64.s` (PR #79), the riscv
  C build flags (PR #81) and tests/CI. No kernel code changed. The kernel
  theorems therefore apply unchanged to the current library.
- PR #79 moves `RSP` into the declared 2048-byte frame around the NEON call.
  That is exactly the frame the ARM `neon_x4` proof assumes when it reports a
  1024-byte stack footprint: the footprint now lands at
  `[SP_body+1024, SP_body+2048)`, inside the Go frame, and no longer below
  `g.stack.lo`. The kernel proof (which measured the 1024-byte use) is the
  formal half of that argument; the wrapper's `ADD`/`SUB` still needs its own
  small proof (see R4).
- The bindings' switch to a full copy of the upstream library (bindings PR 3)
  does not invalidate anything: the copy carries the same instruction streams.
  What is needed is a check that the copied/regenerated objects still match
  `Hashtree/Kernels/*`. Rebuilding from the same source with a different
  compiler or assembler can change code (in particular for the C parts and for
  the riscv baseline change in PR #81), so every `.syso` refresh should rerun
  the identity check and, where the streams changed, regenerate the models and
  re-elaborate the proofs.

## What remains for a complete proof of the library

Target end-to-end statement (per platform, per wrapper): for every feature state
and every `c`, `HashtreeHash` (wrapper + selected kernel, or wrapper + C
dispatcher + kernel) halts, writes exactly `32*c` bytes equal to the SHA-256
node bytes of the input blocks, touches no byte outside the output range and
the Go frame, preserves the Go ABI registers and SP, and — using the Go
prologue's stack guarantee — never accesses memory below `g.stack.lo`.
Composed with `Glue.Hash_spec`, this gives the advertised API contract.

Remaining work, in dependency order:

1. **Build infrastructure (S).** Heavy Lean builds need a build machine again;
   the previous VM is gone and its state is archived (restore recipe in the
   project archive). Add a CI job (elan + Lean cache, per-kernel matrix) and a
   job that runs the artifact-identity check on every `src/**` or `.syso`
   change. Cache `Hashtree/Gen` oleans; a full build of all current proofs is
   tens of minutes and several GB.
2. **linux/amd64 completion (L).** Every count for `avx_x4`, `avx2_x8`,
   `avx512_x16` (the X86Loop/X86ProofV generators exist; the multi-lane
   all-counts work was started and stopped), the tail chains
   `x16 -> x8 -> x4 -> x1` as `KSpec` compositions with the right stack shift,
   `Fits .avx2`/`Fits .avx512`, alignment for `avx2_x8`'s `and rsp,-32`, the
   morestack path and the TLS no-op. This discharges both hypotheses of
   `wrapper_correct` and makes the default amd64 path unconditional.
3. **linux/arm64 + darwin/arm64 completion (L).** Every count for `sha_x1`,
   `neon_x1`, `neon_x4`; chain the `neon_x4 -> neon_x1` tail; prove the ARM
   frame/stack-shift lemma analogous to `X86Frame`; model and prove the PR #79
   wrapper (`ADD $2048, RSP` around the NEON call only, separate return paths,
   correct pcsp delta, 16-byte alignment, `K2`/`K3`); transfer the kernel
   theorems to the Mach-O models via the tail-symbol rename. This closes the
   formal version of U1 on the code that now ships.
4. **linux/riscv64 completion (M).** Every count for the three kernels; a
   symbolic `hashtree_hash` dispatcher (hwprobe as a symbolic input; the
   `xor`-canary simplification noted in the RV notes); `hashtree_init` feature
   detection; the `sp = 8 (mod 16)` alignment invariant (B7); the Go wrapper
   `$0-24` calling convention.
5. **windows/amd64 completion (L).** Functional proofs for the six COFF
   kernels (different ABI: shadow space, `R12`, `xmm6-xmm15`; the AVX-512
   clobber observation U6) and the `$1024-24` Windows wrapper.
6. **C code completion (M-L).** `src/sha256_generic.c` (now built for the RV64GC
   baseline after PR #81), `src/hashtree.c` dispatch/detection/override, or a
   refinement argument that the Go-side gating never selects an unsupported
   path. This is what connects the riscv wrapper to the proved kernels.
7. **Go glue composition (M).** Instantiate `Glue.callSpec` with each platform's
   proved wrapper+kernel chain, including the feature-flag invariant, and state
   the top-level API theorems (`Hash`, `HashByteSlice`, `hashChunked`) per
   platform.
8. **Satisfiability and axiom audit (S).** Add the missing explicit
   `hyps_sat`-style witnesses for the fixed-count multi-lane theorems and check
   `#print axioms` for every final theorem. (The all-counts theorems already
   carry witnesses.)
9. **Documentation and maintenance (S).** Keep the proof-to-artifact mapping,
   the regeneration commands, and the CI identity check in this directory.

## Building

Requires `elan` with the toolchain from `lean-toolchain` (Lean 4.35.0), `zstd`
and `sha256sum`:

```
cd formal/lean
make gen                       # restore Hashtree/Gen from Gen.tar.zst
make verify                    # check it against Gen.files.sha256
lake build Hashtree            # library; the generated proofs dominate the time
lake exe x86check linux        # differential check of the x86 models
lake exe armcheck linux        # AArch64 (also: armcheck mac)
lake exe rvcheck               # RV64

make regen                     # rebuild Hashtree/Gen from the models (long)
lake exe x86proof <dir> <first> <last>   # regenerate one slice of a Gen tree
```

The `*check` executables need no local artifacts: the instruction streams are
embedded in `Hashtree/Kernels`. The generators re-read objects extracted from
the `.syso`/`libhashtree.a` archives only when the *models* are regenerated;
see `tools/` for the object-to-Lean translators and their required cross
tools. `make regen` works from the committed models and needs no artifacts.

## Provenance

`Hashtree/Kernels/*` was generated from the objects listed in
[`provenance/artifacts.sha256`](provenance/artifacts.sha256), which also records
the source commit and the identity check between the bindings archives and the
upstream `.syso` files. Commit history of the proof project is preserved in
`hashtree-bindings` (branch `formal-verification`); this branch imports the tree
at its final state.

## License

MIT, same as the rest of the repository (see `../LICENSE`).
