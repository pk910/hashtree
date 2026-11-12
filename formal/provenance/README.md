# Provenance of the machine-code models

The proofs in `formal/lean` are about the instruction streams in
`Hashtree/Kernels/*`. This directory records which shipped artifacts those
streams came from and how to check that a new build still matches them.

## Basis

| Item | Value |
|---|---|
| hashtree source | `76c54d6dcf3596c03788ea5bc0ef030e9f1b43f4` (v0.2.6) |
| hashtree-bindings `lib/HASHTREE_VERSION` | `76c54d6dcf3596c03788ea5bc0ef030e9f1b43f4` |
| Objects | `ar x lib/<platform>/libhashtree.a` from hashtree-bindings |
| Cross-checked against | the `.syso` archives committed in hashtree (`76c54d6`, unchanged at `42836eb`) |
| Toolchains used for the models | `aarch64-linux-gnu-objdump`, `riscv64-linux-gnu-objdump`, `llvm-objdump` (Mach-O), `objdump`/`x86_64-w64-mingw32-objdump` (ELF/COFF) |
| Lean | `leanprover/lean4:v4.35.0` (`formal/lean/lean-toolchain`) |

`hashtree_*.syso` files are archives; `ar t` lists the kernel objects.

## The identity check

`check_instruction_identity.sh` extracts both archives, disassembles each
kernel object with the tool for its platform, and compares mnemonics and
operands after normalizing addresses, relocation placeholders and `<symbol>`
annotations. The streams are compared, not file bytes: the two builds differ in
metadata, archive layout and symbol decoration, which is irrelevant to the
model.

```
./formal/provenance/check_instruction_identity.sh /path/to/hashtree /path/to/hashtree-bindings/lib
```

Last run (2026-11-12, with the `.syso` at `42836eb` and the bindings archives
pinned to `76c54d6`): **all 21 kernel objects identical**. Per-object
instruction counts are in `instruction-identity.log`.

Notes on individual platforms:

- **linux/amd64**: six objects (`sha256_shani.o`, `sha256_sse_x1.o`,
  `sha256_avx_{x1,x4,x8,x16}.o`); identical.
- **linux/arm64**: three objects; identical.
- **linux/riscv64**: three assembly kernels; identical. The C objects in the
  archive (`sha256_generic.o`, `hashtree.o`) are not covered by a proof and are
  expected to change when upstream regenerates the syso after PR #81.
- **darwin/arm64**: three objects; identical streams, and the Lean models are
  also identical to the linux/arm64 ones except for the leading `_` of the tail
  symbol (`Hashtree/Kernels/ArmMac` vs `Hashtree/Kernels/Arm`).
- **windows/amd64**: six objects; identical to the bindings' Windows archive.
  They differ from the linux/amd64 objects (ABI), as expected.

## When artifacts change

Any change to `src/**` or to a `.syso` invalidates the tie between the proofs
and the shipped code until the check is rerun. The CI gate
(`formal/ci/proofs.py check`, run by
`.github/workflows/formal-verification.yml`) automates this:

1. It regenerates every model from the current `.syso` and compares the term
   stream with `Hashtree/Kernels/*`, and it checks the artifact/source hashes
   in `formal/proofs.json`.
2. If a stream changed, regenerate the model with
   `make -C formal/lean models`, rebuild that kernel's certificate with
   `make -C formal/lean regen KERNEL=<kernel>`, repack with
   `make -C formal/lean pack`, and commit the model, `formal/proofs.json` and
   the `Gen` archive/hashes.
3. Update `artifacts.sha256` and the log when the released objects change.

The identity check against `hashtree-bindings`' archives is separate and still
run manually with `./check_instruction_identity.sh` (see above). The C code
(`sha256_generic.c`, `hashtree.c`, detection, override) is not part of the
current machine-code proofs; see the gaps in `../README.md`.
