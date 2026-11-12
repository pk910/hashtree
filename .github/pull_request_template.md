## Summary

<!-- What changes, and why. -->

## Formal verification (assembly / proof changes)

The heavy Lean check is not run in hosted CI. If this PR touches a `.S` file,
a model under `formal/lean/Hashtree/Kernels`, a generator, or a proof, the
author runs `formal/verify.sh` and an independent reviewer repeats it on the
same commit. Delete this section if none of those paths changed.

**Author report** (paste the fields from `formal/verification-report.json`):

- commit:
- toolchain:
- `gen.archive_sha256`:
- `gen.files_manifest_sha256`:
- audit result (clean / list of unexpected axioms):
- machine:

**Independent reviewer** (`formal/verify.sh` on this exact commit):

- [ ] I ran the full check myself and the tree was clean
- toolchain:
- `gen.archive_sha256`:
- `gen.files_manifest_sha256`:
- audit result:
- Verified-by:

- [ ] The cheap `models and certificates` gate is green
