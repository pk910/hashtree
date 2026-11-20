# Integration of the formal-verification branches

Branch `research/formal-integration`, built and checked on VM1 in a clean clone
(`/root/int/hashtree`), 2026-11-19/20.

## Merges (in order)

| step | branch | head | merge commit | conflicts |
|---|---|---|---|---|
| base | research/formal-r3r4-arm-riscv | 36f1b5a | — | — |
| 1 | research/formal-r4-riscv | 971467b | 473a7b7 | Axioms.lean, Makefile, regen.sh |
| 2 | research/formal-r2-amd64 | a21f67b | 6f18b18 | Axioms.lean, Makefile |
| 3 | research/formal-r2b-x8x16 | 45d55df | 94ddbd2 | Axioms.lean |
| 4 | research/formal-r5-windows | 0e69a20 | 073bd17 | Axioms.lean |
| — | research/formal-r2-winx4 | 905816a | (already contained in r5) | — |
| 5 | research/formal-r2c-x16out | 3490121 | 4386204 | Axioms.lean |
| 6 | research/formal-r3r4-arm-riscv | 07ba4ad (notes only) | 6b2731c | — |

Conflict resolution:
- `Axioms.lean`: union of every branch's imports and `#print axioms` lines, duplicates
  removed, all imports before the first `#print`. Each branch's lines are all present
  except r4's 14 pre-rename names, which are replaced by the renamed ones.
- `Makefile`: r3r4's memory-sizing note and the library-root build (`lake build Hashtree
  $(PROOF_MODULES)`, the 944ddb9 fix) kept. `audit` stays without the `build` prerequisite
  so it can be run separately after a capped build.
- `regen.sh`: the generator build line is the union (`... armloop1 rvloop`).
- No `.lean` proof-module conflicts.

## Decisions

- proofs.json mirrors the 14 Axioms.lean renames (pure name correction, no status change).
  The renamed theorems live in a namespace that differs from their file, so a unit's proof
  may now name the module per theorem (`"modules": {theorem: module}`), and `ci/proofs.py`
  uses it for the certificate presence check (5c95349).
- x86 pins are kept as-is; no x86 tree was regenerated.
- One `make pack` (d78fec6), 9256 files:
  - re-pinned only `ArmNeonX1P`/`ArmNeonX1P0` (`regen.sh neon_x1`; 129 files changed, file
    counts unchanged);
  - new pins: the riscv every-count loop trees `RvX1L`/`RvZbbX1L`/`RvCryptoL` (`rvloop`),
    and the git-tracked trees `SseX1LW`, `WinAvx2X8P`, `WinAvxX1LW`, `WinAvxX4P`,
    `WinSseX1LW`;
  - every other pinned file is byte-identical to the previous pack.
- `regen.sh` creates the arm output directories before `armproof`. Without this, a
  single-kernel regen first deletes them and then fails (59f802f).
- `ci/proofs.py check-audit` joins axiom lists that Lean wraps over several lines. Before
  this, every theorem with a long list (the bv_decide ones) was reported "not audited".

## Results (clean clone, head 6b2731c plus the proofs.py audit-parse fix)

- `make verify`: Gen matches the pinned hashes.
- `make gate`: all shipped kernels match their models and certificates.
- `make build` (library root and every Proofs/Gen module): green. `lake build` (default
  targets): green.
- `make audit` and `proofs.py check-audit`: 584 theorems, only propext / Classical.choice /
  Quot.sound / `*_native.bv_decide.ax_*`; 0 sorryAx; 0 native_decide / ofReduceBool.
  Includes the r2c `turnOut8W`/`turnOut8WLast` and `KSpecC8_of_turnOut8W`.
- `make check-models`: x86check 12 x 140 = 1680 runs, 0 failures; armcheck linux and mac,
  0 failures; rvcheck, 0 failures.

## Sizing observed

- `regen.sh neon_x1` needs more than 60 G (it was OOM-killed at 60 G); it passed under
  160 G in 70 min.
- The R5 W-mode modules `WinAvx2X8W{Shift,Strip}{8,24}c` take about 80 min each at about
  52 G. `WinAvx2X8LinkVr*` take about 25 G.
- The r2c modules `WinAvx2X8WOut{Chk,Cel,Shp}{X,XS}{8,24}` peak at 49–59 G, and
  `Gen/WinAvx2X8P/P211` at 44 G. A capped `make build` OOMs at 6 workers/110 G and 4/160 G
  once these overlap; 3 workers under 160 G completed (6.1 h).
