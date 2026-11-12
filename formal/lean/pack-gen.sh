#!/usr/bin/env bash
# Pack Hashtree/Gen into the committed certificate archive.
#
# Run after `make regen` (whole tree) or `make regen KERNEL=x` (one kernel, with
# the rest restored by `make gen`).  Deterministic: sorted file list, zeroed
# timestamps/ownership; zstd -19 gives roughly 100x compression.
set -euo pipefail
cd "$(dirname "$0")"

[ -d Hashtree/Gen ] || { echo "Hashtree/Gen is missing; run make gen first" >&2; exit 1; }
[ -f Hashtree/Gen/AvxX4P/Final.lean ] || {
  echo "Hashtree/Gen is incomplete; run make gen (or make regen) first" >&2; exit 1; }

find Hashtree/Gen -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum > Gen.files.sha256
tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
    -cf - Hashtree/Gen | zstd -19 -T0 -q -f -o Gen.tar.zst
sha256sum Gen.tar.zst > Gen.sha256
python3 ../ci/proofs.py record-gen --repo ../..
echo "packed $(wc -l < Gen.files.sha256) files, $(stat -c%s Gen.tar.zst) bytes"
