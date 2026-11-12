#!/usr/bin/env bash
# Run the complete formal verification locally and write a report.
#
# The heavy Lean check is not run in hosted CI.  The author of an assembly or
# proof change runs this; an independent reviewer runs it again and compares
# the report (commit, toolchain, Gen archive hash, Gen file-manifest hash,
# audit result).  See formal/README.md, "Verifying a change without heavy CI".
#
#   formal/verify.sh                  # host toolchain (elan / lean 4.35.0)
#   formal/verify.sh --docker         # pinned containers instead
#   formal/verify.sh --out r.json --verifier "Name"
#
# The full build needs several GB of RAM; a machine with 8+ cores is strongly
# recommended.  Nothing here is written to git; the report is for the PR.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
MODE=host
OUT="${VERIFY_OUT:-$ROOT/formal/verification-report.json}"
VERIFIER="${VERIFIER:-}"

usage() {
  sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'
}

while [ $# -gt 0 ]; do
  case "$1" in
    --docker) MODE=docker; shift ;;
    --inside-container) MODE=container; shift ;;
    --out) OUT=$2; shift 2 ;;
    --verifier) VERIFIER=$2; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

# In container mode the Lean toolchain and proof dependencies come from the
# image; only the build, audit and report are run there.  The cheap gate needs
# binutils/python and runs in its own small image (or on the host).
if [ "$MODE" = host ]; then
  if ! command -v lake >/dev/null 2>&1; then
    if [ -x "$HOME/.elan/bin/lake" ]; then
      export PATH="$HOME/.elan/bin:$PATH"
    else
      echo "lake not found: install elan with the toolchain from lean-toolchain," \
           "or run formal/verify.sh --docker" >&2
      exit 2
    fi
  fi
fi

if [ "$MODE" = docker ]; then
  command -v docker >/dev/null 2>&1 || { echo "docker not found" >&2; exit 2; }
  commit=$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || true)
  branch=$(git -C "$ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || true)
  dirty=0
  if [ -n "$(git -C "$ROOT" status --porcelain 2>/dev/null || true)" ]; then dirty=1; fi

  if ! docker image inspect hashtree-proof-gate >/dev/null 2>&1; then
    echo "== building the proof-gate image"
    docker build -f "$ROOT/formal/ci/Dockerfile" -t hashtree-proof-gate "$ROOT/formal/ci"
  fi
  echo "== cheap gate (container)"
  docker run --rm -v "$ROOT:/repo" hashtree-proof-gate

  if ! docker image inspect hashtree-formal >/dev/null 2>&1; then
    echo "== building the Lean toolchain image"
    docker build -f "$ROOT/formal/Dockerfile" -t hashtree-formal "$ROOT/formal"
  fi
  echo "== full proof build and audit (container)"
  docker run --rm \
    -v "$ROOT:/repo" -w /repo \
    -e VERIFY_COMMIT="$commit" -e VERIFY_BRANCH="$branch" \
    -e VERIFY_DIRTY="$dirty" -e VERIFY_GATE=pass \
    -e VERIFY_OUT=/repo/formal/verification-report.json \
    -e VERIFIER="$VERIFIER" \
    hashtree-formal /repo/formal/verify.sh --inside-container
  exit $?
fi

cd "$ROOT/formal/lean"
AUDIT=$(mktemp -t hashtree-audit.XXXXXX)
trap 'rm -f "$AUDIT"' EXIT

if [ "$MODE" = host ]; then
  echo "== cheap gate: models, artifacts, certificate inputs"
  make gate
  export VERIFY_GATE=pass
else
  export VERIFY_GATE="${VERIFY_GATE:-skipped}"
fi

# The archive is what gets checked and shipped; refuse to silently overwrite a
# regenerated but unpacked tree (the author must `make pack` first).
if [ -d Hashtree/Gen ]; then
  if ! sha256sum -c Gen.files.sha256 --quiet; then
    echo "Hashtree/Gen does not match Gen.files.sha256." >&2
    echo "Run 'make pack' to commit the regenerated certificates, then rerun." >&2
    exit 1
  fi
fi

echo "== full proof build: every module under Hashtree/Proofs and Hashtree/Gen"
time make all

echo "== axiom audit"
make audit | tee "$AUDIT"

echo "== axiom policy"
python3 ../ci/proofs.py check-audit --repo ../.. --audit "$AUDIT"

echo "== report"
python3 ../ci/proofs.py report --repo ../.. --audit "$AUDIT" \
  --out "$OUT" --verifier "$VERIFIER" --command "formal/verify.sh"

echo
echo "verification report: $OUT"
echo "Compare its gen.archive_sha256 and gen.files_manifest_sha256 with the"
echo "author's report before approving.  A clean audit is not implied by exit 0."
