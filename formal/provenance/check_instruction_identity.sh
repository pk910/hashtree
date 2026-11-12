#!/usr/bin/env bash
# Compare the instruction streams of the hashtree kernel objects in the shipped
# .syso archives with the objects in hashtree-bindings' lib/*/libhashtree.a.
#
# Usage:
#   check_instruction_identity.sh HASHTREE_REPO BINDINGS_LIB_DIR
# Defaults: the repository containing this script, and ../hashtree-bindings/lib.
#
# Requires: ar, and objdump/llvm-objdump for the target formats:
#   linux/amd64    objdump
#   linux/arm64    aarch64-linux-gnu-objdump (or llvm-objdump)
#   linux/riscv64  riscv64-linux-gnu-objdump (or llvm-objdump)
#   darwin/arm64   llvm-objdump
#   windows/amd64  x86_64-w64-mingw32-objdump
#
# Only instruction mnemonics and operands are compared; addresses, relocation
# placeholders and symbol annotations differ between the two builds.
set -u

root=$(cd "$(dirname "$0")/../.." && pwd)
repo=${1:-$root}
lib=${2:-$root/../hashtree-bindings/lib}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0

pick() { for c in "$@"; do command -v "$c" >/dev/null 2>&1 && { echo "$c"; return; }; done; return 1; }

norm() { # $1 = objdump, $2 = object
  "$1" -d --no-show-raw-insn "$2" 2>/dev/null | grep -E '^[[:space:]]+[0-9a-f]+:' \
    | sed -E 's/^[[:space:]]+[0-9a-f]+:[[:space:]]+//; s/[[:space:]]+<[^>]*>//g; s/[[:space:]]+/ /g'
}

check() { # $1 = platform label, $2 = lib dir name, $3 = objdump, $4.. = objects
  local label=$1 plat=$2 od=$3; shift 3
  mkdir -p "$tmp/syso-$label" "$tmp/lib-$label"
  ( cd "$tmp/syso-$label" && ar x "$repo/hashtree_$label.syso" ) || { echo "EXTRACT FAIL $label"; fail=1; return; }
  ( cd "$tmp/lib-$label" && ar x "$lib/$plat/libhashtree.a" ) || { echo "EXTRACT FAIL $label lib"; fail=1; return; }
  local o n1 n2
  for o in "$@"; do
    norm "$od" "$tmp/lib-$label/$o"   > "$tmp/a"
    norm "$od" "$tmp/syso-$label/$o" > "$tmp/b"
    n1=$(wc -l < "$tmp/a"); n2=$(wc -l < "$tmp/b")
    if [ "$n1" = "$n2" ] && cmp -s "$tmp/a" "$tmp/b"; then
      printf 'IDENTICAL  %-16s %-28s %6s instructions\n' "$label" "$o" "$n1"
    else
      printf 'DIFF       %-16s %-28s %6s vs %6s instructions\n' "$label" "$o" "$n1" "$n2"
      fail=1
    fi
  done
}

odin=$(pick objdump llvm-objdump)
oda=$(pick aarch64-linux-gnu-objdump llvm-objdump)
odr=$(pick riscv64-linux-gnu-objdump llvm-objdump)
odm=$(pick llvm-objdump objdump)
odw=$(pick x86_64-w64-mingw32-objdump llvm-objdump)

check linux_amd64 linux_amd64 "$odin" \
  sha256_shani.o sha256_sse_x1.o sha256_avx_x1.o sha256_avx_x4.o sha256_avx_x8.o sha256_avx_x16.o
check linux_arm64 linux_arm64 "$oda" \
  sha256_armv8_neon_x4.o sha256_armv8_neon_x1.o sha256_armv8_crypto.o
check linux_riscv64 linux_riscv64 "$odr" \
  sha256_riscv_x1.o sha256_riscv_zbb_x1.o sha256_riscv_crypto.o
check darwin_arm64 darwin_arm64 "$odm" \
  sha256_armv8_neon_x4.o sha256_armv8_neon_x1.o sha256_armv8_crypto.o
check windows_amd64 windows_amd64 "$odw" \
  sha256_shani.o sha256_avx_x1.o sha256_avx_x4.o sha256_avx_x8.o sha256_avx_x16.o sha256_sse_x1.o

[ "$fail" = 0 ] && echo "ALL KERNEL INSTRUCTION STREAMS IDENTICAL" || echo "MISMATCH"
exit "$fail"
