# Proof gate image: everything needed to check that the shipped kernel objects
# still match the Lean models, without a Lean toolchain.
#
#   docker build -f formal/ci/Dockerfile -t hashtree-proof-gate formal/ci
#   docker run --rm -v "$PWD:/repo" hashtree-proof-gate
#
# For the expensive certificate build use formal/Dockerfile instead.
#
# The base is trixie (LLVM 19): LLVM 14 in bookworm cannot disassemble the
# ARMv8.2 SHA-256 instructions in the Mach-O objects and prints `<unknown>`,
# which makes the darwin models unreproducible.
FROM debian:trixie-slim

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      binutils \
      binutils-aarch64-linux-gnu \
      binutils-riscv64-linux-gnu \
      binutils-mingw-w64-x86-64 \
      llvm \
      python3 \
      zstd \
      ca-certificates \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /repo
ENTRYPOINT ["python3", "formal/ci/proofs.py", "check", "--repo", "."]
