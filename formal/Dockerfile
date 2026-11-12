# Toolchain image for the Lean proof project.
#
#   docker build -f Dockerfile -t hashtree-formal .
#   docker run --rm hashtree-formal                 # make gen + verify + build
#   docker run --rm -it hashtree-formal bash        # interactive
#   docker run --rm hashtree-formal make regen      # regenerate Hashtree/Gen
#
# The image contains only the pinned Lean 4.35.0 toolchain, make and zstd.
# Hashtree/Gen is restored from the committed Gen.tar.zst; a full build needs
# several GB of RAM and tens of minutes, depending on the machine.

FROM debian:bookworm-slim

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl zstd make \
 && rm -rf /var/lib/apt/lists/*

# The official release archives are used instead of elan, so the toolchain is
# exactly the one in lean-toolchain (Lean 4.35.0).
ARG TARGETARCH
ARG LEAN_VERSION=4.35.0
RUN case "$TARGETARCH" in \
      amd64) lean_arch=linux ;; \
      arm64) lean_arch=linux_aarch64 ;; \
      *) echo "unsupported architecture: $TARGETARCH" >&2; exit 1 ;; \
    esac \
 && curl -fsSL -o /tmp/lean.tar.zst \
      "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-${lean_arch}.tar.zst" \
 && mkdir -p /opt/lean \
 && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 \
 && rm /tmp/lean.tar.zst \
 && /opt/lean/bin/lean --version

ENV PATH=/opt/lean/bin:$PATH

WORKDIR /work
COPY lean/ /work/

CMD ["make", "all"]
