# Building the proof project.
#
# Hashtree/Gen contains ~2.6M lines of machine-generated Lean terms (420 MB
# plain text, 4 MB compressed). It is deterministic output of the generators in
# this directory, so it is kept out of git and restored from Gen.tar.zst.

LAKE ?= lake

.PHONY: gen verify build regen clean-gen

gen:            ## restore the pinned generated proofs
	@sha256sum -c Gen.sha256 --quiet
	@zstd -dc Gen.tar.zst | tar -x
	@echo "restored Hashtree/Gen"

verify:         ## check the restored tree against the pinned hashes
	@sha256sum -c Gen.files.sha256 --quiet
	@echo "Hashtree/Gen matches the pinned hashes"

build: gen      ## restore the generated proofs and build the library
	$(LAKE) build Hashtree

regen:          ## regenerate Hashtree/Gen from the committed models (long)
	./regen.sh

clean-gen:
	rm -rf Hashtree/Gen

.PHONY: all
all: gen verify build   ## restore, verify the hashes, and build the proofs
