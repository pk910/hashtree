# Building the proof project.
#
# Hashtree/Gen contains ~2.6M lines of machine-generated Lean terms (420 MB
# plain text, 4 MB compressed). It is deterministic output of the generators in
# this directory, so it is kept out of git and restored from Gen.tar.zst.

LAKE ?= lake
KERNEL ?= all

.PHONY: gen verify build regen pack models gate check-models audit clean-gen

gen:            ## restore the pinned generated proofs
	@sha256sum -c Gen.sha256 --quiet
	@zstd -dc Gen.tar.zst | tar -x
	@echo "restored Hashtree/Gen"

verify:         ## check the restored tree against the pinned hashes
	@sha256sum -c Gen.files.sha256 --quiet
	@echo "Hashtree/Gen matches the pinned hashes"

# `lake build Hashtree` only builds the hand-written library (the library's
# root module and its imports); it does not touch Hashtree.Gen.  Building every
# module explicitly is what makes the Lean kernel re-check every certificate.
# The list is expanded after `gen` has restored Hashtree/Gen.
PROOF_MODULES = $(shell find Hashtree/Proofs Hashtree/Gen -name '*.lean' 2>/dev/null | sed -e 's|/|.|g' -e 's|\.lean$$||') Axioms

build: gen      ## restore the generated proofs and check every proof module
	$(LAKE) build $(PROOF_MODULES)

regen:          ## regenerate Hashtree/Gen from the committed models (KERNEL=name for one)
	./regen.sh $(KERNEL)

pack:           ## repack Hashtree/Gen into Gen.tar.zst and update the hashes
	./pack-gen.sh

models:         ## regenerate Hashtree/Kernels from the .syso files, update proofs.json
	python3 ../ci/proofs.py gen-models --repo ../..

gate:           ## cheap CI gate: models, artifacts and certificates (no Lean)
	python3 ../ci/proofs.py check --repo ../..

check-models:   ## differential execution of every model against the spec
	$(LAKE) exe x86check
	$(LAKE) exe armcheck linux
	$(LAKE) exe armcheck mac
	$(LAKE) exe rvcheck

audit:          ## print the axioms of every final theorem
	$(LAKE) env lean Axioms.lean

clean-gen:
	rm -rf Hashtree/Gen

.PHONY: all
all: gen verify build   ## restore, verify the hashes, and build the proofs
