# fv-modexp: entry points for building and checking the proofs. `make help` lists them. Adapted from fv-uint256.
#
# Environment variables (all optional unless noted):
#   JANUS             path of the janus binary (required by verify, audit and lint; default: `janus` on PATH)
#   JANUS_CACHE_DIR   Janus result cache; a release run needs a FRESH EMPTY directory (default: a new build/jcache-<stamp>)
#   ROWS              rows verified in parallel (default 1; release: 6)
#   FN                verify only these rows, e.g. FN=RequiredGas or FN="RequiredGas OsakaModexpGas"
#   ISA               verify only this ISA: arm64 or amd64
# The sanity caps (memcap 16G, timeout 900 s per row) are fixed in scripts/verify-all.sh and cannot be overridden.
SHELL := /usr/bin/env bash
JANUS ?= janus
export JANUS
export JANUS_CACHE_DIR
export ROWS

.PHONY: help build harness verify audit lint clean

help:
	@sed -n '2,10p' Makefile
	@echo
	@echo "targets: build harness verify audit lint clean"

# lake build of the FvModexp library (Spec and extraction-independent lemmas; needs lake, the pinned Janus and EthLib packages).
build:
	cd lean && LEAN_NUM_THREADS=4 lake build FvModexp

# Build build/harness-{arm64,amd64} from go/ and check scripts/harness.sha256.
harness:
	bash scripts/build-harness.sh

# Extract and `janus verify` every verified row of docs/COVERAGE.md (rows.tsv: time and peak RSS per row).
verify:
	ONLY_ISA="$(ISA)" scripts/verify-all.sh $(FN)

# Audit only: the statement audit and non-vacuity check, without the kernel replay of the proofs.
audit:
	JANUS_STOP_AFTER_AUDIT=1 ONLY_ISA="$(ISA)" scripts/verify-all.sh $(FN)

# Release lint: no sorry/axioms, source and Lean-level lints, spec closure (statements depend only on Spec/ + pinned EthLib, no EthLib instances).
lint:
	RELEASE=1 scripts/no-sorry.sh

clean:
	rm -rf build
