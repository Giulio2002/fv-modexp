# fv-modexp: entry points for building and checking the proofs. `make help` lists them.
#
# Environment variables (all optional unless noted):
#   JANUS             path of the janus binary (required by verify, audit, lint and check-generated; default: `janus` on PATH)
#   JANUS_CACHE_DIR   Janus result cache; a release run needs a FRESH EMPTY directory (default: a new build/jcache-<stamp>)
#   ROWS              rows verified in parallel (default 1); LEAN_NUM_THREADS, JANUS_JOBS: see scripts/verify-all.sh
#   FN                verify only these rows, e.g. FN=RequiredGas or FN="Top_RunErr Top_RunSucc" (row id = module path, / -> _)
#   ISA               verify only this ISA: arm64 or amd64
# The per-row caps (memcap 16G, timeout 900 s) are constants of scripts/verify-all.sh and cannot be overridden.
SHELL := /usr/bin/env bash
JANUS ?= janus
export JANUS
export JANUS_CACHE_DIR
export ROWS

RUN_SYM := github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run

.PHONY: help build harness verify audit lint check-generated ra-pin clean

help:
	@sed -n '2,9p' Makefile
	@echo
	@echo "targets: build harness verify audit lint check-generated ra-pin clean"

# lake build of the FvModexp library (specification and extraction-independent lemmas, incl. the pure-Lean row 3).
# Env: none beyond the toolchain in lean/lean-toolchain.
build:
	cd lean && LEAN_NUM_THREADS=4 lake build FvModexp

# Build build/harness-{arm64,amd64} from go/ and check them against scripts/harness.sha256. Env: none (needs Go; GOTOOLCHAIN is set by the script).
harness:
	bash scripts/build-harness.sh

# Extract and `janus verify` every row: scripts/release-rows.txt in that order, then the remaining docs/COVERAGE.md rows.
# Env: JANUS, JANUS_CACHE_DIR, ROWS; FN=... and ISA=... select a subset. Per-row time and peak RSS: build/rows.tsv.
verify:
	ONLY_ISA="$(ISA)" scripts/verify-all.sh $(FN)

# Audit only: the statement audit and non-vacuity check, without the kernel replay of the proofs. Env: as `verify`.
audit:
	JANUS_STOP_AFTER_AUDIT=1 ONLY_ISA="$(ISA)" scripts/verify-all.sh $(FN)

# Release lint: no sorry/axioms, source and Lean-level lints, spec closure. Env: JANUS (needed for the spec survey);
# needs build/harness-{arm64,amd64} (`make harness`).
lint:
	RELEASE=1 scripts/no-sorry.sh

# Generated restricted-program modules must equal the output of scripts/gen-libprog-sub.py on the pinned Run extraction
# (never writes tracked files). Env: JANUS (to extract build/x-Run-<isa> when it is missing).
check-generated:
	@for isa in arm64 amd64; do \
	  if [ ! -f build/x-Run-$$isa/Extracted.lean ]; then \
	    [ -f build/harness-$$isa ] || bash scripts/build-harness.sh || exit 1; \
	    . scripts/contract-flags.sh; \
	    $(JANUS) extract build/harness-$$isa '$(RUN_SYM)' build/x-Run-$$isa $$(contract_flags Run) >build/x-Run-$$isa.log || exit 1; \
	  fi; \
	done
	python3 scripts/check-generated

# Return-address pin checklist (docs/HUMAN-REVIEW.md section 2b): self-test, then the report build/rapin/report.txt for the
# release rows. Env: RAPIN_ARGS (e.g. `--isa arm64 --oleans <consumer dir of a release cache>`; see scripts/check-ra-pin).
ra-pin:
	scripts/check-ra-pin --selftest
	scripts/check-ra-pin --release -j 2 $(RAPIN_ARGS)

# Remove build outputs (harness binaries, extractions, caches, logs). Env: none.
clean:
	rm -rf build
