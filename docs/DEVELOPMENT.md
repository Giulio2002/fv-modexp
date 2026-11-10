# Development notes (adapted from fv-uint256 docs/DEVELOPMENT.md)

Status of every row: `COVERAGE.md`; what to trust: `HUMAN-REVIEW.md`; speed record: `PERF.md`.

## Workflow for one row

1. `make harness` (or `scripts/build-harness.sh`): builds `build/harness-{arm64,amd64}` from `go/` with `GOTOOLCHAIN=go1.26.10 CGO_ENABLED=0 GOAMD64=v1 -trimpath -buildvcs=false`
   and checks `scripts/harness.sha256`.
2. Extract: `janus extract build/harness-arm64 'github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas' build/ex-arm64-RequiredGas <flags>`; the flags of a row
   are in `scripts/contract-flags.sh`.
3. Write `lean/FvModexp/Proofs/<ISA>/<Fn>.lean` with `theorem correctness : Ensures Extracted.program Extracted.entry [args] pre post` and `namespace Witness` (`nonvacuous`).
4. `JANUS=... make verify FN=<Fn> ISA=arm64` (rows: extract, `janus verify --proof ... --theorem FvModexp.<ISA>.<Fn>.correctness` plus the witness theorems), run under
   `memcap 16G` and `timeout 900`.
5. Never edit `Spec/` or a `Proofs/Common` module while a `janus verify` that imports it runs (the input goes stale).

## Rules

* Statements: only `FvModexp.Spec.*`, Janus, `Extracted` and plain EthLib definitions (no EthLib instances: `Spec.PostFusaka`, not `fork >= .fusaka`).
* Every Nat-level model of Go code is a faithful transcription of the Go source (cite file:line), proved equal to the mathematical function.
* Harness bytes are pinned by hash; library programs (Extracted-free programs holding addresses of the pinned binary) depend on that layout.
* Cache: a release run uses a fresh empty `JANUS_CACHE_DIR`.

## Lints (all by `RELEASE=1 scripts/no-sorry.sh`, i.e. `make lint`)

1. text-level `sorry` / `admit` / `sorryAx`, host IO tokens (`no-sorry.sh`);
2. `scripts/lint_source.py`: compile-time commands, import hygiene (Lean's own header parser), metaprogramming only in `scripts/tactic-whitelist.txt` files, lakefile/symlink checks
   (lakefile may require only `janus` and `ethlibspec`);
3. `scripts/check-lean-lint`: Lean-level IO / initializer lint (`scripts/SvyTools.lean`);
4. `scripts/check-spec-closure`: every statement depends only on `FvModexp.Spec.*` + Janus + Extracted + EthLib, and on no EthLib instance.
