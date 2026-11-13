# fv-modexp

Machine-checked proofs, with [Janus](https://github.com/Giulio2002/Janus) v0.2.0 (Lean 4), that the **compiled linux/arm64 and linux/amd64 machine code** of
[go-ethereum](https://github.com/ethereum/go-ethereum) **v1.17.10**'s MODEXP precompile (`PrecompiledContractsOsaka[0x05] = &bigModExp{eip2565, eip7823, eip7883: true}`)
meets the **EthLib MODEXP specification**, for every fork from Fusaka on. Status of every row: [`docs/COVERAGE.md`](docs/COVERAGE.md).

## What is claimed

1. `(*bigModExp).Run`: for every input, with the Osaka receiver: if `checkLengths (parseLengths data)` fails it returns `(nil, error)`; otherwise `(compute data (parseLengths data), nil)`. No panic, no fault.
2. `(*bigModExp).RequiredGas`: when the lengths pass the EIP-7823 bound, the result is `requiredGas fork data (parseLengths data)` for every `fork` with `.fusaka ≤ fork`; otherwise it returns without panic or fault.
3. `FvModexp.Proofs.Compose.composition` (pure Lean): geth's `RunPrecompiledContract` logic (gas check, then run) agrees with EthLib's `modexp fork data gas`.

Every main theorem has a kernel-checked `Witness.nonvacuous` (a concrete returning run), so no statement is vacuous. What a reader must trust: [`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md).

## Sanity goal (project requirement)

Proofs must not take unbounded time or memory. **Hard caps, no override, for every `janus verify` row: 15 minutes wall and 16 GB** (`timeout 900`, `memcap 16G`, constants in `scripts/verify-all.sh`).
Every proof module's elaboration should take at most 5 minutes and 8 GB; anything above is profiled and fixed (summaries, segment splits, `Nat` normalisation, small `omega` contexts), never given
more heartbeats, timeouts or memory. Targets: median row at most 3 minutes; a full release run (both ISAs, 6 rows in parallel) at most 2 hours. Per-row time and peak RSS go to `build/rows.tsv`; before/after numbers of every fix are in `docs/PERF.md`.

## Pins and known limitations

* **Janus** v0.3.3 = `6d65752215a09ceaf88d18e2f11bac7bcf19eb82` (`lean/lakefile.toml`, `lean/lake-manifest.json`), Lean `v4.34.1`.
* **EthLib pin**: package `ethlibspec` = `github.com/Giulio2002/EthLib` branch `modexp-spec-lean-v4.34.1` @ `f4756ef5dc5619357f336e81166fb64a139abcd7`, a byte-identical copy of `ethereum/EthLib@ffd60c4bcbafa185ad8fbcf23be544d4b01f6d1c` (see its `UPSTREAM.md`); needed because upstream is on Lean v4.35.0. The spec is never edited here.
* **Go toolchain: 1.26.10 vs geth's 1.27.3.** geth's own release binaries are built with Go 1.27.3, which Janus v0.2.0's runtime pins do not cover. The harness (`go/`: geth v1.17.10, go-bigmodexpfix `f9e208c548ab`, holiman/uint256 v1.3.2) is built with the Janus-pinned
  `GOTOOLCHAIN=go1.26.10` (which satisfies geth's `go.mod`), `CGO_ENABLED=0 GOAMD64=v1 -trimpath -buildvcs=false`; its hashes are in `scripts/harness.sha256`. The verified artefact is geth v1.17.10 compiled by Go 1.26.10, not the shipped release binary.

## Running

`make help` lists targets: `make build` (lake build of `FvModexp`), `make harness`, `make verify [FN=RequiredGas] [ISA=arm64]` (needs `JANUS=/path/to/janus`, a fresh `JANUS_CACHE_DIR`, `memcap`, GNU `time`), `make audit`, `make lint` (`RELEASE=1 scripts/no-sorry.sh`).

## Layout

```
Makefile, scripts/   entry points, row runner (verify-all.sh), harness build + hashes, lints
docs/                COVERAGE.md, HUMAN-REVIEW.md, DEVELOPMENT.md, PERF.md
go/                  the harness (links geth's Osaka precompile set)
lean/FvModexp/Spec/  plain definitions every final statement depends on (human-reviewed)
lean/FvModexp/Proofs/{Common,Arm64,Amd64}/   proofs
```

Infrastructure adapted from [fv-uint256](https://github.com/Giulio2002/fv-uint256).
