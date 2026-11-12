# Coverage

Rows of the fv-modexp project: machine code of geth v1.17.10 (`github.com/ethereum/go-ethereum`, `core/vm`), the Osaka MODEXP precompile
`PrecompiledContractsOsaka[0x05] = &bigModExp{eip2565: true, eip7823: true, eip7883: true}`, against the EthLib MODEXP specification
(`EthLib.Execution.Evm.Precompiles.Modexp`, pinned package `ethlibspec`, see README.md), for every fork `.fusaka ≤ fork`.
`scripts/verify-all.sh` reads this table: the Symbol cell is the exact symbol passed to `janus extract`; a row whose per-ISA status starts with
`verified` (or `partial`) is verified, `todo` / `in progress` fails the run as MISSING, `n/a` is skipped. The proof module of a row is
`lean/FvModexp/Proofs/<Arm64|Amd64>/<Fn>.lean` (or `<Fn>Main.lean` when it holds `theorem correctness`), with `<Fn>` = the last symbol component
with its first letter upper-cased. Every `verified` row has a kernel-checked `Witness.nonvacuous` (non-vacuity rule).

Sanity caps for every row (fixed in `scripts/verify-all.sh`): `memcap 16G`, `timeout 900`. Per-row time and peak RSS of the last run: `build/rows.tsv`;
module elaboration profiles: `docs/PERF.md`.

| Symbol | Owner | arm64 | amd64 | Notes |
|---|---|---|---|---|
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run` | top | todo | todo | row 1: Osaka receiver; lengths fail -> (nil, error), else (compute data (parseLengths data), nil); contracts: see `scripts/contract-flags.sh` |
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run` | top | partial (row 1 error path; janus-provfix 859eaa2a, correctness + Witness.nonvacuous, fresh-cache verify-all after the warm-up: 535 s / 6.4 GB at load ~15; s18 re-measure at load 35-60: 751 s / 6.5 GB; s19 after trims + 4-wide replay, load 20-30: 376 s) | partial (row 1 error path; same run: 802 s / 6.2 GB; s18 re-measure at load 35-60: TIMEOUT 901 s → amd64 RunErr modules trimmed → amd64-only fresh re-measure at load 45-55: 886 s / 4.9 GB; s19 after trims + 4-wide replay + per-ISA warm-up, load 20-30: 412 s) | row 1, error half: `checkLengths (parseLengths data)` fails -> returns (nil, non-nil error), no panic/fault, frame; module: `Top/RunErr`; success half = `Top/RunOkRow` (after the Janus v0.3.1 re-pin) |
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas` | infra | verified (janus-provfix 57c1094c, fresh cache, correctness + Witness.nonvacuous, olean provenance checked: da06a30 row 748 s / 3.9 GiB per job; split tree ee8a255 via verify-all: warm-up 807 s, row 824 s / 4.9 GiB per job, host load ~40) | verified (janus-provfix 859eaa2a, correctness + Witness.nonvacuous, audit + olean provenance + kernel replay passed: row 423 s / 5.7 GiB with the amd64 modules compiled in-row (warm framework cache), 193 s re-run; ISA=amd64 verify-all) | row 2: lengths pass -> `requiredGas fork data (parseLengths data)` for `.fusaka ≤ fork` (receiver = Osaka flags) |

Pure-Lean row 3 (no machine code): `FvModexp.Proofs.Compose.composition` in `lean/FvModexp/Proofs/Common/Compose.lean`, checked by `make build`.

## Function summaries feeding row 1 (owner top unless noted; all about the Run extraction)

| Function | arm64 | amd64 | Module / theorem |
|---|---|---|---|
| go-bigmodexpfix `nat.setBytes` | proved (no sorry) | proved (no sorry) | `Proofs/<Isa>/Nat/SetBytes.lean`: `FvModexp.<Isa>.SetBytes.{ens,sum}` |
| math/big `nat.setBytes` | proved (no sorry) | proved (no sorry) | `Proofs/<Isa>/Nat/SetBytesStd.lean`: `FvModexp.<Isa>.SetBytesStd.{ens,sum}` |
| go-bigmodexpfix `addTo` (divmc) | proved (no sorry; asm `addVV.abi0`, `addVW` summaries used; premises: live memmove contract) | same | `Proofs/<Isa>/Nat/AddTo.lean`: `FvModexp.<Isa>.AddTo.ens` |
| go-bigmodexpfix `nat.add` (divmc) | proved (no sorry; all paths incl. self-call swap, `z.set(x)`, reuse/alloc; premises: live makeslice + memmove contracts) | same | `Proofs/<Isa>/Nat/NatAdd*.lean`: `FvModexp.<Isa>.NatAdd.ens` |
| go-bigmodexpfix `nat.sub` (divmc) | proved (no sorry; Pre: `len y ≤ len x`, `Y ≤ X` (both panics refuted); premises: live makeslice + memmove) | same | `Proofs/<Isa>/Nat/NatSub*.lean`: `FvModexp.<Isa>.NatSub.ens` |
| go-bigmodexpfix `basicMul` (divmc) | proved (no sorry; hypothesis: asm `addMulVVWW.abi0`; row `BasicMulRow` VERIFIED janus-provfix, correctness + Witness.nonvacuous (s27), 238 s / 3.4 GB, load ~60) | same | `Proofs/<Isa>/Nat/BasicMul.lean`: `FvModexp.<Isa>.BasicMul.ens` |
| go-bigmodexpfix `nat.add` / `nat.sub`, empty-tolerant operands (`Pre0`, RdIn0 decision) (divmc) | proved (no sorry; derived summaries `ensR0`/`ensX0`/`ens0`; sub: x, y, z-window guarded (= infra's `SubPre0`), `SubMod2N.subHypR0_of`; add: x, y guarded) | proved (no sorry; `ensR0`/`ens0`) | `Proofs/<Isa>/Nat/Nat{Add,Sub}0*.lean`: `FvModexp.<Isa>.Nat{Add,Sub}.ensR0` |
| go-bigmodexpfix `nat.sqr` (incl. `basicSqr`, `karatsubaSqr`, `(*Int).Add/Sub`) (divmc) | proved (no sorry; `NatSqr.ens`, export `SqrHypX`; row `SqrRow` VERIFIED janus-provfix, correctness + Witness.nonvacuous, 570 s / 3.1 GB at host load ~55 (s27 trims; bottom-up after StackNat/MulAddWW/BasicMul/BasicSqr/IntAS rows in one fresh store, JANUS_REPLAY_THREADS=1; was 815 s)) | todo (port; LibSqr generated; amd64 (*Int).Add/Sub port in progress: IntASDefs/Val/Call/At/Post) | `Proofs/Arm64/Nat/{Sqr,KSqr}*.lean`: `FvModexp.Arm64.NatSqr.ens` |
| go-bigmodexpfix `nat.mul` (incl. `karatsuba`, `(*Int).mul`, `basicMul`, `mulAddWW`) (divmc) | proved (no sorry; `NatMul.ens`, SCC over nat.mul/karatsuba/(*Int).mul; exports `NatMul.hypX0`/`hypX`/`hypXE0`, `NatMulXE.hypXE`; row `MulRow` VERIFIED janus-provfix, correctness + Witness.nonvacuous, 370 s / 2.5 GB at load ~8 (s26); re-run s27 after the bottom-up rows incl. BasicMul/BasicSqr/IntAS/Sqr: 578 s / 2.2 GB at load ~50) | todo (port; LibMul generated) | `Proofs/Arm64/Nat/{Mul,KMul}*.lean`: `FvModexp.Arm64.NatMul.ens` |
| go-bigmodexpfix `nat.montgomery`, roomy (`cap(z) ≥ 2n`) (expmc) | proved (no sorry; asm's verified `addMulVVWW`/`subVV`; live memclr/memmove contracts) | same | `Proofs/<Isa>/Exp/Mont.lean`: `FvModexp.<Isa>.Mont.ens` (= Nat model `Exp.montgomery`) |
| go-bigmodexpfix `nat.{expNNEven,expNNOddMontgomeryWindowSize4/2,expNNPowerOfTwoWindowSize4/2}.deferwrap1` (`stk.restore`) (expmc) | proved (no sorry) | proved (no sorry) | `Proofs/<Isa>/Exp/Defer.lean`: `FvModexp.<Isa>.Defer.sum` |
| `(*Int).Mod`, `(*Int).exp`, `(*Int).Bytes` | hypothesis (interface draft v1) | todo | `Proofs/Arm64/Top/RunIface.lean`: `ModSpec`, `ExpSpec`, `BytesSpec` |
| `(*bigModExp).Run` body | todo | todo | — |
