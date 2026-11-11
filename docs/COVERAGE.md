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
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas` | infra | in progress | in progress | row 2: lengths pass -> `requiredGas fork data (parseLengths data)` for `.fusaka ≤ fork` (receiver = Osaka flags) |

Pure-Lean row 3 (no machine code): `FvModexp.Proofs.Compose.composition` in `lean/FvModexp/Proofs/Common/Compose.lean`, checked by `make build`.

## Function summaries feeding row 1 (owner top unless noted; all about the Run extraction)

| Function | arm64 | amd64 | Module / theorem |
|---|---|---|---|
| go-bigmodexpfix `nat.setBytes` | proved (no sorry) | proved (no sorry) | `Proofs/<Isa>/Nat/SetBytes.lean`: `FvModexp.<Isa>.SetBytes.{ens,sum}` |
| math/big `nat.setBytes` | proved (no sorry) | proved (no sorry) | `Proofs/<Isa>/Nat/SetBytesStd.lean`: `FvModexp.<Isa>.SetBytesStd.{ens,sum}` |
| go-bigmodexpfix `addTo` (divmc) | proved (no sorry; hypotheses: asm `addVV.abi0`, planned `addVW`) | same | `Proofs/<Isa>/Nat/AddTo.lean`: `FvModexp.<Isa>.AddTo.ens` |
| go-bigmodexpfix `basicMul` (divmc) | proved (no sorry; hypothesis: asm `addMulVVWW.abi0`) | same | `Proofs/<Isa>/Nat/BasicMul.lean`: `FvModexp.<Isa>.BasicMul.ens` |
| go-bigmodexpfix `nat.montgomery`, roomy (`cap(z) ≥ 2n`) (expmc) | proved (no sorry; asm's verified `addMulVVWW`/`subVV`; live memclr/memmove contracts) | same | `Proofs/<Isa>/Exp/Mont.lean`: `FvModexp.<Isa>.Mont.ens` (= Nat model `Exp.montgomery`) |
| go-bigmodexpfix `nat.{expNNEven,expNNOddMontgomeryWindowSize4/2,expNNPowerOfTwoWindowSize4/2}.deferwrap1` (`stk.restore`) (expmc) | proved (no sorry) | proved (no sorry) | `Proofs/<Isa>/Exp/Defer.lean`: `FvModexp.<Isa>.Defer.sum` |
| `(*Int).Mod`, `(*Int).exp`, `(*Int).Bytes` | hypothesis (interface draft v1) | todo | `Proofs/Arm64/Top/RunIface.lean`: `ModSpec`, `ExpSpec`, `BytesSpec` |
| `(*bigModExp).Run` body | todo | todo | — |
