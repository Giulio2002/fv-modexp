# Development notes: conventions, proof techniques and tooling

A guide for people extending or re-checking the proofs. The status of every row is in [`COVERAGE.md`](COVERAGE.md), what to
trust in [`HUMAN-REVIEW.md`](HUMAN-REVIEW.md), the Go-level models in [`MODELS.md`](MODELS.md), timings in [`PERF.md`](PERF.md).
Older working notes are in [`history/`](history/); module comments that cite `docs/CONVENTIONS.md §n` refer to
[`history/CONVENTIONS-v2.md`](history/CONVENTIONS-v2.md), whose rules are summarised below.

## Workflow for one row

1. `make harness`: builds `build/harness-{arm64,amd64}` from `go/` (`GOTOOLCHAIN=go1.26.10 CGO_ENABLED=0 GOAMD64=v1
   -trimpath -buildvcs=false`) and checks `scripts/harness.sha256`.
2. Extract. Row 1 and every function summary it uses are about **one extraction per ISA**, that of `(*bigModExp).Run`:
   `janus extract build/harness-arm64 'github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run' build/x-Run-arm64 $(contract_flags Run)`
   (after `. scripts/contract-flags.sh`; 84 functions on arm64, 82 on amd64). Row 2 uses its own extraction of
   `(*bigModExp).RequiredGas`, which needs no runtime contract.
3. Write `lean/FvModexp/Proofs/<Isa>/<Area>/<Name>Row.lean` with `theorem correctness` (an `Ensures` stated with Janus
   vocabulary, `FvModexp.Spec.*` and EthLib) and `namespace Witness` with `nonvacuous` (a concrete returning run satisfying
   the precondition, with one call-site state for every runtime contract). Janus refuses a main theorem without it.
4. Add the row to `scripts/release-rows.txt` at its dependency position (`python3 scripts/row-order.py --keep-order` checks
   the order) and its flags to `scripts/contract-flags.sh` if it is a new symbol.
5. `make verify FN=<Area>_<Name>Row ISA=arm64` (the row id is the module path with `/` replaced by `_`).
6. Never edit `Spec/` or a `Proofs/Common` module while a `janus verify` that imports it runs: the input goes stale.

For quick iteration outside `janus verify`, `scripts/dev-lean.sh` compiles modules against the Janus/EthLib build of a kept
`janus verify` workspace, and `scripts/dev-rg.sh` compiles extraction-dependent modules against an `Extracted.lean`.

## Proof conventions

Every machine-code proof of a function that `Run` reaches follows the same statement shape, so that summaries compose
bottom-up into the row-1 theorems. Lean vocabulary: `Proofs/Common/{Conv,Link}.lean` (ISA independent) and
`Proofs/{Arm64,Amd64}/Conv.lean`. The `nat.setBytes` modules (`Proofs/<Isa>/Nat/SetBytes*.lean`) are a compact example
with a runtime call, three loops and both the reuse and the allocation branch.

* **Modules and names.** `Proofs/<Isa>/<Area>/<Name>.lean`, namespace `FvModexp.<Isa>.<Name>`, `<Name>` unique per ISA;
  areas `Nat`, `NatQ`, `Int`, `Exp`, `ExpQ`, `RG` (RequiredGas), `Top` (Run), `Witness`. An `Arm64` module never imports
  an `Amd64` one; `Proofs/Common` never imports `Extracted`. A function too large for one module is split into
  `<Name>Defs` (pre, post, invariants), one module per loop or segment, and `<Name>` composing them.
* **Exports.** Each function module exports `fn` (the full symbol), `names` (`fn` and every extracted function it reaches),
  `ens` (the `Ensures` theorem) and `sum` (`ens` turned into a summary a caller can use:
  `Ensures.toSummaryIn ens (noExit_restrict hap names) (codeIn_restrict_mono hap hsub)`).
* **Program.** `ens` is proved on `(Extracted.program.onlySegments names).link impl`, or faster on a generated library
  program equal to it (`scripts/gen-libprog-sub.py`, then `rw [eq_only]`). Addresses are never literals: entries are
  `segAddr Extracted.program fn`, loop heads `entry + offset`, contracts `Extracted.program.contractAddr "runtime.…"`,
  data `Extracted.dataAddr.«…»`.
* **Runtime.** One runtime invariant `R : RtInv` (Janus `Contracts/Live.lean`) is threaded through every call. Each runtime
  function the code calls is a hypothesis: the Janus live contract (`MakesliceLiveContract`, `MemmoveLive`,
  `NewobjectLiveContract`, `GrowsliceLiveContract`, `MemclrNoHeapPointersLive`, `WbLiveContract … n`, `PoolGetLive`,
  `PoolPutLive`; amd64 `…64` twins) about `Extracted.program.ofImpl impl`, with frame size 4096. The only premise on `impl`
  is `ImplApart Extracted.program impl`.
* **Call environment.** `CallEnv R L s stk above`: the stack check falls through with `stk` bytes to spare, the window
  `[SP - stk, SP + above)` is writable and outside the runtime-owned ranges, data is loaded, the stack-guard slot is apart
  from the window, no caller object lies in the window. `stk` is the function's frame plus the largest callee window
  (`framesize + 4096` for a runtime call), read off the disassembly. amd64 adds the TLS slot and keeps `fsBase`.
* **Values.** A Go `nat` `(ptr, len, cap)` has value `natVal m p n` (little-endian limbs); `limbs m p n` is the same slice as
  a model list (`Mdl.val (limbs m p n) = natVal m p n`); a `[]byte` read as a number is `beVal m p n` (big-endian).
  Results are stated about pre-state values. The bridge to EthLib's `ByteArray` (`Spec.bytesAt`) appears only in `Run`.
* **Objects and aliasing.** An input the function only reads: readable, below `2^48`, `Held R L p n` (inside a caller
  object or outside the runtime) and outside the window. An array it may write: `NatLive` plus outside the window and
  apart from the stack-guard word. Distinct objects are related by one atomic `Apart a n b k` fact each, only where the code
  needs it. A held range is unchanged by every runtime call and summary unless it is named in that callee's written set.
* **Live set and budget.** Pre: `R.inv b L g …`; post: `∃ L' b', LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' g …`, where
  `cost` is a closed upper bound on the bytes the function allocates (`allocCost n = 2n + 24`). The `Q` modules (`NatQ`,
  `ExpQ`) restate the multiplication, division and exponentiation summaries with tight per-call costs, which keeps Run's
  total budget below `2^35` bytes over the whole input range.
* **Requests.** The precondition states `R.ok` for exactly the runtime requests the function makes, guarded by the
  condition under which it makes them, never `∀ args, R.ok …` (the witness runtime must be able to serve them). Layers
  below `*Int` take the bounded `RunIface.Serves R` (requests up to 1 MiB / `2^17` elements).
* **Frame.** `MemFrame s.mem s'.mem (R.rt ++ window ++ ws) ∧ LiveFrame s.mem s'.mem L ws`, `ws` = the caller-visible ranges
  the function writes. On arm64 the window excludes the caller's saved `X29`/`X30` slots. Postcondition definitions are
  `@[reducible]` so that `janus_run … calls [F.sum …]` destructures them.
* **Panics.** `Ensures` means no panic and no fault under the precondition: every panic path (bounds, divide, nil
  dereference) is refuted by the precondition, and the precondition is implied by every call site that `Run` reaches. A
  panic not refutable from the call sites would be a finding.
* <a id="writable-globals"></a>**Writable globals** (`math/big` thresholds, `natOne`, `stackPool`, `runtime.writeBarrier`,
  amd64 `hasADX`): the precondition states the value the code reads (or none, where both values are proved) and that the
  global is outside the runtime-owned ranges. `Run` collects them in `Spec.RunArm64.Globals`/`NatOne`/`StackPool` (amd64:
  `Spec.RunAmd64.*`, plus `CpuOne`).
* **Hypothesis-first.** A caller may be proved before its callee by taking the callee's `sum` as a premise with exactly the
  statement `ens` will have. The row-1 theorems have no such premise: every callee is proved
  ([`HUMAN-REVIEW.md` §2](HUMAN-REVIEW.md#2-the-main-theorem-statements)).
* **Loops.** One `Reaches` lemma per loop head, by induction on the iterations left; the invariant is equations on the
  state plus `MemFrame` facts and the runtime invariant.

## Proof techniques worth keeping

[`PERF.md`](PERF.md#techniques-that-mattered) lists the speed techniques with measurements. In addition:

* **Name hypotheses by content**, never by position (`rename_i` breaks when an upstream summary gains a conjunct).
* After a `janus_run` through a callee, name the store chain once (`janus_frame`) and transport facts in a small pure
  lemma instead of simplifying memory terms in the big context.
* `janus_data hd [hw]` on the Run extraction (49 data objects) produces 49 disjunctions; use `janus_data hd` and add the one
  fact needed (`FvModexp.Arm64.apart_of_data`).
* Go's signed `/8` and arithmetic shifts on lengths need `asr63_small`, `sshiftRight_small`, `toInt_small` and friends
  (`Common/BitLemmas.lean`) passed to `janus_run`.
* Every `until` pc must be a correct literal offset; a wrong one lets `janus_run` go round a loop until the budget runs out,
  which looks like a hang.
* Syntax: write `(by omega)` in parentheses when more tactics follow on the line; give implicit arguments that occur only in
  a lemma's conclusion explicitly.

## Tooling

### Scripts used by the gates (`make lint`, `make verify`, `make check-generated`)

| script | role |
|---|---|
| `verify-all.sh` | build/check the harness, extract, `janus verify` every row under the caps, write `build/rows.tsv` |
| `release-rows.txt`, `row-order.py` | release order of the rows (dependency order; `--keep-order` checks it) |
| `witness-theorems.py` | the main and witness theorem names of a row module, passed to `janus verify` |
| `contract-flags.sh`, `noflags.txt` | `janus extract --contract …` flags per symbol |
| `build-harness.sh`, `harness.sha256` | the pinned binaries under verification |
| `no-sorry.sh` | text lint (`sorry`, `admit`, `sorryAx`); with `RELEASE=1` runs every lint below and requires an empty `WIP-SORRY.txt` |
| `lint_source.py`, `LintImports.lean`, `tactic-whitelist.txt` | source lint: compile-time commands, import hygiene (Lean's own header parser), metaprogramming only in whitelisted files, lakefile and symlink checks, heartbeat limits |
| `check-lean-lint`, `SvyTools.lean` | Lean-level lint: no IO, system primitives or initializers in any `FvModexp` declaration |
| `check-spec-closure`, `spec_survey.py` | every final statement depends only on `FvModexp.Spec`, Janus, `Extracted` and EthLib definitions, and on no EthLib instance |
| `check-ra-pin`, `RaPin.lean` | return-address pin checklist ([`HUMAN-REVIEW.md` §2b](HUMAN-REVIEW.md#2b-return-address-pins)) |
| `check-generated`, `gen-libprog-sub.py` | generated restricted-program modules equal the generator's output |
| `lint-tests/` | bypass attempts the lints must reject (`--selftest` modes) |

**Tactic whitelist.** `scripts/tactic-whitelist.txt` is `sha256<TAB>path` for the files allowed to define tactics. Under
`RELEASE=1` a changed whitelisted file fails the lint. After reviewing a change, run `scripts/lint_source.py
--update-whitelist` and commit the new hashes in the same commit as the change.

**Fresh cache.** A Janus cache built against another pin or extractor can poison the kernel replay, so `verify-all.sh` refuses
a non-empty `JANUS_CACHE_DIR` unless `ALLOW_WARM_CACHE=1` (development only).

### Generators

Several families of proof modules were produced mechanically. Only the restricted-program modules of
`gen-libprog-sub.py` (headers `GENERATED by scripts/gen-libprog-sub.py`) are checked by `make check-generated`; the other
generators are kept as a record of how their modules were first produced, and those modules may have been edited since.

| generator | output |
|---|---|
| `gen-libprog-sub.py` | restricted library programs (`Lib*`, one per function family) with `eq_only`; **checked** |
| `gen-libprog.py` | Extracted-free copies of single-function extractions (`Proofs/Lib/`, assembly leaf summaries) |
| `gen-libne-twins.py`, `gen-libne-twins64.py` | `LibNE` twins of `nat.expNN`'s path modules (arm64, amd64) |
| `gen-run-la.py`, `gen-run-la64.py`, `gen-run-de64.py` + `RunDE64.tmpl` | per-operand segment modules of `Run` (length headers, operand `setBytes` segments) |
| `gen-run-dj1-64.py` | **stale**: its output no longer matches the committed amd64 `Top/RunDJ*1` modules |
| `gen-grow-stub.py`, `gen-grow-stub64.py`, `grow-stub64.s` | machine words of the `growslice` stub used by the witnesses (`Witness/StubsGrow.lean`) |
| `gen/` | case and port generators cited by individual modules (`gen-sb-cases*.py`, `gen-w4seg-amd64.py`, `p2w4-body.py`, `port-*.py`, `q64/`), budget mirrors (`exp-budget-terms.py`, `mod-budget-check.py`: numeric checks, not proofs), `stmt-of-thm.py` |

### Other tools

| tool | role |
|---|---|
| `repin REV [JANUS_BIN]` | re-pin Janus to a release commit: lists the rebuild scope, updates `lean/lakefile.toml` and the manifest |
| `rel-summary.py` | verdict table of a release run from `build/` logs (time split, load) |
| `crit-path.py` | longest weighted import path of a row's modules (estimates row time from dev compile logs) |
| `used-imports/` | rewrite a module family's imports to the modules whose constants it uses |
| `exp-difftest/`, `muldiv-difftest/` | differential tests of the Nat-level models against the real Go code (`lean/tests/*.lean`, [`MODELS.md`](MODELS.md)) |
| `asm-row.sh`, `asm-runrow.sh` | run a single-function row: `lean/FvModexp/Legacy/` modules on their own extraction, or a summary row on the Run extraction |

### `lean/FvModexp/Legacy/`

The first proofs of the assembly leaf routines (`addVV`, `subVV`, `addMulVVWW`, `mulAddVWW`, `lshVU`, `rshVU`, `nat.cmp`,
`divWW`, arm64 `bits.Div64` and `reciprocalWord`) were stated on single-function extractions. They are kept in `Legacy/`
as standalone rows (`scripts/asm-row.sh`), imported by nothing and not part of the release run. The same machine code is
verified inside the release rows through the library summaries `Proofs/<Isa>/<Fn>Sum.lean`
([`COVERAGE.md`](COVERAGE.md#assembly-leaf-routines)).
