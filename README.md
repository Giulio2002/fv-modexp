# fv-modexp

Machine-checked proofs, with [Janus](https://github.com/Giulio2002/Janus) (Lean 4), that the **compiled arm64 and amd64 machine code**
of [go-ethereum](https://github.com/ethereum/go-ethereum) **v1.17.10**'s MODEXP precompile computes what the
[EthLib](https://github.com/ethereum/EthLib) MODEXP specification says, for every fork from Fusaka on.

The precompile is `PrecompiledContractsOsaka[0x05] = &bigModExp{eip2565: true, eip7823: true, eip7883: true}`. Its arithmetic
runs in `github.com/ethereum/go-bigmodexpfix`, a patched copy of Go's `math/big` (multiplication, Karatsuba, division,
Montgomery and windowed exponentiation, assembly vector kernels); all of that machine code is inside the proofs.

## What is proved

For geth's Osaka receiver and every input byte string `data` (the call data, read from memory as a Go `[]byte`):

1. **Row 1, `(*bigModExp).Run`.** If the three length headers pass the EIP-7823 bound (each at most 1024 bytes), `Run` returns
   `(compute data (parseLengths data), nil)`, where `compute` is EthLib's output function. Otherwise it returns `(nil, err)`
   with `err ≠ nil`. It never panics or faults, follows the Go ABI, and writes only its own stack window and fresh runtime
   memory.
2. **Row 2, `(*bigModExp).RequiredGas`.** If the lengths pass, it returns `requiredGas fork data (parseLengths data)` for every
   fork `fork ≥ .fusaka`. For every input, including ones that fail the bound, it returns without panic or fault.
3. **Row 3, composition** (pure Lean). geth's `RunPrecompiledContract` logic (gas check, optional result cache, then `Run`),
   applied to any precompile that meets rows 1 and 2, agrees with EthLib's `modexp fork data gas`. Either both fail, or both
   succeed with the same output and `gas - cost` left, where `cost` is EthLib's `chargedGas`.

Rows 1 and 2 are proved separately for linux/arm64 and linux/amd64. Every main theorem is paired with a kernel-checked
non-vacuity witness, a concrete run from a state that satisfies the precondition. For row 1 on success that run computes
`3^5 mod 7` and returns `[5]`. Janus refuses a main theorem without such a witness. Per-row status: [`docs/COVERAGE.md`](docs/COVERAGE.md).

## A worked example

The specification side is EthLib, used unchanged: `parseLengths`, `checkLengths`, `requiredGas`, `compute`, `chargedGas`,
`modexp` from `EthLib.Execution.Evm.Precompiles.Modexp`. The statements may not use instances or classes of a dependency, so
`lean/FvModexp/Spec/` adds a few plain definitions. These are the ones row 2 uses (from `Spec/Modexp.lean`, `Spec/Mem.lean`,
`Spec/Fork.lean`):

```lean
/-- The call data passes the EIP-7823 bound: `checkLengths (parseLengths data)` succeeds (every length header is at most 1024). -/
def LengthsPass (data : ByteArray) : Prop := checkLengths (parseLengths data) = Except.ok ()

/-- The Osaka receiver: the three `bool` fields `eip2565`, `eip7823`, `eip7883` of `*bigModExp` at address `p` are all `true`. -/
def OsakaReceiver (m : Memory) (p : Nat) : Prop :=
  (m.bytes p).toNat = 1 ∧ (m.bytes (p + 1)).toNat = 1 ∧ (m.bytes (p + 2)).toNat = 1

/-- The result `uint64` of a Go call, as a natural number (`X0` on arm64, `RAX` on amd64). -/
def u64 (x : BitVec 64) : Nat := x.toNat

/-- The `n` bytes at address `p` (a Go slice `(ptr = p, len = n)`), as a `ByteArray`. -/
def bytesAt (m : Memory) (p n : Nat) : ByteArray :=
  ⟨((List.range n).map fun i => byteOf m (p + i)).toArray⟩

/-- `fork` is Fusaka or later, in plain `Nat` order on the constructor index (`postFusaka_iff : PostFusaka fork ↔ Fork.fusaka ≤ fork`). -/
def PostFusaka (fork : Fork) : Prop := Fork.fusaka.ctorIdx ≤ fork.ctorIdx
```

The arm64 row-2 theorem, `FvModexp.Arm64.RequiredGas.correctness` (`lean/FvModexp/Arm64/RequiredGas.lean`), as written:

```lean
theorem correctness (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap]
      -- Pre: enough stack, the data the code reads is loaded, a real Go slice and receiver, Osaka flags, nothing overlaps the frame
      (fun s => GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544)
      -- Post: for every fork from Fusaka on, if the lengths pass, the result register is EthLib's requiredGas
      (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat)))
```

(The `--` comments are added here.) `Ensures prog entry args Pre Post` is Janus's total-correctness judgement for a Go
call: for every state that sets up this call and satisfies `Pre`, and then for every return address, execution of the
extracted bytes from that state with the return address installed reaches the return address without faulting or panicking,
obeys the Go ABI (callee-saved registers, stack pointer), and satisfies `Post`. Because `Pre` is evaluated before the return
address exists, no precondition can constrain where the call returns (Janus v0.4.0). `Extracted.program` holds the instruction bytes that `janus extract` copied out of the linked executable.
Lean decodes and runs them in Janus's ISA model.

Row 1 is stated the same way. Its success postcondition (`Spec/Arm64/Run.lean`) says the returned slice holds exactly
EthLib's output:

```lean
/-- `Run` returned `(out, nil)`: the nil `error` (type word `X3 = 0`) and `out = (X0, X1)` holds exactly the bytes
`compute data (parseLengths data)` of the EthLib specification. -/
def OkRet (data : ByteArray) (s' : State) : Prop :=
  s'.regs 3 = 0#64 ∧
    bytesAt s'.mem (s'.regs 0).toNat (s'.regs 1).toNat =
      EthLib.Execution.Evm.Precompiles.Modexp.compute data (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths data)
```

The one-theorem form of row 1, `FvModexp.Arm64.Run.correctness_total` (`lean/FvModexp/Arm64/RunTotal.lean`), shortened:

```lean
theorem correctness_total (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    -- … one hypothesis per runtime function Run calls (memmove, newobject, growslice, memclr, write barriers,
    --   sync.Pool Get/Put) and the shape `S : PoolShape` of the pooled object
    (W : Nat) (hW : 624 + 72944 ≤ W) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => S = StkShape ∧ RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧ … ∧
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) →
          RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b) ∧ …)
      (fun s s' =>
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧ RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
          RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') ∨
        (LengthsFail (bytesAt s.mem p.toNat len.toNat) ∧ RunArm64.ErrRet s' ∧
          RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s'))
```

Every definition in these statements is either Janus's, EthLib's, or in `lean/FvModexp/Spec/`, and
[`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md) §1 explains each one. `scripts/check-spec-closure` checks with Lean itself that
no final statement depends on anything else (in particular on nothing under `Proofs/`).

## Result

<!-- RELEASE: update this block on a re-pin or a new release run (Janus tag + commit, run id, counts, slowest row, lint). -->
**Release run rel51 on Janus v0.4.0** ([`b5db6432`](https://github.com/Giulio2002/Janus/commit/b5db64328e92cf4a5d5b87c32a9c66844b0d892b)):
**80/80 rows verified** (arm64 43/43, amd64 37/37), fresh cache per ISA, one row at a time, 2026-11-19.
One amd64 row (`NatQ/DrsRowQ`) hit the 900 s cap at a host load of 134 and passed on a single-row rerun (warm cache, load < 46); every other row inside the hard caps of 900 s and 16 GB; slowest arm64 `Exp/W4Row` (838 s), amd64 `NatQ/DivRowQ` (864 s). 11 rows took over 600 s, all at a host load far above normal (shared machine; details in [`docs/PERF.md`](docs/PERF.md)). Release lint clean.
Janus binary sha256 (amd64, built from the tag): `b92df613719f6d2f82b01be636f0801b9f7666540fbd9b5d6faabd1691239050`.

Previous release run, **rel50 on Janus v0.3.3** (2026-11-15), before the v0.4.0 migration: **80/80 rows verified** (arm64 43,
amd64 37). Fresh cache, one row at a time. Every row finished in under 600 s, inside the hard caps of 900 s and 16 GB; the
slowest were arm64 `Exp/NRow` (538 s) and amd64 `NatQ/DrsRowQ` (532 s). Release lint clean; the manual return-address audit
that v0.3.3 required was clean on all 80 rows.
<!-- /RELEASE -->

The 80 rows are the 4 claim rows per ISA plus the function summaries that row 1 composes (`nat.mul`, `nat.sqr`, Karatsuba,
`nat.div`, Montgomery multiplication, the window-2/4 and power-of-two exponentiations, `(*Int).Mod`, `(*Int).exp`, …).
Each summary is a verified row of its own. Per-row times are in [`docs/PERF.md`](docs/PERF.md).

## Check it yourself

| command | what it does |
|---|---|
| `make build` | `lake build` of the `FvModexp` library: the specification, the Go-level models, and row 3 (pure Lean) |
| `make harness` | build `build/harness-{arm64,amd64}` from `go/` and check their hashes against `scripts/harness.sha256` |
| `make verify` | `scripts/verify-all.sh`: extract and `janus verify` every row, both ISAs, in release order |
| `make verify FN=RequiredGas ISA=arm64` | one row on one ISA (row id = module path with `/` replaced by `_`, e.g. `RunSucc`, `Nat_DivWRow`) |
| `make audit` | statement audit and non-vacuity check only, without the kernel replay of the proofs |
| `make lint` | `RELEASE=1 scripts/no-sorry.sh`: no `sorry`/axioms, source and Lean-level lints, spec closure |
| `make check-generated` | generated proof modules equal their generator's output |

You need a `janus` binary built from the pinned commit (`go build ./cmd/janus` in the Janus repository), passed as
`JANUS=/path/to/janus`, plus `lake`, Go (the harness build sets `GOTOOLCHAIN=go1.26.10`), `python3`, GNU `time` and
`memcap`, the per-row memory cap. A release run needs an empty `JANUS_CACHE_DIR` (the default is a new directory under
`build/`). A full run of both ISAs takes about six hours one row at a time (`ROWS=N` runs rows in parallel); one row takes
between a few seconds and 10 minutes.

Example: `make verify JANUS=$HOME/janus/bin/janus FN=RequiredGas ISA=amd64`.

| component | version |
|---|---|
| Lean | `leanprover/lean4:v4.34.1` (`lean/lean-toolchain`) |
| Janus | v0.4.0, commit `b5db6432`, pinned in `lean/lakefile.toml` and `lean/lake-manifest.json` <!-- RELEASE: Janus pin --> |
| EthLib | package `ethlibspec` = [Giulio2002/EthLib](https://github.com/Giulio2002/EthLib) `f4756ef5`, byte-identical to `ethereum/EthLib@ffd60c4b` (see its `UPSTREAM.md`), on Lean v4.34.1 |
| geth | v1.17.10, with `go-bigmodexpfix` `f9e208c548ab` and `holiman/uint256` v1.3.2 (`go/go.mod`, `go/go.sum`) |
| Go | `go1.26.10`, `CGO_ENABLED=0 GOAMD64=v1 -trimpath -buildvcs=false`; binary hashes in `scripts/harness.sha256` |

## What you have to trust

The Lean kernel checks every proof. It cannot check that the statements mean what you want, or that the pieces outside the
proofs are right. A reader has to trust or review the following ([`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md) covers each in
detail):

* **The specification.** EthLib's MODEXP module at the pinned revision, and the plain definitions in `lean/FvModexp/Spec/`
  (fork order, memory-to-bytes, the Osaka receiver, and row 1's environment, budget and frame predicates).
* **The claim statements.** The `correctness` theorems of the claim rows and row 3's `composition`. Row 3 is pure Lean about
  an abstract precompile: it assumes rows 1 and 2 in value form (`RowsHold`). No Lean theorem derives `RowsHold` from the
  machine-code theorems; the reader checks that its three fields restate rows 1 and 2.
* **Runtime contracts.** The `Run` extraction treats twelve runtime entry points as unverified contracts: `makeslice`,
  `memmove`, `newobject`, `growslice`, `memclrNoHeapPointers`, five GC write barriers and `sync.(*Pool).Get`/`Put`. The row-1
  theorems take Janus's pinned contract for each one the proved code calls as a hypothesis, all sharing one runtime invariant. Row 2 assumes no contract; even
  `memmove` runs from its extracted machine code.
* **Janus.** Its ISA models of arm64 and amd64, the Go ABI model, the extractor, and the audit that classifies statements.
  Since v0.4.0, `Ensures` installs the return address after the precondition is evaluated, so no precondition can pin it
  ([`HUMAN-REVIEW.md` §2b](docs/HUMAN-REVIEW.md#2b-return-address-pins)).
  See Janus's `SOUNDNESS.md`.
* **The pinned harness build.** The verified bytes are those of `go/` (geth v1.17.10) compiled by the Janus-pinned
  **Go 1.26.10**. geth's own release binaries use **Go 1.27.3**, which Janus v0.4.0's runtime pins do not cover, so the
  shipped geth binary is not the verified artefact. amd64 is verified at `GOAMD64=v1` only. The proofs use absolute
  addresses of the pinned binary, which is why `verify-all.sh` checks its hash.
* **Stack growth and preemption are not modelled.** `runtime.morestack` never runs in the proofs: each precondition requires
  enough free stack that every stack check falls through, and no pending preemption request. Free stack required: row 1
  success more than 73 568 bytes (arm64) or 44 352 bytes (amd64), row 1 failure 4 800 bytes, row 2 464 bytes (arm64) or 456
  bytes (amd64). These are proof-side upper bounds, not measured stack depths. A call with less free stack, which real geth
  handles by growing the stack, is outside the claim.
* **Other environment assumptions.** Single-threaded execution and a non-moving heap. The precondition fixes the `math/big`
  thresholds and `natOne` at their initial values. Runtime requests stay below generous size bounds (`OkReqs`, at least 10×
  what EIP-7823-bounded inputs need). An allocation budget is stated as a premise and proved to be at most `2^35` bytes over
  the whole input range. On amd64 the `hasADX` byte must be readable; both code paths are proved.
* **Precompile result cache.** geth v1.17.10 caches precompile results by default. Row 3 models the cache and proves a hit
  returns what `Run` would. It assumes the cache holds only what geth's own stores put there (`CacheStoredBy`).

## Repository map

```
README.md          this file
Makefile           entry points (`make help`)
docs/              COVERAGE.md   status of every row
                   HUMAN-REVIEW.md   what to review: spec definitions, statements, assumptions, non-vacuity
                   MODELS.md     Go-level models (Nat transcriptions of the Go code) and assembly leaf preconditions
                   DEVELOPMENT.md    conventions, proof techniques, tooling
                   PERF.md       caps, release-run times, speed techniques
                   history/      development logs kept for provenance
go/                the harness: links geth's Osaka precompile set (its binaries are pinned by hash)
lean/              Lake package `fvmodexp`
  FvModexp/Spec/     the specification side: every definition a final statement depends on (reviewed by a human);
                     Spec/Arm64/Run.lean and Spec/Amd64/Run.lean hold row 1's per-ISA predicates
  FvModexp/Arm64/, FvModexp/Amd64/   the claim modules: RequiredGas, RunErr, RunSucc, RunTotal (the final theorems)
  FvModexp/Proofs/   proofs and proof-only definitions: Common/ (ISA-independent models and lemmas), Arm64/, Amd64/
  FvModexp/Legacy/   first single-function proofs of the assembly leaves (not part of the release run)
  tests/             differential `#guard` tests of the Go-level models against the real Go code
scripts/           verify-all.sh, release-rows.txt, lints (no-sorry.sh, lint_source.py, check-*), generators, pinned data
WIP-SORRY.txt      allowlist of unfinished modules for no-sorry.sh; empty at release
```

`Spec/` never imports `Proofs/`. The final theorems of rows 1 and 2 (`theorem correctness`, `namespace Witness`) are in
`lean/FvModexp/<Isa>/`. Every other release row, one per function summary, is a module under `lean/FvModexp/Proofs/<Isa>/`.

## More

* [`docs/COVERAGE.md`](docs/COVERAGE.md): every row, its Go function and status.
* [`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md): the review checklist and every assumption.
* [`docs/MODELS.md`](docs/MODELS.md): how the Go code is modelled and which no-panic facts are proved.
* [`docs/PERF.md`](docs/PERF.md) and [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md): how to extend the proofs and keep them fast.
* Infrastructure adapted from [fv-uint256](https://github.com/Giulio2002/fv-uint256), the same approach applied to `holiman/uint256`.
