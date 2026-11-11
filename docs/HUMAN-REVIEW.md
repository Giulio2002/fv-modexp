# What a human must review to trust the result

The kernel checks the proofs; it cannot check that the *statements* mean what you intend. Review, in this order.

## 1. The specification

### 1a. The reference: EthLib (not ours, not editable)

The MODEXP semantics is `EthLib.Execution.Evm.Precompiles.Modexp` from the pinned package `ethlibspec` (github.com/Giulio2002/EthLib branch
`modexp-spec-lean-v4.34.1` @ `f4756ef5`, a byte-identical copy of ethereum/EthLib@ffd60c4b, see its UPSTREAM.md): `parseLengths`, `checkLengths`, `requiredGas`,
`compute`, `chargedGas`, `modexp`. This project never edits or re-defines it. Read it: it is the specification being proved.

### 1b. `lean/FvModexp/Spec/` (ours: plain definitions the statements use)

A final statement may not use an instance or class of a dependency, so these plain defs replace instance-based notation.
`scripts/check-spec-closure` enforces: statements depend only on `FvModexp.Spec.*`, Janus, `Extracted`, EthLib, and reach no EthLib instance.

| Definition | Meaning, and why it is what it says |
|---|---|
| `Spec.PostFusaka fork` (`Spec/Fork.lean`) | `Fork.fusaka.ctorIdx ≤ fork.ctorIdx` in plain `Nat` order. EthLib's `Fork` order is `ctorIdx` (`instance : LE Fork := ⟨fun a b => a.ctorIdx ≤ b.ctorIdx⟩`); `postFusaka_iff : PostFusaka fork ↔ Fork.fusaka ≤ fork` (and `postFusaka_iff_ge`) are proved by `Iff.rfl`. geth uses the Osaka set from Osaka on (Bogota/Amsterdam reuse it), hence every fork `.fusaka ≤ fork` is covered. |
| `Spec.byteOf m a` (`Spec/Mem.lean`) | The byte at address `a` of the Janus memory `m`, as `UInt8`. |
| `Spec.bytesAt m p n` | The `n` bytes at address `p` as an EthLib `ByteArray`: `data[i] = byteOf m (p+i)`, `i < n`. A Go `[]byte` `(ptr = p, len = n, cap)` IS this call data (the capacity is irrelevant to MODEXP). `bytesAt_size`, `byteAt_bytesAt` relate it to EthLib's total read `byteAt` (zero past the end, "infinite right padding"). |
| `Spec.LengthsPass data` (`Spec/Modexp.lean`) | `checkLengths (parseLengths data) = Except.ok ()`, i.e. EIP-7823: the three length headers are at most 1024. `lengthsPass_iff` gives the explicit form (proved). `LengthsFail = ¬ LengthsPass`. |
| `Spec.OsakaReceiver m p` | The receiver `*bigModExp` at `p` has `eip2565`, `eip7823`, `eip7883` all `true`: the three bytes at `p`, `p+1`, `p+2` equal 1 (field order of `type bigModExp struct`, `core/vm/contracts.go:419`; Go keeps a `bool` as a byte 0/1). A precondition: the theorem says nothing about other receivers. |
| `Spec.u64 x` | A `uint64` result register read as a natural number. For `RequiredGas` the statement is `u64 result = requiredGas fork data (parseLengths data)` as an equality in `Nat`, so the value fits in 64 bits (the proof shows it; for lengths at most 1024 no saturation to `MaxUint64` occurs). |
| `Spec.Precompile`, `Spec.runPrecompiled` (`Spec/Geth.lean`) | geth's `RunPrecompiledContract` logic (`core/vm/contracts.go:272`): `gasCost := RequiredGas(input)`; `gas < gasCost` -> `ErrOutOfGas`; else charge and `Run`; an error from `Run` is passed up. `none` = failed call (the EVM caller then consumes all gas), `some (out, remaining)` = success. Cache and logger paths are not modelled (`cache = nil`, `logger = nil`). |

## 2. The main theorem statements

* Row 2 `FvModexp.<Arm64|Amd64>.RequiredGas.correctness` (`Proofs/<ISA>/RequiredGas*.lean`): for every receiver with `OsakaReceiver`, every input slice `(ptr, len, cap)` and every `fork` with
  `PostFusaka fork`, if `LengthsPass (bytesAt mem ptr len)` then the call returns normally with `u64 result = requiredGas fork data (parseLengths data)`; otherwise it returns without panic or fault (any value).
  Plus the Go ABI, stack and frame conditions printed by `janus verify`.
* Row 1 `FvModexp.<ISA>.Run.correctness` (agent `top`): see its module header.
* Row 3 `FvModexp.Proofs.Compose.composition` (`Proofs/Common/Compose.lean`): pure Lean. From the guarantees of rows 1 and 2 (hypothesis structure `RowsHold`), geth's `runPrecompiled` agrees with EthLib's
  `modexp fork data gas`: failure iff failure (error length bound, or out of gas), otherwise equal outputs and remaining gas `gas - cost` with `cost` = EthLib's `chargedGas`.

## 3. Assumptions and limits

* **Toolchain gap.** The binary under verification is built with Go 1.26.10 (Janus-pinned: `GOTOOLCHAIN=go1.26.10`, `CGO_ENABLED=0`, `GOAMD64=v1`, `-trimpath -buildvcs=false`, `scripts/harness.sha256`), because Janus v0.2.0's runtime pins do not
  cover Go 1.27.3, which geth's own release binaries use. geth v1.17.10 itself satisfies the module's `go` directive with 1.26. Verified code = geth v1.17.10 source compiled with 1.26.10, not the shipped release binary. amd64 is verified at `GOAMD64=v1` only.
* **EthLib pin.** The spec is the pinned EthLib revision; if upstream changes the MODEXP spec after `ffd60c4b`, nothing here follows.
* **Runtime contracts** (Janus-pinned, per row in `scripts/contract-flags.sh`): none for RequiredGas.
* Single-threaded execution, non-moving heap, the Go ABI, the harness binary (Janus assumptions, SOUNDNESS.md).
* Modeled `RunPrecompiledContract` is abstract (row 3); the stretch goal of verifying its machine code is not part of the claimed result.

## 4. Non-vacuity

Every main theorem has a kernel-checked `Witness.nonvacuous` (concrete returning run satisfying the precondition) which `janus verify` requires.

## Row 1 runtime assumptions: `RunIface.Serves R` and non-vacuity (agent top, DRAFT 2026-11-11)

`Serves R` (lean/FvModexp/Proofs/Arm64/Top/RunIface.lean) says the runtime serves every request of the Run extraction's
contracts up to: `makeslice` cap ≤ 2^17 elements, `memmove`/`memclrNoHeapPointers` ≤ 2^20 bytes, `growslice` new length
≤ 2^17; `newobject`, write barriers, `sync.Pool` Get/Put unconstrained (no size argument). An unbounded version is not
satisfiable by any Janus stub runtime (the stubs serve fixed / ≤ N sizes) and is not what a real runtime does (huge
requests throw `out of memory`), so it was rejected.

**Request sizes Run can make** (EIP-7823: each operand ≤ 1024 bytes = 128 words; `m` = len(modulus) ≤ 128 words). From the
go-bigmodexpfix code (to be confirmed by the `R.ok` needs of divmc's/expmc's summaries; this table is the review target):

| request | site | worst case |
|---|---|---|
| `make([]byte, n)` | `getData` (Run), `LeftPadBytes` (Run), `(*Int).Bytes` | 1024 B (Bytes: `8·len(abs)` ≤ 1032 B) |
| `nat.make(n)` = `makeslice(Word, n, n+4)` | setBytes (≤ 128), mul/sqr `z.make(len x + len y)` (≤ 256), div `u.make(len+1)`, `q.make(m-n+1)`, Montgomery `zz.make(2m)`, power table 16 × m | ≤ 260 words |
| `(*stack).nat(n)` → `growslice` of the pooled `[]Word` | karatsuba/karatsubaSqr scratch (≈ 3·n·log n words for n ≤ 256), divRecursive scratch | ≤ ~ 10 000 words (estimate) |
| `memmove` | getData/LeftPad copies (≤ 1024 B), `nat.set` / `copy` of nats (≤ 260 words ≈ 2 KiB) | ≤ 2 KiB (stack scratch copies ≤ ~80 KiB) |
| `memclrNoHeapPointers` | `clear(z)` of scratch nats | ≤ ~80 KiB |

The bounds 2^17 elements (1 MiB of words) and 2^20 bytes leave ≥ 10× margin over these estimates.

**Non-vacuity plan (coordinator requirement, open):**
1. `correctness` (full row-1 statement) — `Witness.nonvacuous` runs the EIP-7823 error path (no `Serves` needed there).
2. `correctness_ok` (same statement restricted to `LengthsPass data`, `Serves R` in its precondition) — `Witness.correctness_ok`
   runs a small success input (base 3, exp 5, mod 7 → `0x05`) to the return. Its runtime must satisfy the bounded `Serves R`:
   this needs witness stubs that serve EVERY size up to the bound (a looping `memmove`/`memclr`, a general `growslice`,
   bump `makeslice` for any cap ≤ 2^17, `Pool.Get` returning nil, `Pool.Put` dropping), proved against the live contracts —
   Janus' stub library only has fixed-size / ≤N-size copies. Work item for top (or infra), tracked in NOTES-top.md.
3. Satisfiability of `Serves R` for the worst case (requirement (a)) follows from 2's stubs: they serve every request up to the
   bounds, sized with a heap ≥ the Run budget.
