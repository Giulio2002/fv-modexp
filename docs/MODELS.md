# Go-level models

The machine-code theorems are stated against the EthLib specification, but their proofs go through **Nat-level models**:
faithful transcriptions of the Go source (each cites `file:line`) into Lean functions on `Nat` and `List Nat`, each proved
equal to the mathematical function it computes. This page indexes them, the no-panic facts they establish, and the
preconditions of the assembly leaf routines. None of this is in a final statement; it is what a reviewer reads to see how
the proofs connect the machine code to the specification.

1. [Multiplication and division layer](#multiplication-and-division-layer)
2. [Exponentiation layer](#exponentiation-layer)
3. [Assembly leaf routines](#assembly-leaf-routines)

## Multiplication and division layer

Namespace `FvModexp.Mdl`, files `lean/FvModexp/Proofs/Common/*.lean` (proof-only, pure core Lean, no Mathlib).
Source cited as `arith.go` / `nat.go` / `natmul.go` / `natdiv.go` / `int.go` =
github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/ (line numbers of that copy);
`std nat.go` = Go 1.26.10 `src/math/big/nat.go` (geth's `big.Int.SetBytes/Uint64/BitLen` on the header lengths).
No `sorry`; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

### Conventions
* A Go `nat` / `[]Word` is a `List Nat`, least-significant limb first; `Wd l` = every limb `< 2^64`; `val l` its value;
  `norm` = `nat.norm` (drop most-significant zero limbs), `Normed l` = `norm l = l`. uint64 wrap-around is `% 2^64`.
* Byte buffers are `List Nat` in Go index order, `Bt` = all `< 256`, `beVal` = big-endian value.
* A function that writes slices returns the FINAL CONTENTS of each written slice (same length) plus its Go results.
  In-place stores into a sub-slice: `upd z i l`; sub-slice reads: `sl z i n = z[i:i+n]`.
* `z.make(n)` (nat.go:57): the models take no `z`; every caller overwrites (or clears) all `n` limbs before reading, so the
  result does not depend on the old contents. Whether the result reuses `z`'s backing array (`n <= cap(z)`) is a memory-model
  fact for the machine-code proofs.
* Panics are not modelled: theorems carry the no-panic preconditions, and every no-panic side condition a CALLER relies on
  (slice bounds, `panic("impossible")`, `addTo` length, dropped carries, quotient-digit stores) is proved where the Go caller
  guarantees it.
* Mutually recursive code (`nat.mul` <-> `karatsuba` <-> `Int.mul`; `divRecursiveStep` -> itself / `divBasic` / `nat.mul`;
  `divLarge` -> `divRecursive`) is modelled with the callee as a FUNCTION PARAMETER plus its value contract
  (`DivContract.lean`: `MulContract`, `DivBasicContract`, `DivRecursiveContract`) — exactly the shape in which the
  machine-code proofs compose per-function summaries — and closed versions (`natMul`, `natSqr`, ...) are built on top.
* Vector primitives `addVV/subVV/lshVU/rshVU/mulAddVWW/addMulVVWW` are ASSEMBLY on both ISAs (arith_{arm64,amd64}.s,
  `.abi0`); their models are the `_g` reference loops of arith.go, i.e. the functional spec the assembly must meet.
  Elementwise ops read `x[i]`,`y[i]` before writing `z[i]`, so the results are valid for `z == x` exactly (same base).

### Index: Go function → model → theorem

#### Words, vectors (Words, Div64Math, DivWW, WordFacts, VecOps)
| Go (file:line) | model | theorem |
|---|---|---|
| `mulWW` arith.go:43 / `bits.Mul64` | `mulWW` | `mulWW_spec` |
| `mulAddWWW_g` arith.go:49 | `mulAddWWW` | `mulAddWWW_spec` |
| `nlz` arith.go:58 (`bits.LeadingZeros64`) | `nlz` | `nlz_spec` |
| `bits.Div64` (go1.26.10 math/bits, software path used on arm64; DIVQ on amd64) | `div64`, `d64loop` | `div64_spec`, `d64loop_spec` (math: Div64Math, adapted from fv-uint256) |
| `divWW` arith.go:273 | `divWW`, `qguess`, `divWWfix`, `divWWn` | `divWW_spec` |
| `reciprocalWord` arith.go:333 | `reciprocalWord` | `reciprocalWord_spec`, `reciprocalWord_eq_div64` (= `bits.Div(^u, _M, u)` quotient) |
| `addVV` arith.go:63 / `subVV` arith.go:77 | `addVV`/`addVVc`, `subVV`/`subVVc` | `addVVc_spec`, `subVVc_spec` |
| `addVW` arith.go:103 / `subVW` arith.go:157 | `addVW`/`incCarry`, `subVW`/`decCarry` | `addVW_spec`, `subVW_spec` |
| `lshVU` arith.go:198 / `rshVU` arith.go:221 | `lshVU`/`lshVUz`, `rshVU`/`rshVUz` | `lshVU_spec`, `rshVU_spec` |
| `mulAddVWW` arith.go:244 / `addMulVVWW` arith.go:255 | `mulAddVWW`, `addMulVVWW` | `mulAddVWW_spec`, `addMulVVWW_spec` |

#### nat basics (NatBasic, BytesNat, BitsNat, WordFacts)
| Go (file:line) | model | theorem |
|---|---|---|
| `nat.norm` nat.go:49 | `norm` | `val_norm`, `normed_norm`, `norm_eq_take`, `Normed.val_ge`, `length_le_of_val_lt` |
| `nat.cmp` nat.go:152 | `natCmp` (`cmpRev`) | `natCmp_spec` (normalised operands) |
| `setWord` nat.go:71 / `setUint64` nat.go:80 | `natSetWord`, `natSetUint64` | `natSetWord_spec`, `natSetUint64_spec` |
| `nat.add` nat.go:98 / `nat.sub` nat.go:124 | `natAdd`/`natAddO`, `natSub`/`natSubO` | `natAdd_spec`, `natSub_spec` |
| `addTo` nat.go:234 | `addTo` | `addTo_spec` |
| `nat.lsh` nat.go:395 / `nat.rsh` nat.go:425 / `nat.trunc` nat.go:530 | `natLsh`, `natRsh`, `natTrunc` | `natLsh_spec`, `natRsh_spec`, `natTrunc_spec` |
| `nat.setBytes` nat.go:1665 (= std nat.go:1022) | `natSetBytes`, `sbWords`, `sbTail`, `bigEndianWord` | `natSetBytes_spec` (`val = beVal buf`, Normed, len ≤ ⌈len/8⌉) |
| `nat.bytes` nat.go:1628 | `natBytes`, `bytesLoop`, `bytesWord`, `lzBytes` | `bytesWord_spec`, `bytesLoop_spec`, `natBytes_exact` |
| `(*Int).Bytes` int.go:527 | `intBytes` | `intBytes_spec` (minimal big-endian encoding: `beVal = val`, no leading 0 byte) |
| `nat.bitLen` nat.go:342 (= std nat.go:332), `(*Int).BitLen` int.go:548 | `natBitLen`, `smear`, `bitsLen` | `natBitLen_spec` (= `bitsLen (val x)` = `log2 + 1`), `bitsLen_spec`, `smear_log2` |
| `low64` int.go:416, `(*Int).Uint64` int.go:439 | `low64` | `low64_spec`, `low64_eq_val` |
| `(*Int).IsUint64` int.go:453 | `isUint64` | `length_le_one_iff` |
| `(*Int).SetBytes` int.go:518 | `intSetBytes` | `intSetBytes_spec` |
| `(*stack).nat` nat.go:319 (`nr := (n+3) &^ 3`) | `stackRound` | `stackRound_eq`, `stackRound_bounds` |

#### Int (IntOps, IntDiv)
| Go (file:line) | model | theorem |
|---|---|---|
| `Int{neg, abs}` int.go:33 | `GInt`, `GInt.ival`, `Ok`, `Canon`, `mkInt` | `mkInt_canon`, `mkInt_ival` |
| `(*Int).Add` int.go:141 / `Sub` int.go:162 | `intAdd`, `intSub` | `intAdd_spec`, `intSub_spec` (accept denormalised `-0`) |
| `(*Int).Cmp` int.go:378 | `intCmp` (`same` flag = `x == y`) | `intCmp_spec` |
| `(*Int).mul` int.go:191 (`x == y` → sqr) | `intMul` | `intMul_spec`, `intMul_ne_spec` |
| `Neg`/`Sign`/`Set`/`SetUint64`/`SetInt64` int.go:134/44/95/70/58 | `intNeg`, `intSign`, `intSet`, `intSetUint64`, `intSetInt64` | `*_spec` |
| `(*Int).QuoRem` int.go:299 | `intQuoRem` | `intQuoRem_spec` (`Int.tdiv`, `Int.tmod`) |
| `(*Int).Div` int.go:308 | `intDiv` | `intDiv_spec` (Euclidean `/`) |
| `(*Int).Mod` int.go:325 (incl. `z == y` alias copy) | `intMod` | `intMod_spec` (Euclidean `%`) |

#### Multiplication (NatMul1, MulSqr, Karatsuba, KaratsubaSqr, MulClosed)
| Go (file:line) | model | theorem |
|---|---|---|
| `basicMul` natmul.go:151 | `basicMul`, `basicMulLoop` | `basicMul_spec` |
| `nat.mulAddWW` natmul.go:136 | `natMulAddWW` | `natMulAddWW_spec` |
| `nat.mul` natmul.go:16 (parametric: `kar`, `mulRec`) | `natMulM`, `natMulS`, `mulChunks` | `natMulM_spec'`, `natMulS_spec'`, `mulChunks_spec'` (restricted contracts `MulContractLt`) |
| `basicSqr` natmul.go:113 | `basicSqr`, `basicSqrLoop`, `addMulStep` | `basicSqr_spec` |
| `nat.sqr` natmul.go:73 (parametric) | `natSqrP` | `natSqrP_spec`, `natSqrP_at` |
| `karatsuba` natmul.go:164 | `karatsuba mul` (`kTx kTy kZ1m kZ0 kZ2 kZ1a kZ1b kZ`) | `karatsuba_spec`, `karatsuba_facts` (no-panic/storage facts) |
| `karatsubaSqr` natmul.go:257 | `karatsubaSqr sqr` (`ksTx ksZ1m ksZ0 ksZ2 ksZ1a ksZ1b`) | `karatsubaSqr_spec`, `karatsubaSqr_facts` |
| `nat.mul` / `nat.sqr` closed | `natMul`, `natSqr` (`natMulF`, `natSqrF` fuel) | `natMul_spec : MulContract natMul`, `natSqr_spec`, `natMulF_stable` |
| closed kernels | `karatsubaC`, `karatsubaSqrC` | `karatsubaC_spec`, `karatsubaSqrC_spec` |

#### Division (DivW, DivBasic*, DivLarge, NatDiv, DivRec*)
| Go (file:line) | model | theorem |
|---|---|---|
| `divWVW` natdiv.go:579 | `divWVW`, `divWVWLoop` | `divWVWLoop_spec`, `divWVW_spec` (incl. `len(x)==1` `bits.Div` branch) |
| `nat.divW` natdiv.go:550 / `modW` natdiv.go:570 | `natDivW`, `natModW` | `natDivW_spec`, `natModW_spec` |
| `divBasic` natdiv.go:646 (Knuth D) | `divBasic`, `dbLoop`, `dbStep`, `qhatEst`, `corrLoop`, `greaterThan`, `dbFix`, `dbSubAdd` | `divBasic_contract : DivBasicContract divBasic`, `qhatEst_spec`, `dbStep_inv` |
| `divLarge` natdiv.go:597 (parametric in `divRecursive`) | `divLarge dr qs uIn vIn` | `divLarge_spec` |
| `nat.div` natdiv.go:518 / `nat.rem` natdiv.go:505 | `natDiv dr qs u v`, `natRem dr qs u v` | `natDiv_spec`, `natRem_spec` |
| `divRecursive` natdiv.go:740 / `divRecursiveStep` natdiv.go:750 (parametric: `db`, `mul`) | `divRecursive db mul`, `drs` (fuel = `len v + 1`), `drsLoop`, `blockStep`, `blockM`, `finalBlock`, `refMid`, `corr1`, `corr2`, `corrSub`, `subToC` | `divRecursive_contract : DivBasicContract db → MulContract mul → DivRecursiveContract (divRecursive db mul)`, `drs_spec`, `drsLoop_spec`, `blockStep_spec`, `finalBlock_spec`, `refMid_spec`; math `gg_lower`/`gg_upper` (DivRecMath), `natCmp_stale` (DivRecAux) |
| closed division | `divRecursiveC`, `natDivC`, `natRemC`, `intQuoRemC`, `intDivC`, `intModC` (DivClosed) | `divRecursiveC_contract`, `natDivC_spec`, `natRemC_spec`, `intQuoRemC_spec`, `intDivC_spec`, `intModC_spec` |

### No-panic facts proved (for the machine-code proofs)
* divBasic: Knuth bound `X/D ≤ q̂ ≤ X/D + 1` after the correction loop (incl. `rhat` overflow break, `qhat = _M` case);
  when `j+qhl > len(u)` (only `j = m`) `qhatv[n] = 0` so `u[j:j+qhl]` is in bounds; the `q[j]` store is in bounds (the skipped
  `j = m = len(q)` digit is 0); at most one add-back.
* divRecursiveStep: both `panic("impossible")` checks and the final `c > 0` panic are unreachable; `qhat0.length + s ≤ 3n`
  (qhatv capacity); `addTo(z[j-B:], qhat)`, `addTo(uu[s:], v[s:])`, `addTo(z, qhat.norm())` have `len(x) ≤ len(z)` and drop
  no carry; `uu[s:B+n]` in bounds; the in-place remainder of the recursive call is what the caller reads back.
  `cmp` on the NON-renormalised `qhatv` (after an in-place correction) still decides correctly (`natCmp_stale`:
  `len(qhatv) ≤ len(uu.norm())`).
* karatsuba / karatsubaSqr: `tx`,`ty` fit `n2` limbs (storage `z[0:n2]`, `z[n2:2n2]`); `z0`, `z2` products fit
  `z[0:2n2]`, `z[2n2:]`; `z1` fits `stk.nat(2n2+1)` after each `Add`; final `z1 ≥ 0`, `len(z1.abs) ≤ len(z[n2:])`; `addTo`
  drops no carry.
* divLarge: preconditions of divBasic / divRecursive hold (incl. top limb of the shifted `u` `< 2^63`).

### Contract strengthening (not a Go bug)
`DivRecursiveContract` requires `2 * val u < 2^(64 len u)` (top limb `< 2^63`). Without it, `divRecursive` called on
`u = v·2^(64·30) - 1`, `len v = 40`, `len q = 30` gives `len(qhat.norm()) = len(z[j-B:]) + 1` in the first step and
`addTo(z[j-B:], qhat)` would slice out of bounds. `divLarge` (the only caller) always satisfies the bound
(`u[len(uIn)]` = bits shifted out by `shift ≤ 63`); proved in `divLarge_spec`.

### Obligations left to the machine-code layer (memory facts not expressible on values)
* `nat.mul` writes only `z[:len x + len y]` of the `3n`-limb `qhatv = stk.nat(3n)` buffer (divRecursiveStep models
  `qhatv` as the zero-padded product).
* `z.make(n)` reuse vs allocation (`n ≤ cap(z)`), `alias(z, x)` checks, `stk.nat` capacities (`cap = n`, `stackRound`),
  and that `divLarge`'s `u` may share storage with `uIn` exactly (lshVU in place, top-down, is safe).

### Differential test (sanity, not proof)
`scripts/muldiv-difftest/run.sh` (needs `go` 1.26.10 on PATH): copies go-bigmodexpfix f9e208c548ab, exports internals
(`fvexport.go.txt`), runs random/edge inputs and checks the Lean models with `#guard` (`lean/tests/MulDivDiff.lean`,
487 guards, all pass): `natSetBytes`, `intBytes`, `natBitLen`, `natMul` (sizes 0..97 × 1..80), `natSqr`, `basicSqr`,
`karatsubaC`, `karatsubaSqrC` (to 97 limbs), `divBasic` (final `q` AND in-place `u`), `divRecursiveC` (n = 40..99, final
`q` and `u`), `natDivC` (all regimes).

## Exponentiation layer

Namespace `FvModexp.Exp`, files `lean/FvModexp/Proofs/Common/Exp*.lean`. Source cited as
`nat.go` / `int.go` = github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/,
`contracts.go` = github.com/ethereum/go-ethereum@v1.17.10/core/vm/contracts.go.
Value conventions as in the multiplication and division layer above.
No `sorry`, no axioms beyond `propext`/`Classical.choice`/`Quot.sound`.

| Go function (file:line) | Lean model | Correctness theorem | File |
|---|---|---|---|
| windowed-loop skeleton shared by expNNSlow / expNNOddMontgomeryWindowSize{2,4} / expNNPowerOfTwoWindowSize{2,4} | `wordLoop`, `outerLoop`, `winRun` | `wordLoop_rep`, `outerLoop_rep`, `winRun_rep` (generic `StepOk` invariant) | ExpWindow |
| `computeMontgomeryk0` nat.go:1271 | `montK0`, `newton`, `newtonLoop` | `montK0_spec : (k0*m0 + 1) % 2^64 = 0`, `newtonLoop_spec` | ExpMont |
| `nat.montgomery` nat.go:188 | `montgomery`, `montStep`, `montIter` | `montgomery_spec` (AMM: `T*B^n = x*y + Q*m`, result `T` or `T-m`, `< B^n`) | ExpMont |
| `nat.expNNOdd` nat.go:1343 | `expNNOdd` | `expNNOdd_correct` | ExpOdd |
| `expNNOddMontgomeryWindowSize4/2` nat.go:1363 / 1496 | `expNNOddMont 4/2`, `montPow` | `expNNOddMont_correct`, `mont_rep`, `mont_mul_rep` | ExpOdd |
| `buildPrecomputationWindowModPower2` nat.go:856 | `p2Pow` | `p2Pow_rep` | ExpPow2 |
| `expNNPowerOfTwoWindowSize4/2` nat.go:975 / 1129 | `p2win 4/2`, `skipZero` | `p2win_correct` (uses `pow_mod_phi`: odd `x`, exponent mod 2^(L-1)) | ExpPow2 |
| `nat.expNNPowerOfTwo` nat.go:906 | `expNNPowerOfTwo f` (f = recursion budget; Go recurses once, odd base) | `expNNPowerOfTwo_correct` (f ≥ 2) | ExpPow2 |
| `nat.expNNSlow` nat.go:732 | `expNNSlow` | `expNNSlow_correct` (`m = 0` → `x^y`, else `x^y % m`) | ExpSlow |
| `nat.subMod2N` nat.go:1726 | `subMod2N` | `subMod2N_spec` (`< 2^n`, `(r + y) ≡ x mod 2^n`) | ExpEven |
| `nat.modularInverseModPowerOfTwo` nat.go:1287 | `modularInverseModPowerOfTwo`, `henselLoop` | `modularInverseModPowerOfTwo_spec` (`x*r ≡ 1 mod 2^n`), `hensel_step` | ExpEven |
| `nat.expNNEven` nat.go:801 | `expNNEven rec` | `expNNEven_correct` (CRT, `crt_unique`) | ExpEven |
| `nat.expNN` nat.go:639 | `expNN f` (use f = 2) | `expNN_correct : 0 < m → m < 2^(2^64) → expNN 2 x y m slow = x^y % m` | ExpNN |
| `(*Int).Exp` / `(*Int).exp` int.go:567 / 575 | `intExpPub`, `intExp`, `GoInt` | `intExp_correct` (non-negative operands, `m > 0`) | ExpNN |
| `(*Int).Mod` (+ `QuoRem`) int.go:325 / 299 | `intMod` | `intMod_nonneg`, `bitLen_one_mod` (geth's `base.BitLen()==1` path is `b^e % m`) | ExpNN |
| geth `bigModExp.Run` switch, contracts.go:684-693 | `runValue` | `runValue_eq_spec : runValue b e m = if m = 0 then 0 else EthLib.Execution.Evm.powMod b e m` | ExpNN |
| EthLib `EthLib.Execution.Evm.powMod` (pinned ethlibspec, PowMod.lean:34) | — | `powMod_eq : powMod b e m = b ^ e % m` (all `m`) | ExpNN |
| byte bound | — | `lt_two_pow_B_of_bytes` (≤ 2^57 bytes ⇒ `m < 2^(2^64)`; geth ≤ 1024 bytes) | ExpNN |

Spec-level helpers (math meaning of tiny word loops, ExpBase): `nlen` (`len`), `wd` (`x[i]`), `bitLen` (nat.go:340),
`tz` (`trailingZeroBits`, nat.go:364), `isPow2` (nat.go:379), `nlzW` (`nlz`, arith.go:58).

### Reachability of ModInverse / GCD (verdict: UNREACHABLE from Run)
* The only call of `(*Int).ModInverse` in the reached set is int.go:583, inside `if y.neg { … }` of `(*Int).exp`
  (`nat.modInverse` int.go:918 is not in the extracted set). `(*Int).GCD` is called only from `ModInverse` (int.go:901);
  `lehmerGCD` only from `GCD` (int.go:649); `lehmerSimulate`/`lehmerUpdate`/`euclidUpdate` only from `lehmerGCD`;
  `(*Int).Div` (int.go:855) and the `SetInt64` calls (int.go:580, 769) only on those paths too.
* geth builds `exp` with `new(patched_big.Int).SetBytes(…)` (contracts.go:680), and `SetBytes` sets `z.neg = false`
  (int.go:518-521), so `y.neg = false` and the branch is never taken. Nat-level statement:
  `intExp_modInverse_irrelevant` (result independent of `ModInverse` when `y.neg = false`).
  The machine-code proofs must establish the same path condition (the `neg` byte of the exponent `Int` is 0 at
  the `if y.neg` test of `(*Int).exp`), after which ModInverse/GCD/lehmer*/euclidUpdate need no model.
* Also unreachable with non-negative operands: the sign fix-up in `exp` (`z.neg` ⇒ `z.abs.sub(mWords, z.abs)`,
  int.go:599-603) since `x.neg = false`, and the `z.Add/z.Sub` in `(*Int).Mod` (int.go:332-337) since `x.neg = false`.
  NOTE: `(*Int).Add`/`Sub`/`mul` ARE reachable — via `karatsuba` (natmul.go:207-216) and `karatsubaSqr` (natmul.go:295-303) —
  that is the multiplication layer, not this one.

### Differential test against the real Go code
`scripts/exp-difftest/run.sh` copies go-bigmodexpfix f9e208c548ab from GOMODCACHE, exports the unexported functions
(`fvexport.go.txt`), runs `main.go` on random inputs (fixed seed) and checks the outputs with `#guard`s on the Lean
models (`lean/tests/ExpDiff.lean`, 508 guards: montgomery, computeMontgomeryk0, modularInverseModPowerOfTwo,
subMod2N, expNNOddMontgomeryWindowSize{2,4}, expNNPowerOfTwo, expNNSlow incl. m = 0, expNNEven, expNN). All pass.
This is a sanity check for the transcriptions, not part of the proof.

## Assembly leaf routines

The vector kernels `addVV`, `subVV`, `mulAddVWW`, `addMulVVWW`, `lshVU`, `rshVU` are Go assembly (`arith_arm64.s`,
`arith_amd64.s`, ABI0) on both ISAs; `nat.cmp`, `divWW` and, on arm64, `bits.Div64` and `reciprocalWord` are compiled Go.
Each has a machine-code summary proved once and used by every caller. These routines are verified as part of the release rows on
the Run extraction (table "Assembly leaf routines" in [`COVERAGE.md`](COVERAGE.md)).

### How the summaries are used

* Every summary is proved once on an **Extracted-free library program** `FvModexp.Lib.<Name>.program`
  (`lean/FvModexp/Proofs/Lib/`, generated by `scripts/gen-libprog.py` from `janus extract` of the **pinned harness**,
  `scripts/harness.sha256`): the same bytes at the same absolute addresses as in the extraction of `Run`. A caller
  (e.g. the `Run` row) moves it to its own `Extracted.program` with `Janus.Contracts.EqHashModel.Summary.of_codeIn`
  (arm64) / `Summary.of_codeIn64` (amd64) (fv-uint256 `CodeIn.lean` pattern) and uses it with `janus_run calls [...]`.
* Assembly kernels (`*.abi0`) are `GoABI0.Summary0 program entry Pre Q`: arguments are read from the caller's frame,
  `Q s m` states the memory after the call (result words included) relative to the call state `s`.
  Go (ABIInternal) leaves are `Summary program entry Pre Post` with `Post` either an explicit `s' = { s with regs := … }`
  (cmp) or equations on the result registers (Div64, divWW).
* Values: `FvModexp.Asm.lv m p n = m.readLE p (8 n) = Σ_{i<n} limb_i·2^(64 i)` (model independent). Row statements use
  `readLE` directly (Janus vocabulary only).
* **Model bridge** (`Common/AsmModel.lean`): `limbs m p n : List Nat` (the slice as a model `nat`), `val_limbs`,
  `Wd_limbs`, `eq_of_val`, and `addVV_model`, `subVV_model`, `mulAddVWW_model`, `addMulVVWW_model`, `cmp_model`
  (result word `= BitVec.ofInt 64 (Mdl.natCmp x y)`): the value-level postconditions imply
  `limbs m' z n = (Mdl.<op> (limbs m x n) …).1` and the carry/borrow `= (…).2`. Summary-level model forms:
  `Arm64/AsmModels.lean` (`addVV_summary_model`, `subVV_summary_model`, `cmp_res_model`), `Amd64/AsmModels.lean`.

### Preconditions and the real call sites (go-bigmodexpfix f9e208c548ab, `src/math/big`)

Aliasing: every slice summary allows `z` **equal to or disjoint from** each input slice (`z = x ∨ Apart z (8n) x (8n)`),
which covers every call site below (in-place calls pass the same base; all others pass separately allocated slices).
Every summary also needs `z[0:n]` disjoint from the result word (amd64: from the whole call frame incl. the return
address), which holds for every Go caller (the frame is the caller's outgoing-argument area).

| routine | call site | aliasing at the call |
|---|---|---|
| addVV | nat.go:115 `nat.add` `addVV(z[:n], x[:n], y[:n])` | `z` = `z.make` (same base as `x` or `y` when reused) or fresh |
| addVV | nat.go:236 `addTo` `addVV(z[:n], z[:n], x[:n])` | `z = x`, `y` disjoint |
| addVV | natdiv.go:704 `addVV(u[j:j+n], u[j:j+n], v)` | `z = x`, `y` disjoint |
| subVV | nat.go:141 `nat.sub` | as `nat.add` |
| subVV | nat.go:214 montgomery `subVV(z[:n], z[n:], m)` | `z[:n]`, `z[n:2n]` adjacent (disjoint), `m` disjoint |
| subVV | natdiv.go:702, 838, 847, 872, 882 | `z = x` (same sub-slice), `y` disjoint |
| mulAddVWW | natmul.go:144 `nat.mulAddWW` | `z` fresh/`make`, disjoint or equal |
| mulAddVWW | natdiv.go:693 `mulAddVWW(qhatv[0:n], v, qhat, 0)` | disjoint |
| mulAddVWW | natconv.go:533 `mulAddVWW(larger, larger, b, 0)` | `z = x` (not reachable from Run) |
| addMulVVWW | natmul.go:129 basicSqr, natmul.go:155 basicMul, nat.go:201/203 montgomery | `z = x`, `y` disjoint |
| lshVU | nat.go:417 `nat.lsh` `lshVU(z[n-m:n], x, s)`; natdiv.go:614-615 divLarge; natmul.go:131 | backward loop: summary allows `x ≤ z` or disjoint |
| rshVU | nat.go:446 `nat.rsh` `rshVU(z, x[m-n:], s)`; natdiv.go:636 `rshVU(u, u, shift)` | forward loop: summary allows `z ≤ x` or disjoint |
| nat.cmp | everywhere (`x.cmp(y)`) | read-only; slices may be empty (`len = 0`, any pointer, e.g. nil) |

Other preconditions: lengths are those of `z` (`len(x), len(y) ≥ len(z)` at every call site); the `n` limbs of each
slice must be readable / writable (`Ptr`). For `n = 0` the kernels read nothing but the summaries still ask the
(zero-length) ranges to lie in a region; `nat.cmp` asks nothing of an empty slice. Shift counts: every reachable call
passes `1 ≤ s ≤ 63`.
`nat.cmp` compares **lengths first** (as Go does); it is the value comparison only for normalized inputs
(`cmp_model` + `Mdl.natCmp_spec`).
`Div64` (arm64): `y ≠ 0`, `hi < y`, `GuardOK s 0`, `StackOK s 40 0`. `divWW` (arm64): `y ≠ 0`, `x1 < y`,
`m = reciprocal of y` (as `reciprocalWord` computes), frameless. `divWW` (amd64): the same, args `RAX, RBX, RCX, RDI`,
results `RAX, RBX`; Pre adds the return slot `[RSP]` readable with value `< 2^47`; Post = `Amd64.DivWWSum.Post`
(rip = return address, `RSP + 8`, results, registers outside `RAX..RDX, RSI, RDI, R8..R11` kept, memory, `X15`, FS, DF).

### amd64 `addMulVVWW`: how both paths are covered

`CMPB ·hasADX(SB), $0; JNZ altcarry` reads a runtime global (CPUID-dependent). The summary's precondition only asks the
byte to be readable; `main_lem` runs both branches. MULQ path: 1x loop (`one_lem`) and 4x block (`blk_lem`, executed
limb by limb through the segment lemmas `segM0..3`, which keep the symbolic state small). ADX path: 1x loop
(`aone_lem`), 8x block (`ablock`: four pair-segment lemmas `segA0..3` carrying `RBX` and the `CF`/`OF` chains as one
carry word `W = RBX + CF + OF`, `ablkval` bounds `W < 2^64`), loop `ablk_lem`.

#### `hasADX` at the real call sites
The amd64 `addMulVVWW` summary needs the byte `math/big.hasADX` (`.noptrbss`, `Extracted.dataAddr.«…hasADX»` =
`0xbb6b8a` in the pinned harness) to be readable; any value. In the running process the byte is part of the binary's
mapped `.noptrbss` segment (written once by the package initializer from CPUID), so a caller's precondition provides it
like the other writable globals (see "Writable globals" in DEVELOPMENT.md): the region holding `0xbb6b8a` readable and the byte outside `R.rt`
(the summary only reads it, so the fact survives every other call). Callers (basicMul, basicSqr, montgomery) must
carry this fact (`GlobalIs`-style: readable + Outside R.rt) in their `CallEnv` extension; no value is assumed, both
code paths are proved.
