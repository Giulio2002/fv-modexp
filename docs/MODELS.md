# Nat-level models of the multiplication / division layer (agent mathdiv)

Namespace `FvModexp.Mdl`, files `lean/FvModexp/Proofs/Common/*.lean` (proof-only, pure core Lean, no Mathlib).
Source cited as `arith.go` / `nat.go` / `natmul.go` / `natdiv.go` / `int.go` =
github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/ (line numbers of that copy);
`std nat.go` = Go 1.26.10 `src/math/big/nat.go` (geth's `big.Int.SetBytes/Uint64/BitLen` on the header lengths).
No `sorry`; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Conventions
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

## Index: Go function → model → theorem

### Words, vectors (Words, Div64Math, DivWW, WordFacts, VecOps)
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

### nat basics (NatBasic, BytesNat, BitsNat, WordFacts)
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

### Int (IntOps, IntDiv)
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

### Multiplication (NatMul1, MulSqr, Karatsuba, KaratsubaSqr, MulClosed)
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

### Division (DivW, DivBasic*, DivLarge, NatDiv, DivRec*)
| Go (file:line) | model | theorem |
|---|---|---|
| `divWVW` natdiv.go:579 | `divWVW`, `divWVWLoop` | `divWVWLoop_spec`, `divWVW_spec` (incl. `len(x)==1` `bits.Div` branch) |
| `nat.divW` natdiv.go:550 / `modW` natdiv.go:570 | `natDivW`, `natModW` | `natDivW_spec`, `natModW_spec` |
| `divBasic` natdiv.go:646 (Knuth D) | `divBasic`, `dbLoop`, `dbStep`, `qhatEst`, `corrLoop`, `greaterThan`, `dbFix`, `dbSubAdd` | `divBasic_contract : DivBasicContract divBasic`, `qhatEst_spec`, `dbStep_inv` |
| `divLarge` natdiv.go:597 (parametric in `divRecursive`) | `divLarge dr qs uIn vIn` | `divLarge_spec` |
| `nat.div` natdiv.go:518 / `nat.rem` natdiv.go:505 | `natDiv dr qs u v`, `natRem dr qs u v` | `natDiv_spec`, `natRem_spec` |
| `divRecursive` natdiv.go:740 / `divRecursiveStep` natdiv.go:750 (parametric: `db`, `mul`) | `divRecursive db mul`, `drs` (fuel = `len v + 1`), `drsLoop`, `blockStep`, `blockM`, `finalBlock`, `refMid`, `corr1`, `corr2`, `corrSub`, `subToC` | `divRecursive_contract : DivBasicContract db → MulContract mul → DivRecursiveContract (divRecursive db mul)`, `drs_spec`, `drsLoop_spec`, `blockStep_spec`, `finalBlock_spec`, `refMid_spec`; math `gg_lower`/`gg_upper` (DivRecMath), `natCmp_stale` (DivRecAux) |
| closed division | `divRecursiveC`, `natDivC`, `natRemC`, `intQuoRemC`, `intDivC`, `intModC` (DivClosed) | `divRecursiveC_contract`, `natDivC_spec`, `natRemC_spec`, `intQuoRemC_spec`, `intDivC_spec`, `intModC_spec` |

## No-panic facts proved (for the machine-code proofs)
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

## Contract strengthening (not a Go bug)
`DivRecursiveContract` requires `2 * val u < 2^(64 len u)` (top limb `< 2^63`). Without it, `divRecursive` called on
`u = v·2^(64·30) - 1`, `len v = 40`, `len q = 30` gives `len(qhat.norm()) = len(z[j-B:]) + 1` in the first step and
`addTo(z[j-B:], qhat)` would slice out of bounds. `divLarge` (the only caller) always satisfies the bound
(`u[len(uIn)]` = bits shifted out by `shift ≤ 63`); proved in `divLarge_spec`.

## Obligations left to the machine-code layer (memory facts not expressible on values)
* `nat.mul` writes only `z[:len x + len y]` of the `3n`-limb `qhatv = stk.nat(3n)` buffer (divRecursiveStep models
  `qhatv` as the zero-padded product).
* `z.make(n)` reuse vs allocation (`n ≤ cap(z)`), `alias(z, x)` checks, `stk.nat` capacities (`cap = n`, `stackRound`),
  and that `divLarge`'s `u` may share storage with `uIn` exactly (lshVU in place, top-down, is safe).

## Differential test (sanity, not proof)
`scripts/muldiv-difftest/run.sh` (needs `go` 1.26.10 on PATH): copies go-bigmodexpfix f9e208c548ab, exports internals
(`fvexport.go.txt`), runs random/edge inputs and checks the Lean models with `#guard` (`lean/tests/MulDivDiff.lean`,
487 guards, all pass): `natSetBytes`, `intBytes`, `natBitLen`, `natMul` (sizes 0..97 × 1..80), `natSqr`, `basicSqr`,
`karatsubaC`, `karatsubaSqrC` (to 97 limbs), `divBasic` (final `q` AND in-place `u`), `divRecursiveC` (n = 40..99, final
`q` and `u`), `natDivC` (all regimes).
