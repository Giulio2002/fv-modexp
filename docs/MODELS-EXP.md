# Nat-level exponentiation models (agent mathexp)

Namespace `FvModexp.Exp`, files `lean/FvModexp/Proofs/Common/Exp*.lean`. Source cited as
`nat.go` / `int.go` = github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/,
`contracts.go` = github.com/ethereum/go-ethereum@v1.17.10/core/vm/contracts.go.
Value convention and the Nat meaning of every sub-call (mul/sqr/div/rem/add/sub/trunc/lsh/rsh/cmp): /srv/fv-modexp-ops/NOTES-models.md.
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

## Reachability of ModInverse / GCD (verdict: UNREACHABLE from Run)
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
  that is the multiplication layer (mathdiv), not this one.

## Differential test against the real Go code
`scripts/exp-difftest/run.sh` copies go-bigmodexpfix f9e208c548ab from GOMODCACHE, exports the unexported functions
(`fvexport.go.txt`), runs `main.go` on random inputs (fixed seed) and checks the outputs with `#guard`s on the Lean
models (`lean/tests/ExpDiff.lean`, 508 guards: montgomery, computeMontgomeryk0, modularInverseModPowerOfTwo,
subMod2N, expNNOddMontgomeryWindowSize{2,4}, expNNPowerOfTwo, expNNSlow incl. m = 0, expNNEven, expNN). All pass.
This is a sanity check for the transcriptions, not part of the proof.
