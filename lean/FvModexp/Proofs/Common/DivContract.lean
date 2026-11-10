import FvModexp.Proofs.Common.Slices
/-!
# Value-level contracts shared by the division models (natdiv.go)

`divLarge` (natdiv.go:597) calls `q.divBasic(stk, u, v)` (natdiv.go:646) or `q.divRecursive(stk, u, v)` (natdiv.go:740), and
`divRecursiveStep` (natdiv.go:750) calls `divBasic` again.  The models of these functions are written in separate modules; a model
that *calls* one of them takes the callee as a function parameter and assumes the callee's contract below (this mirrors how the
machine-code proofs compose per-function summaries).  The concrete models are proved to satisfy the contracts
(`divBasic_contract`, `divRecursive_contract`).

A division routine is modelled as `f q u v = (q', u')`: the final contents of the quotient slice `q` and of the (in-place) dividend
slice `u`; `v` is read only.  `n = len(v)`, `m = len(u) - n`.
-/
namespace FvModexp.Mdl

/-- Top limb of a non-empty limb list (`v[len(v)-1]`). -/
def topLimb (v : List Nat) : Nat := v.getD (v.length - 1) 0

/-- Contract of `(q nat) divBasic(stk, u, v)` (natdiv.go:646-722).
* `u` shorter than `v` (`m < 0`): the `for j := m; j >= 0; j--` loop does not run; nothing is written.
* otherwise the `m+1` quotient digits go to `q[0..m]` (when `len(q) = m` the top digit is provably 0 and is not stored:
  `if j == m && m == len(q) && qhat == 0 { continue }`), the rest of `q` is untouched, and `u` is overwritten with the
  remainder (`u[n:]` all zero). -/
def DivBasicContract (db : List Nat → List Nat → List Nat → List Nat × List Nat) : Prop :=
  ∀ q u v : List Nat, Wd q → Wd u → Wd v → 2 ≤ v.length → 2 ^ 63 ≤ topLimb v →
    (u.length < v.length → db q u v = (q, u)) ∧
    (v.length ≤ u.length →
      (u.length - v.length < q.length ∨
        (u.length - v.length = q.length ∧ val u < val v * 2 ^ (64 * q.length))) →
      (db q u v).1.length = q.length ∧ (db q u v).2.length = u.length ∧
      Wd (db q u v).1 ∧ Wd (db q u v).2 ∧
      val ((db q u v).1.take (u.length - v.length + 1)) = val u / val v ∧
      (db q u v).1.drop (u.length - v.length + 1) = q.drop (u.length - v.length + 1) ∧
      val (db q u v).2 = val u % val v ∧
      (∀ d ∈ (db q u v).2.drop v.length, d = 0))

/-- Contract of `(z nat) divRecursive(stk, u, v)` (natdiv.go:740-743) as used by `divLarge` (natdiv.go:626-630):
`len(v) >= divRecursiveThreshold`, `v` normalised (top bit set), `len(q) = len(u) - len(v)` and the quotient fits in `len(q)`
words (true in `divLarge` because `u[len(u)-1]` holds only the bits shifted out of `uIn`). -/
def DivRecursiveContract (dr : List Nat → List Nat → List Nat → List Nat × List Nat) : Prop :=
  ∀ q u v : List Nat, Wd q → Wd u → Wd v → 40 ≤ v.length → 2 ^ 63 ≤ topLimb v →
    v.length ≤ u.length → q.length = u.length - v.length → val u < val v * 2 ^ (64 * q.length) →
      (dr q u v).1.length = q.length ∧ (dr q u v).2.length = u.length ∧
      Wd (dr q u v).1 ∧ Wd (dr q u v).2 ∧
      val (dr q u v).1 = val u / val v ∧ val (dr q u v).2 = val u % val v ∧
      (∀ d ∈ (dr q u v).2.drop v.length, d = 0)

/-- Contract of the multiplier `(z nat) mul(stk, x, y)` (natmul.go:16) at the value level: normalised product. -/
def MulContract (mul : List Nat → List Nat → List Nat) : Prop :=
  ∀ a b : List Nat, Wd a → Wd b →
    Wd (mul a b) ∧ val (mul a b) = val a * val b ∧ Normed (mul a b) ∧ (mul a b).length ≤ a.length + b.length

end FvModexp.Mdl
