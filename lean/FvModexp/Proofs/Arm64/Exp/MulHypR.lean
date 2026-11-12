import FvModexp.Proofs.Arm64.Exp.MulHyp

/-!
# `nat.sqr` / `nat.mul` premises WITH the reuse clause (arm64; agent infra, for `buildPrecomputationWindowModPower2`)

`buildPrecomputationWindowModPower2` (nat.go:856) reslices every result `powers[i] = (*p)[:len:w]` and panics unless
`cap ≥ w`, so it needs to know that `sqr` / `mul` REUSE `z` when it is big enough and not an alias (Go: `z.make(n)` reuses
when `n ≤ cap z`; `alias(z, x)` compares the cap ends `&z[cap-1] = &x[cap-1]`, nat.go:227). Same shape as `SqrHyp` /
`MulHyp` plus
* pre: each operand's capacity `xc` with `xl ≤ xc < 2^40`, `Held x (8 xc)`, `x + 8 xc ≤ 2^48` (divmc's `SPre` has these);
* post: `need ≤ zc →` (cap ends differ) `→` the result registers are `z`'s array and capacity
  (divmc's `SPost` reuse clause, `need = 2·xl` resp. `xl + yl`; for `nat.mul` also the `m < n` swap,
  `mulAddWW` (`z.make(m+1)`, `m + 1 ≤ m + n`) and the `len = 0` (`z[:0]`) paths reuse).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

/-- an operand's capacity facts -/
@[reducible] def CapIn (R : RtInv) (L : List (Nat × Nat)) (x xl xc : Nat) : Prop :=
  xl ≤ xc ∧ xc < 2 ^ 40 ∧ Held R L x (8 * xc) ∧ x + 8 * xc ≤ 2 ^ 48

/-- the result registers are `z`'s array when `need ≤ zc` and `z`'s cap end differs from every operand's -/
@[reducible] def Reuse (need zp zc : Nat) (ops : List (Nat × Nat)) (s' : State) : Prop :=
  need ≤ zc → (∀ o ∈ ops, zp + 8 * zc ≠ o.1 + 8 * o.2) →
    s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 2 = BitVec.ofNat 64 zc

def SqrHypR (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSqr) [z, zl, zc, st, x, xl, xc]
      (fun s => SqrPre R b (cost (stLen s.mem st.toNat) xl.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat x.toNat
        xl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat)
      (fun s s' => SqrPost R b (cost (stLen s.mem st.toNat) xl.toNat) L stk above z.toNat zc.toNat st.toNat x.toNat
        xl.toNat s s' ∧ Reuse (2 * xl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat)] s')

def MulHypR (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat)
      (fun s s' => MulPost R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zc.toNat st.toNat
        x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

end FvModexp.Arm64.EvenHyp
