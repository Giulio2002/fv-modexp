import FvModexp.Proofs.Arm64.Nat.DivLargeDefs
import FvModexp.Proofs.Arm64.Nat.SqrMulX
import FvModexp.Proofs.Common.MulCost
import FvModexp.Proofs.Common.DivRec

/-!
# `(z nat) divRecursiveStep(stk *stack, u, v nat, depth int)` (go-bigmodexpfix natdiv.go:750), arm64 — statements

The function is recursive (`qhat.divRecursiveStep(stk, uu[s:B+n], v[s:], depth+1)`, natdiv.go:813 / :863, on a divisor of
`n - n/2 + 1 < n` words), so its summary is proved by induction on `len v` (`Summary.induction_mutual` over the argument
record `Args`, PROOFS.md §Recursion), on the program `LibDrs` (the division tree without `divLarge` / `nat.div`).

* window: the member pre takes a window `W ≥ drsW (len v)`; one level down the window is `W - 400` (frame 400,
  `SUB $400, RSP, R20`; spills `SP + 8 … SP + 96`, `above = 96`), `drsW_inner`. The deepest callee is `nat.mul`
  (`mulWX = 30208`, `above = 88`): `drsW n = 30608 + 400·log₂(n - 3) ≤ 40960` for `n ≤ 2^9` (`drsW_le`).
* budget: `drsC ℓ ul vl` (`ℓ` the stack length at entry) mirrors the calls: `divBasic` (`n < 40`) or `stk.nat(B + 1)` and
  at most `(ul - vl) / B + 1` wide-digit steps, each a recursive call, `stk.nat(3n)` and `nat.mul(qhat, v[:B-1])`.
* `nat.mul` is a premise in divmc's export shape (`EvenHyp.MulHypX`) plus its exact-write clause (`ExactR`, = divmc's
  `NatMul.Exact`): `qhatv[:s]` may reach past the product's length into the zeros of `clear(qhatv)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW drsFn drsNames)

def fn : String := drsFn
def names : List String := drsNames

theorem entry_drs : segAddr Extracted.program drsFn = 0x1ba3a0 := by decide

/-! ## Window -/

/-- the window of `divRecursiveStep` on a divisor of `n` words -/
def drsW (n : Nat) : Nat := 30608 + 400 * Nat.log2 (n - 3)

theorem drsW_ge (n : Nat) : 30608 ≤ drsW n := by unfold drsW; omega

/-- the recursive call runs one frame (400) down on `n - n/2 + 1` words -/
theorem drsW_inner {n : Nat} (h : 40 ≤ n) : drsW (n - n / 2 + 1) + 400 ≤ drsW n := by
  unfold drsW
  have := log2_step (a := n - n / 2 + 1 - 3) (b := n - 3) (by omega) (by omega)
  omega

theorem drsW_le {n : Nat} (h : n ≤ 2 ^ 9) : drsW n ≤ 40960 := by
  unfold drsW
  have h1 : Nat.log2 (n - 3) ≤ Nat.log2 (2 ^ 9) := log2_mono (by omega)
  have h2 : Nat.log2 (2 ^ 9) = 9 := by decide
  omega

/-! ## Budget -/

/-- **the budget of `divRecursiveStep`** (`ℓ` the stack length at entry, `ul`/`vl` the argument lengths) -/
def drsC (ℓ ul n : Nat) : Nat :=
  if h : n < 40 then stackNatCost ℓ (n + 1) else
    stackNatCost ℓ (n / 2 + 1) +
      ((ul - n) / (n / 2) + 1) *
        (drsC (ℓ + StackNat.rnd (n / 2 + 1)) ul (n - n / 2 + 1) +
          stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) +
          mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1))
termination_by n
decreasing_by omega

theorem drsC_small {ℓ ul n : Nat} (h : n < 40) : drsC ℓ ul n = stackNatCost ℓ (n + 1) := by
  rw [drsC, dif_pos h]

theorem drsC_big {ℓ ul n : Nat} (h : ¬ n < 40) : drsC ℓ ul n =
    stackNatCost ℓ (n / 2 + 1) +
      ((ul - n) / (n / 2) + 1) *
        (drsC (ℓ + StackNat.rnd (n / 2 + 1)) ul (n - n / 2 + 1) +
          stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) +
          mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1)) := by
  rw [drsC, dif_neg h]

/-- `drsC` is monotone in the dividend length -/
theorem drsC_ul : ∀ (n ℓ ul ul' : Nat), ul ≤ ul' → drsC ℓ ul n ≤ drsC ℓ ul' n
  | n, ℓ, ul, ul', h => by
    by_cases hn : n < 40
    · rw [drsC_small hn, drsC_small hn]; exact Nat.le_refl _
    · rw [drsC_big hn, drsC_big hn]
      have ih := drsC_ul (n - n / 2 + 1) (ℓ + StackNat.rnd (n / 2 + 1)) ul ul' h
      have hq : (ul - n) / (n / 2) ≤ (ul' - n) / (n / 2) := Nat.div_le_div_right (by omega)
      have := Nat.mul_le_mul (Nat.add_le_add_right hq 1)
        (Nat.add_le_add_right (Nat.add_le_add_right ih
          (stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n)))
          (mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1)))
      omega
termination_by n => n
decreasing_by omega

/-! ## `nat.mul` (premise) -/

/-- divmc's `NatMul.Exact` (MulDefs) on the result registers: when `z` is large enough and no operand's alias, the result
is `z`'s array, only `z[0:need]` (and the stack scratch) is written, and `z[0:need]` holds the product (or, on the paths
that write nothing, the product is `0` and `z[0:need]` is unchanged) -/
@[reducible] def ExactR (R : RtInv) (L : List (Nat × Nat)) (ws : List (Nat × Nat))
    (need zp zc st xp xc yp yc v : Nat) (s s' : State) : Prop :=
  need ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → zp + 8 * zc ≠ yp + 8 * yc →
    s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 2 = BitVec.ofNat 64 zc ∧
    (natVal s'.mem zp need = v ∨ (v = 0 ∧ natVal s'.mem zp need = natVal s.mem zp need)) ∧
    MemFrame s.mem s'.mem (R.rt ++ ws ++ [(zp, zp + 8 * need)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(zp, zp + 8 * need)] ++ stkWs s.mem st)

/-- `nat.mul`'s statement as divRecursiveStep uses it: divmc's `EvenHyp.MulHypX` with the exact-write clause -/
def MulHypXE (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program EvenHyp.fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => EvenHyp.MulPre R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ EvenHyp.CapIn R L x.toNat xl.toNat xc.toNat ∧
        EvenHyp.CapIn R L y.toNat yl.toNat yc.toNat ∧
        EvenHyp.MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat)
      (fun s s' => EvenHyp.MulPostL R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        ExactR R L (winA s stk above) (xl.toNat + yl.toNat) z.toNat zc.toNat st.toNat x.toNat xc.toNat y.toNat yc.toNat
          (natVal s.mem x.toNat xl.toNat * natVal s.mem y.toNat yl.toNat) s s')

/-! ## The recursion as one family of summaries -/

/-- a call: budget, live set, window and the eleven argument registers `z = (qp, ql, qc)`, `stk`, `u = (up, ul, uc)`,
`v = (vp, vl, vc)`, `depth` -/
structure Args where
  b : Nat
  L : List (Nat × Nat)
  W : Nat
  qp : BitVec 64
  ql : BitVec 64
  qc : BitVec 64
  st : BitVec 64
  up : BitVec 64
  ul : BitVec 64
  uc : BitVec 64
  vp : BitVec 64
  vl : BitVec 64
  vc : BitVec 64
  d : BitVec 64

/-- the argument registers and the return-address facts at the entry -/
@[reducible] def Entry (a : Args) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = a.qp ∧ s.regs 1 = a.ql ∧ s.regs 2 = a.qc ∧
    s.regs 3 = a.st ∧ s.regs 4 = a.up ∧ s.regs 5 = a.ul ∧ s.regs 6 = a.uc ∧ s.regs 7 = a.vp ∧ s.regs 8 = a.vl ∧
    s.regs 9 = a.vc ∧ s.regs 10 = a.d

/-- the member precondition: window large enough, `DrsPreW` with the budget `drsC` -/
def preOf (R : RtInv) (a : Args) (s : State) : Prop :=
  Entry a s ∧ drsW a.vl.toNat ≤ a.W ∧
    DrsPreW R a.b a.L (drsC (stLen s.mem a.st.toNat) a.ul.toNat a.vl.toNat) a.W a.qp.toNat a.ql.toNat a.qc.toNat
      a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat s

/-- the callee-saved part of the post -/
@[reducible] def Kept (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18

def postOf (R : RtInv) (a : Args) (s s' : State) : Prop :=
  Kept s s' ∧ DrsPostW R a.b a.L (drsC (stLen s.mem a.st.toNat) a.ul.toNat a.vl.toNat) a.W a.qp.toNat a.ql.toNat
    a.st.toNat a.up.toNat a.ul.toNat a.vp.toNat a.vl.toNat s s'

/-- the measure: the divisor length -/
def μ (a : Args) (_ : State) : Nat := a.vl.toNat

/-- the program of the summary -/
abbrev P (impl : List Segment) : Program := (Extracted.program.onlySegments names).link impl

/-- the induction hypothesis below measure `n` -/
@[reducible] def IH (impl : List Segment) (R : RtInv) (n : Nat) (a : Args) : Prop :=
  Summary (P impl) 0x1ba3a0 (fun s => preOf R a s ∧ μ a s < n) (postOf R a)

end FvModexp.Arm64.DivRec
