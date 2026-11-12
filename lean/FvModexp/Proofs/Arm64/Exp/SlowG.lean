import FvModexp.Proofs.Arm64.Exp.EvMulD
import FvModexp.Proofs.Arm64.Exp.ExpHypL

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the EMPTY-TOLERANT callee premise forms of its `sqr` / `div` calls (agent expmc)

FINDING (expmc s37): `nat.expNNSlow`'s loop can pass an EMPTY nat with a `nil` pointer (`(0, 0, 0)`) or an empty
runtime slice (cap 0, pointer anywhere in a runtime range) as the OPERAND of `zz.sqr(stk, z)`, `zz.mul(stk, z, x)` and
as the dividend of `zz.div(stk, r, z, m)`: e.g. `modexp(2, 4, 4)` (`y = 4` has 3 bits → `expNNSlow`): iteration 1
`z = 2² = 4`, `div(4, 4)` (`len m = 1`) returns `r = z2.setWord(0) = nil` (the `r` buffer is still `nil`), so
iteration 2 calls `nil.sqr(stk, nil)` and `div(…, u = nil, …)`. divmc's `SqrHypX` / asm's `DivHypL` ask `RdIn` of the
operand (`accessible p 0` = a memory REGION containing `p`, false for `p = 0`), so they cannot be discharged there.
The Go code is fine (`sqr`: `n == 0 → return z[:0]`; `divW` with `len u = 0`; `z2.set(u)` copies 0 words).

Premise forms used by `ExpSlow.hyp` (callee summaries stay premises; the owners prove these forms):
* `SqrHypG` (divmc): `SqrHypX` with the operand `RdIn0`, `CapIn0` (infra's, EvMulD) and `SqrXG` (alias-capacity fact
  under `0 < zc → 0 < xl`); post `SqrPostL` (no `Reuse`). divmc's `SPre` already has every operand fact under
  `0 < xl`/`0 < xc` EXCEPT `accessible xp (8 * xl)`.
* `MulHypG` (infra's, EvMulD; proved: `ExpEven.NatMulG.hypG`) — unchanged.
* `DivHypLG` (asm): `DivHypL` with the dividend `RdIn0` and every apartness fact of `u` under `0 < ul`
  (`DivPreG`; post `DivPostL` unchanged).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut StackOK' DivPostL fnDiv)
open FvModexp.Arm64.ExpEven (CapIn0)

/-- `EvenHyp.SqrPre` with the operand empty-tolerant (`RdIn0`) -/
@[reducible] def SqrPreG (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st x xl : Nat)
    (s : State) : Prop :=
  CallEnv R L s stk above ∧ RunIface.Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧
    WrOut R L s stk above zp zc ∧
    RdIn0 R L s stk above x xl ∧ xl ≤ 2 ^ 12 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    StkIn R L s stk above st ∧ stLen s.mem st + 4 * (2 * xl) + 64 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st x (8 * xl) ∧
    c ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

theorem SqrPre.toG {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st x xl : Nat} {s : State}
    (h : SqrPre R b c L stk above zp zl zc st x xl s) : SqrPreG R b c L stk above zp zl zc st x xl s := by
  obtain ⟨h1, h2, h3, h4, h5, hx, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, hx.toRdIn0, h6⟩

/-- `SqrX` with the alias-capacity fact guarded (as infra's `MulXG`) -/
@[reducible] def SqrXG (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st zp zc x xl xc : Nat) : Prop :=
  StkX R L s stk above st ∧ Outside zp (8 * zc) (win s stk above) ∧ (zp = x → 0 < zc → 0 < xl → zc = xc) ∧
    OpX s.mem st zp (8 * zc) ∧ OpX s.mem st x (8 * xl)

/-- **`nat.sqr`**, empty-tolerant operand (see the module doc) -/
def SqrHypG (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSqr) [z, zl, zc, st, x, xl, xc]
      (fun s => SqrPreG R b (cost (stLen s.mem st.toNat) xl.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat
        x.toNat xl.toNat s ∧ CapIn0 R L x.toNat xl.toNat xc.toNat ∧
        SqrXG R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat)
      (fun s s' => SqrPostL R b (cost (stLen s.mem st.toNat) xl.toNat) L stk above z.toNat zc.toNat st.toNat x.toNat
        xl.toNat s s')

/-- `ExpHyp.DivPre` with the dividend `u` empty-tolerant: `RdIn0`, and each apartness fact of `u` under `0 < ul` -/
@[reducible] def DivPreG (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zl zc st z2 z2l z2c u ul v vl : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ RunIface.Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧ z2l ≤ z2c ∧
    WrOut R L s stk above zp zc ∧ WrOut R L s stk above z2 z2c ∧
    RdIn0 R L s stk above u ul ∧ RdIn R L s stk above v vl ∧ ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧
    NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16 ∧ (stCap s.mem st = 0 → stW s.mem st = 0) ∧
    (0 < ul → Apart u (8 * ul) st 24 ∧
      Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    Apart v (8 * vl) st 24 ∧ Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    st ≠ 0 ∧
    (Apart st 24 ((s.regs 28).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 ∧
    (0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)) ∧
    (∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      (0 < ul → Apart p (8 * c) u (8 * ul)) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    cost (stLen s.mem st) ul vl ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- **`nat.div`**, empty-tolerant dividend, `StackBackL` post (see the module doc) -/
def DivHypLG (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => DivPreG R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat
        ul.toNat v.toNat vl.toNat s)
      (fun s s' => DivPostL R b cost L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat
        vl.toNat s s')

end FvModexp.Arm64.ExpSlow
