import FvModexp.Proofs.Arm64.Exp.SlowG
import FvModexp.Proofs.Arm64.Exp.NHyp
import FvModexp.Proofs.Arm64.Nat.RtPostQ
import FvModexp.Proofs.Common.MulCostQ

set_option autoImplicit false

/-!
# Q-form (TIGHT COSTS) export statements of the division chain (arm64; owner asm)

The amortised-stack twins (Common/StackPot, NOTES-conventions "[divmc s34]/[divmc s35] TIGHT COSTS") of
* `ExpHyp.DivHypL` → `ExpHyp.DivHypLQ` and `ExpSlow.DivHypLG` → `ExpSlow.DivHypLGQ` (`nat.div`, stack given),
* `NHyp.RemHyp` → `NHyp.RemHypQ` (`nat.rem`, stack given; post `NHyp.CPostRQ`),
* `IMod.DivHypM` (`nat.div` with `stk == nil`, the stack owned by the call): SAME statement, only the cost instance
  changes: `Q.NatDiv.costMQ Q.drsCQ` (the plain form `C + stkRes (HM ul)`, `HM ul = 16·ul + 64` the level bound of a
  fresh stack, `len = 0`).
Shape (divmc's HOW-TO): a reserve level `H` is ∀-quantified before `b`; the pre's cost slot is the PAIR
`(stLen s.mem st + D ≤ H ∧ c ≤ b)` (`D` = the `2 ^ 16` bound's, which stays) with the interface cost
`c = C ul vl + stkR H s.mem st` (`C` level-free); the post's `RtPost … c` becomes `RtPostQ … c (stkR H s'.mem st)`.

Level-free costs (`stk.nat` costs nothing; transcriptions of the calls, go-bigmodexpfix natdiv.go):
* `divBasic` (natdiv.go:646): `0` (its only charged call is `stk.nat(n + 1)`);
* `drsCQ ul n` (natdiv.go:750): `n < 40` → `divBasic` (0); else at most `(ul - n)/(n/2) + 1` wide-digit steps, each a
  recursive call on `n - n/2 + 1` words and `qhatv.mul(stk, qhat, v[:B-1])` (`mulCQ (n/2 + 1) (n/2 - 1)`);
* `DivLarge.costQ dc il vl` (natdiv.go:590): `u.make(len uIn + 1)`, `z.make(m + 1)`, the division `dc (il + 1) vl`;
* `NatDiv.costQ dc ul vl` (natdiv.go:520): `divW`'s `z.make(len u)` + `setWord`'s `make(nat, 1)` + `divLarge`;
* `nat.rem` (natdiv.go:505): the `div` only (`stk.nat(k)` is free): cost instance `NatDiv.costQ dc` itself.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q

/-- **the level-free budget of `divRecursiveStep`** (`ul`/`n` the dividend/divisor lengths) -/
def drsCQ (ul n : Nat) : Nat :=
  if h : n < 40 then 0 else
    ((ul - n) / (n / 2) + 1) * (drsCQ ul (n - n / 2 + 1) + mulCQ (n / 2 + 1) (n / 2 - 1))
termination_by n
decreasing_by omega

theorem drsCQ_small {ul n : Nat} (h : n < 40) : drsCQ ul n = 0 := by
  rw [drsCQ, dif_pos h]

theorem drsCQ_big {ul n : Nat} (h : ¬ n < 40) : drsCQ ul n =
    ((ul - n) / (n / 2) + 1) * (drsCQ ul (n - n / 2 + 1) + mulCQ (n / 2 + 1) (n / 2 - 1)) := by
  rw [drsCQ, dif_neg h]

/-- `drsCQ` is monotone in the dividend length -/
theorem drsCQ_ul : ∀ (n ul ul' : Nat), ul ≤ ul' → drsCQ ul n ≤ drsCQ ul' n
  | n, ul, ul', h => by
    by_cases hn : n < 40
    · rw [drsCQ_small hn, drsCQ_small hn]; exact Nat.le_refl _
    · rw [drsCQ_big hn, drsCQ_big hn]
      have ih := drsCQ_ul (n - n / 2 + 1) ul ul' h
      have hq : (ul - n) / (n / 2) ≤ (ul' - n) / (n / 2) := Nat.div_le_div_right (by omega)
      exact Nat.mul_le_mul (Nat.add_le_add_right hq 1) (Nat.add_le_add_right ih _)
termination_by n => n
decreasing_by omega

/-- the level-free budget of `divLarge` (`il = len uIn`, `vl = len vIn`; `dc` the division's) -/
@[reducible] def DivLarge.costQ (dc : Nat → Nat → Nat) (il vl : Nat) : Nat :=
  makeCost (il + 1) + makeCost (il - vl + 1) + dc (il + 1) vl

/-- the level-free budget of `nat.div` with a given stack -/
@[reducible] def NatDiv.costQ (dc : Nat → Nat → Nat) (ul vl : Nat) : Nat :=
  makeCost ul + makeCost 1 + DivLarge.costQ dc ul vl

/-- the reserve level of the `stk == nil` form (`getStack()` returns `len = 0`; `nat.div`'s bound `16·len u + 64`) -/
@[reducible] def NatDiv.HM (ul : Nat) : Nat := 16 * ul + 64

/-- the budget of the `stk == nil` form (`IMod.DivHypM`'s cost argument): the plain form `C + stkRes H` + the
24-byte `newobject` of `getStack` (as `NatDiv.costM`) -/
@[reducible] def NatDiv.costMQ (dc : Nat → Nat → Nat) (ul vl : Nat) : Nat :=
  NatDiv.costQ dc ul vl + stkRes (NatDiv.HM ul) + 24

end FvModexp.Arm64.Q

namespace FvModexp.Arm64.ExpHyp

/-- `DivPre` in the Q-form: the cost slot is `(stLen + 16·len u + 64 ≤ H ∧ c ≤ b)` -/
@[reducible] def DivPreQ (R : RtInv) (b H c : Nat) (L : List (Nat × Nat))
    (stk above zp zl zc st z2 z2l z2c u ul v vl : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ RunIface.Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧ z2l ≤ z2c ∧
    WrOut R L s stk above zp zc ∧ WrOut R L s stk above z2 z2c ∧
    RdIn R L s stk above u ul ∧ RdIn R L s stk above v vl ∧ ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧
    NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16 ∧ (stCap s.mem st = 0 → stW s.mem st = 0) ∧
    Apart u (8 * ul) st 24 ∧ Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    Apart v (8 * vl) st 24 ∧ Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    st ≠ 0 ∧
    (Apart st 24 ((s.regs 28).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 ∧
    (0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)) ∧
    (∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      Apart p (8 * c) u (8 * ul) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (stLen s.mem st + 16 * ul + 64 ≤ H ∧ c ≤ b) ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- `DivPostL` in the Q-form (`c` the interface cost, `r'` the reserve after the call) -/
@[reducible] def DivPostLQ (R : RtInv) (b c r' : Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 1 = BitVec.ofNat 64 ql ∧
    s'.regs 2 = BitVec.ofNat 64 qc ∧ s'.regs 3 = BitVec.ofNat 64 r ∧ s'.regs 4 = BitVec.ofNat 64 rl ∧
    s'.regs 5 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPostQ R b c r' L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st)

/-- **`nat.div`, Q-form** (twin of `DivHypL`; `cost` level-free, e.g. `Q.NatDiv.costQ Q.drsCQ`) -/
def DivHypLQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => DivPreQ R b H (cost ul.toNat vl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s)
      (fun s s' => DivPostLQ R b (cost ul.toNat vl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s')

end FvModexp.Arm64.ExpHyp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut StackOK' fnDiv DivPreQ DivPostLQ DivHypLQ)

/-- `DivPreG` in the Q-form: the cost slot is `(stLen + 16·len u + 64 ≤ H ∧ c ≤ b)` -/
@[reducible] def DivPreGQ (R : RtInv) (b H c : Nat) (L : List (Nat × Nat))
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
    (stLen s.mem st + 16 * ul + 64 ≤ H ∧ c ≤ b) ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- `DivPostLG` in the Q-form -/
@[reducible] def DivPostLGQ (R : RtInv) (b c r' : Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 1 = BitVec.ofNat 64 ql ∧
    s'.regs 2 = BitVec.ofNat 64 qc ∧ s'.regs 3 = BitVec.ofNat 64 r ∧ s'.regs 4 = BitVec.ofNat 64 rl ∧
    s'.regs 5 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      ExpHyp.NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPostQ R b c r' L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ ExpHyp.stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ ExpHyp.stWs s.mem st) ∧
      (0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc)) ∧
      (¬ (q = zp ∧ qc = zc) → 0 < qc → 0 < stCap s'.mem st →
        Apart q (8 * qc) (stW s'.mem st) (8 * stCap s'.mem st))

/-- **`nat.div`, empty-tolerant dividend, Q-form** (twin of `DivHypLG`; `cost` level-free) -/
def DivHypLGQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => DivPreGQ R b H (cost ul.toNat vl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s)
      (fun s s' => DivPostLGQ R b (cost ul.toNat vl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk
        above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s')

theorem DivPreQ.toG {R : RtInv} {b H c : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st z2 z2l z2c u ul v vl : Nat}
    {s : State} (h : DivPreQ R b H c L stk above zp zl zc st z2 z2l z2c u ul v vl s) :
    DivPreGQ R b H c L stk above zp zl zc st z2 z2l z2c u ul v vl s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hu, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hus, huf, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, hall, h28⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hu.toRdIn0, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    fun _ => ⟨hus, huf⟩, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    fun p c hm hc => ⟨fun _ => (hall p c hm hc).1, (hall p c hm hc).2⟩, h28⟩

theorem DivPostLGQ.toL {R : RtInv} {b c r' : Nat} {L : List (Nat × Nat)} {stk above zp zc st z2 z2c u ul v vl : Nat}
    {s s' : State} (h : DivPostLGQ R b c r' L stk above zp zc st z2 z2c u ul v vl s s') :
    DivPostLQ R b c r' L stk above zp zc st z2 z2c u ul v vl s s' := by
  obtain ⟨q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hf, hl, -, -⟩ := h
  exact ⟨q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hf, hl⟩

/-- the empty-tolerant Q form gives the plain Q form -/
theorem DivHypLGQ.toL {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat} (h : DivHypLGQ impl R ns stk above cost) : DivHypLQ impl R ns stk above cost :=
  fun H b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
    (h H b L z zl zc st z2 z2l z2c u ul uc v vl vc).mono_ret (fun _ hp => DivPreQ.toG hp) (fun _ _ _ _ hq => DivPostLGQ.toL hq)

end FvModexp.Arm64.ExpSlow

namespace FvModexp.Arm64.NHyp

open FvModexp.Arm64.ExpHyp

/-- `CPostR` in the Q-form (`c` the interface cost, `r'` the reserve after the call) -/
@[reducible] def CPostRQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v c r' : Nat)
    (s s' : State) : Prop :=
  ∃ p l cp : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 cp ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF R L L' s'.mem zp zc 1 p l cp v ∧ RtPostQ R b c r' L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p cp

/-- **`nat.rem`, Q-form** (twin of `RemHyp`; `cost` level-free, e.g. `Q.NatDiv.costQ Q.drsCQ`; the level twin of
`CPre`'s `stLen + need ≤ 2 ^ 16` is the last pre conjunct) -/
def RemHypQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnRem)
      [z, zl, zc, st, u, ul, uc, v, vl, vc]
      (fun s => (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(u.toNat, ul.toNat), (v.toNat, vl.toNat)]
          (need ul.toNat vl.toNat) (cost ul.toNat vl.toNat + stkR H s.mem st.toNat) s ∧
        0 < vl.toNat) ∧ NoAlias z.toNat zc.toNat u.toNat uc.toNat ∧ 0 < st.toNat ∧
        stLen s.mem st.toNat + need ul.toNat vl.toNat ≤ H)
      (fun s s' => CPostRQ R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem u.toNat ul.toNat % natVal s.mem v.toNat vl.toNat)
        (cost ul.toNat vl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) s s')

end FvModexp.Arm64.NHyp
