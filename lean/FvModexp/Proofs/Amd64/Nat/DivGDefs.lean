import FvModexp.Proofs.Amd64.Exp.ExpHyp
import FvModexp.Proofs.Amd64.Exp.RdIn0

set_option autoImplicit false

/-!
# `nat.div` (amd64): the empty-tolerant / results-apart statement — twin of `FvModexp.Arm64.ExpSlow.DivHypLG`

(agent top s35; defs only.) `DivPreG` = `ExpHyp.DivPre` with the dividend `u` empty-tolerant (`RdIn0`; each
apartness fact of `u` under `0 < ul`). `DivPostLG` = `ExpHyp.DivPostL` + the two results apart when both non-empty
+ a fresh quotient apart from the stack's final array (the arm64 clauses (ii)/(iii), same order). `DivHypLG`: the
`Ensures` premise in the CONVENTIONS §3 shape (register arguments `z, stk, z2`; `u`, `v` on the stack at
`RSP+8 … RSP+56`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn RdIn0 WrOut RtPost)
open FvModexp.Amd64.ExpHyp (NatOF StackOK' stWs fnDiv)

/-- `ExpHyp.DivPre` with the dividend `u` empty-tolerant: `RdIn0`, and each apartness fact of `u` under `0 < ul` -/
@[reducible] def DivPreG (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = u ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc ∧ s.mem.readLE ((s.regs 4).toNat + 32) 8 = v ∧
    s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl ∧ s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc ∧
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧ z2l ≤ z2c ∧
    WrOut R L s stk above zp zc ∧ WrOut R L s stk above z2 z2c ∧
    RdIn0 R L s stk above u ul ∧ RdIn R L s stk above v vl ∧ ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧
    NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16 ∧ (stCap s.mem st = 0 → stW s.mem st = 0) ∧
    (0 < ul → Apart u (8 * ul) st 24 ∧
      Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    Apart v (8 * vl) st 24 ∧ Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    st ≠ 0 ∧
    (Apart st 24 ((s.regs 14).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (Apart st 24 (s.fsBase.toNat - 8) 8 ∧
      Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8) ∧
    (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 ∧
    (0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)) ∧
    (∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      (0 < ul → Apart p (8 * c) u (8 * ul)) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    cost (stLen s.mem st) ul vl ≤ b ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- `ExpHyp.DivPostL` + the two results apart when both non-empty + a fresh quotient apart from the stack's final
array (as the remainder's clause) -/
@[reducible] def DivPostLG (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b (cost (stLen s.mem st) ul vl) L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      (0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc)) ∧
      (¬ (q = zp ∧ qc = zc) → 0 < qc → 0 < stCap s'.mem st →
        Apart q (8 * qc) (stW s'.mem st) (8 * stCap s'.mem st))

theorem DivPostLG.toL {R : RtInv} {b : Nat} {cost : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {stk above zp zc st z2 z2c u ul v vl : Nat} {s s' : State}
    (h : DivPostLG R b cost L stk above zp zc st z2 z2c u ul v vl s s') :
    ExpHyp.DivPostL R b cost L stk above zp zc st z2 z2c u ul v vl s s' := by
  obtain ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl, -, -⟩ := h
  exact ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl⟩

/-- **`nat.div`** (amd64), empty-tolerant dividend, `StackBackL` post, results apart -/
def DivHypLG (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c]
      (fun s => DivPreG R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc
        v vl vc s)
      (fun s s' => DivPostLG R b cost L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s')

end FvModexp.Amd64.ExpSlow
