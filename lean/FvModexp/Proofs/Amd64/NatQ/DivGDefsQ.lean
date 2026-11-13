import FvModexp.Proofs.Amd64.Nat.DivGDefs
import FvModexp.Proofs.Amd64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# `nat.div` (amd64), empty-tolerant / results-apart statement, Q-form (TIGHT COSTS, top s38)

Amd64 twin of arm64 `ExpSlow.DivPreGQ` / `DivPostLGQ` / `DivHypLGQ` (Arm64/NatQ/DivHypQ.lean, asm s38) on top's amd64
`DivPreG` / `DivPostLG` / `DivHypLG` (Amd64/Nat/DivGDefs.lean): the cost slot is `(stLen + 16·ul + 64 ≤ H ∧ c ≤ b)`,
the post's runtime part `RtPostQ R b c r'`; `DivHypLGQ … cost` with `c = cost ul vl + stkR H s.mem st`,
`r' = stkR H s'.mem st` (as asm's amd64 `ExpHyp.DivHypLQ`, NatQ/DivHypQ.lean). `DivHypLGQ.toL : … → DivHypLQ …`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn RdIn0 WrOut)
open FvModexp.Amd64.ExpHyp (NatOF StackOK' stWs fnDiv)

/-- `ExpHyp.DivPre` with the dividend `u` empty-tolerant: `RdIn0`, and each apartness fact of `u` under `0 < ul` -/
@[reducible] def DivPreGQ (R : RtInv) (b H c : Nat) (L : List (Nat × Nat))
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
    (stLen s.mem st + 16 * ul + 64 ≤ H ∧ c ≤ b) ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧ (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (s.fsBase.toNat - 8) 8) ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- `ExpHyp.DivPostL` + the two results apart when both non-empty + a fresh quotient apart from the stack's final
array (as the remainder's clause) -/
@[reducible] def DivPostLGQ (R : RtInv) (b c r' : Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPostQ R b c r' L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      (0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc)) ∧
      (¬ (q = zp ∧ qc = zc) → 0 < qc → 0 < stCap s'.mem st →
        Apart q (8 * qc) (stW s'.mem st) (8 * stCap s'.mem st))

theorem DivPostLGQ.toL {R : RtInv} {b c r' : Nat} {L : List (Nat × Nat)}
    {stk above zp zc st z2 z2c u ul v vl : Nat} {s s' : State}
    (h : DivPostLGQ R b c r' L stk above zp zc st z2 z2c u ul v vl s s') :
    ExpHyp.DivPostLQ R b c r' L stk above zp zc st z2 z2c u ul v vl s s' := by
  obtain ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl, -, -⟩ := h
  exact ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl⟩

/-- **`nat.div`** (amd64), empty-tolerant dividend, `StackBackL` post, results apart, Q-form (`cost` level-free) -/
def DivHypLGQ (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (cost : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c]
      (fun s => DivPreGQ R b H (cost ul vl + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc
        v vl vc s)
      (fun s s' => DivPostLGQ R b (cost ul vl + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s')


theorem DivPreQ.toG {R : RtInv} {b H c : Nat} {L : List (Nat × Nat)}
    {stk above zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (h : ExpHyp.DivPreQ R b H c L stk above zp zl zc st z2 z2l z2c u ul uc v vl vc s) :
    DivPreGQ R b H c L stk above zp zl zc st z2 z2l z2c u ul uc v vl vc s := by
  obtain ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
  refine ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8.toRdIn0, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, fun _ => ⟨h20, h21⟩, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, fun p c hm hc => ?_, h30, h31⟩
  obtain ⟨a1, a2, a3, a4⟩ := h29 p c hm hc
  exact ⟨fun _ => a1, a2, a3, a4⟩

/-- the empty-tolerant Q form gives the plain Q form -/
theorem DivHypLGQ.toL {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat} (h : DivHypLGQ impl R ns stk above cost) : ExpHyp.DivHypLQ impl R ns stk above cost :=
  fun H b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
    (h H b L z zl zc st z2 z2l z2c u ul uc v vl vc).mono (fun _ hp => DivPreQ.toG hp) (fun _ _ _ hq => DivPostLGQ.toL hq)

end FvModexp.Amd64.ExpSlow
