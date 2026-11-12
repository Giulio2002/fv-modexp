import FvModexp.Proofs.Arm64.Exp.ExpHyp

/-!
# `nat.div`'s shape with the stack in the live set (`StackBackL`, BRIEF "STACK-IN-LIVE-SET")

`DivPostL` = `ExpHyp.DivPost` with `StackBackL` (a grown stack array is an element of the final live set) in place of
`StackBack`; `DivHypL` = `DivHyp` with it. The windows need it to export `StackBackL` (`nat.expNN`'s `stk == nil` path
ends in `Pool.Put`). `DivHypL.toDivHyp` keeps every `DivHyp` user valid.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpHyp

@[reducible] def DivPostL (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 1 = BitVec.ofNat 64 ql ∧
    s'.regs 2 = BitVec.ofNat 64 qc ∧ s'.regs 3 = BitVec.ofNat 64 r ∧ s'.regs 4 = BitVec.ofNat 64 rl ∧
    s'.regs 5 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b (cost (stLen s.mem st) ul vl) L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st)

theorem DivPostL.toDivPost {R : RtInv} {b : Nat} {cost : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {stk above zp zc st z2 z2c u ul v vl : Nat} {s s' : State}
    (h : DivPostL R b cost L stk above zp zc st z2 z2c u ul v vl s s') :
    DivPost R b cost L stk above zp zc st z2 z2c u ul v vl s s' := by
  obtain ⟨q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hf, hl⟩ := h
  exact ⟨q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb.toStackBack, ha, hf, hl⟩

/-- `DivHyp` with the `StackBackL` post -/
def DivHypL (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat
        ul.toNat v.toNat vl.toNat s)
      (fun s s' => DivPostL R b cost L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat
        vl.toNat s s')

theorem DivHypL.toDivHyp {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat → Nat} (h : DivHypL impl R ns stk above cost) : DivHyp impl R ns stk above cost :=
  fun b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs hpre =>
    (h b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs hpre).mono fun _ h' => ⟨h'.1, h'.2.toDivPost⟩

end FvModexp.Arm64.ExpHyp
