import FvModexp.Proofs.Amd64.Nat.DivLargeDefs

set_option autoImplicit false

/-!
# `divLarge` (amd64): the strengthened postcondition `PostG` — twin of `Arm64/Nat/DivLargeG.lean` (defs)

`PostG` = `Post` + (ii) `q` apart from `r` when both are non-empty + (iii) a fresh `q` apart from the stack's final
array. `HypG` = `Hyp` with it; `HypG.toHyp` keeps every `Hyp` user valid. (A new module so that `DivLargeDefs` is
unchanged.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivLarge

@[reducible] def PostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem ip il / natVal s.mem vp vl) ∧
      ExpHyp.NatOF R L L' s'.mem up uc 1 r rl rc (natVal s.mem ip il % natVal s.mem vp vl) ∧
      EvenHyp.RtPost R b c L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = up ∧ rc = uc) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 41272 112 ++ (ar zp zc ++ ar up uc) ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ((ar zp zc ++ ar up uc) ++ stkWs s.mem st) ∧
      (0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc)) ∧
      (¬ (q = zp ∧ qc = zc) → 0 < qc → 0 < stCap s'.mem st →
        Apart q (8 * qc) (stW s'.mem st) (8 * stCap s'.mem st))

theorem PostG.toPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s s' : State} (h : PostG R b L c zp zc st up uc ip il vp vl s s') : Post R b L c zp zc st up uc ip il vp vl s s' := by
  obtain ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl, -, -⟩ := h
  exact ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl⟩

/-- `divLarge`'s `Ensures` with `PostG` -/
def HypG (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc : BitVec 64) (ip il vp vl : Nat),
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, u, ul, uc]
      (fun s => Pre R b L (cost dc (stLen s.mem st.toNat) il vl) z.toNat zc.toNat st.toNat u.toNat uc.toNat
        ip il vp vl s)
      (fun s s' => PostG R b L (cost dc (stLen s.mem st.toNat) il vl) z.toNat zc.toNat st.toNat u.toNat
        uc.toNat ip il vp vl s s')

theorem HypG.toHyp {impl : List Amd64.Segment} {R : RtInv} {dc : Nat → Nat → Nat → Nat} (h : HypG impl R dc) :
    Hyp impl R dc :=
  fun b L z zl zc st u ul uc ip il vp vl ret hret s hs hpre =>
    (h b L z zl zc st u ul uc ip il vp vl ret hret s hs hpre).mono fun _ h' => ⟨h'.1, h'.2.toPost⟩

end FvModexp.Amd64.DivLarge
