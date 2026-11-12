import FvModexp.Proofs.Arm64.Exp.EvenNHyp

/-!
# `nat.expNN` (arm64): the result capacity bound, and infra's `ExpNNHypNE0` from `ExpNNHypNE`

`ExpN.Post` states the result capacity `c < 2 ^ 40` (fresh results come from `nat.make`, whose capacity is below
`2 ^ 40`; reused ones are `z`'s, `zc < 2 ^ 40` by `ExpN.Pre`). `cap_of_post` unpacks it as the register fact;
`ExpNNHypNE.toNE0` turns the conclusion of `ExpN.ens_noEven` into infra's `EvenHyp.ExpNNHypNE0` (agent expmc, s33).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

theorem cap_of_post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {zp zc st xp xl yp yl mp n : Nat} {s s' : State}
    (h : Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s') : (s'.regs 2).toNat < 2 ^ 40 := by
  obtain ⟨p, l, c, -, -, h2, -, -, -, hc, -⟩ := h
  rw [h2, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hc.1

/-- the LOCATION of an empty result, as register values ([infra s33]): `0`, or a runtime pointer apart from the call's
live set (from `Post`'s `p < 2 ^ 64` and its location disjunct) -/
theorem loc_of_post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {zp zc st xp xl yp yl mp n : Nat} {s s' : State}
    (h : Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s') :
    (s'.regs 2).toNat = 0 → 0 < zc → (s'.regs 0).toNat = 0 ∨
      (InRanges (s'.regs 0).toNat 0 R.rt ∧ ApartAll (s'.regs 0).toNat 0 L) := by
  obtain ⟨p, l, c, h0, -, h2, -, -, -, hc, L', b', -, -, -, -, hres, -⟩ := h
  intro e2 hz
  rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at e2
  subst e2
  rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc.2]
  rcases hres with ⟨-, e⟩ | ⟨-, e⟩ | h
  · exact Or.inl e
  · omega
  · exact Or.inr h

end FvModexp.Arm64.ExpN

namespace FvModexp.Arm64.EvenHyp

theorem ExpNNHypNE.toNE0 {impl : List Segment} {R : RtInv} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    (h : ExpNNHypNE impl R K costF needR costR needS needP costS costP) :
    ExpNNHypNE0 impl R K costF needR costR needS needP costS costP :=
  fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
    (h b L zp zl zc st xp xl xc yp yl yc mp n mc slow).mono (fun _ hp => hp)
      (fun _ _ _ hq => ⟨hq, ExpN.cap_of_post hq⟩)

/-- [infra s33]: `ExpNNHypNE` → infra's `ExpNNHypNE1` (its body spelled out: `ExpNNHypNE0`'s post + the empty-result
location, `ExpN.loc_of_post`); usable wherever `EvenHyp.ExpNNHypNE1 …` is expected (definitional) -/
theorem ExpNNHypNE.toNE1 {impl : List Segment} {R : RtInv} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    (h : ExpNNHypNE impl R K costF needR costR needS needP costS costP) :
    ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat),
    Ensures ((Extracted.program.onlySegments ExpN.names).link impl) (segAddr Extracted.program ExpN.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 slow]
      (ExpN.Pre R b L K costF needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (fun s s' => ExpN.Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s' ∧
        (s'.regs 2).toNat < 2 ^ 40 ∧
        ((s'.regs 2).toNat = 0 → 0 < zc → (s'.regs 0).toNat = 0 ∨
          (InRanges (s'.regs 0).toNat 0 R.rt ∧ ApartAll (s'.regs 0).toNat 0 L))) :=
  fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
    (h b L zp zl zc st xp xl xc yp yl yc mp n mc slow).mono (fun _ hp => hp)
      (fun _ _ _ hq => ⟨hq, ExpN.cap_of_post hq, ExpN.loc_of_post hq⟩)

end FvModexp.Arm64.EvenHyp
