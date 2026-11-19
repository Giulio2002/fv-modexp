import FvModexp.Proofs.Amd64.Exp.NNilD
import FvModexp.Proofs.Amd64.Exp.SetRetWinX

set_option autoImplicit false

/-!
# `ExpN.PreNF` survives installing the return address (amd64, Janus v0.4.0 `hinv` of `ExpN.ensNilF`; top s55)

Twin of `Exp/NInv.lean` (`ExpN.pre_setRet`) for the `stk == nil` precondition: `janus64_ensures_old` over `PreNF`
ran out of 12 GB. Proved by hand from the frame lemmas `SetRetWin` / `SetRetWinX`: the window
`[sp - K, sp + 0x510)` (`sp = RSP - 0x498`) contains the return slot; every memory read of the precondition (operands,
`natOne`, globals, the pool's `New` word, guard and TLS words) is apart from it, and the stack arguments lie at
`RSP + 8 …`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

open FvModexp.Amd64.SetRetWin

set_option maxHeartbeats 4000000 in
theorem preNF_setRet {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costD : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (ret : Nat)
    (h : PreNF R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow s) :
    PreNF R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow
      (s.setRet ret) := by
  unfold PreNF PreNil at h ⊢
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23,
    c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46,
    c47, c48, c49, c50, c51⟩, hX, hW⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, hce, hsv⟩ := c1
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19⟩ := hce
  have hR : 0x498 ≤ (s.regs 4).toNat := le_of_regs_eq (by decide) e1
  have hlo : (s.regs 4).toNat - 0x498 - K ≤ (s.regs 4).toNat := Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hhi : (s.regs 4).toNat + 8 ≤ (s.regs 4).toNat - 0x498 + 0x510 := slot_hi hR (by decide)
  have hhiA : (s.regs 4).toNat + 8 ≤ (s.regs 4).toNat - 0x498 - K + (K + 0x510) := slot_hiK hR v2 (by decide)
  have hmv : natVal (s.setRet ret).mem mp n = natVal s.mem mp n := rdA hlo hhiA c18.2
  have hone : (s.setRet ret).mem.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 := rdO hlo hhi hW
  have hacc : s.mem.accessible (s.regs 4).toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ v4 hlo hhiA
  have hsl : Outside (s.regs 4).toNat 8 R.rt := Outside.of_sub v8 hlo hhiA
  have hnz : ∀ p k, (0 < k → Apart p (8 * k) ((s.regs 4).toNat - 0x498 - K) (K + 0x510)) → NatNorm s.mem p k →
      NatNorm (s.setRet ret).mem p k := fun p k ha hn => by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [natNorm_setRet (Or.inl h0)]; exact hn
    · exact natNormA hlo hhiA (ha h0) hn
  obtain ⟨p1, p2, p3, p4⟩ := c3
  refine ⟨⟨⟨e1, e2, e3, e4, e5, e6, e7, ⟨v1, v2, v3, by rw [setRet_accessible]; exact v4, v5,
      by rw [setRet_accessible]; exact v6, by simp only [setRet_regs]; rw [rdA hlo hhiA v9]; exact v7, v8, v9, v10, v11,
      (dataLoaded_setRet_iff hacc).2 v12, v13, v14, v15, by rw [setRet_accessible]; exact v16,
      by simp only [setRet_fsBase]; rw [rdA hlo hhiA v19]; exact v17, v18, v19⟩, hsv⟩,
    globalsR hlo hhi c2, ⟨p1, (rdO hlo hhi p4).trans p2, p3, p4⟩, c4, c5, by rw [setRet_accessible]; exact c6, c7,
    stackArg hR (by decide) c8, stackArg hR (by decide) c9, stackArg hR (by decide) c10, stackArg hR (by decide) c11,
    stackArg hR (by decide) c12, stackArg hR (by decide) c13, c14, c15, c16, c17,
    c18, by rw [setRet_accessible]; exact c19, c20, natNormA hlo hhiA c18.2 c21,
    c22, fun hy => by rw [setRet_accessible]; exact c23 hy, c24, hnz _ _ (fun hy => (c22 hy).2) c25, c26, c27,
    c28, fun hx => by rw [setRet_accessible]; exact c29 hx, c30,
    hnz _ _ (fun hx => apart_mono (c28 hx).2 (Nat.mul_le_mul_left 8 c33)) c31, c32, c33, c34, c35, c36, c37,
    ?_, c39, c40, ?_, c42, by rw [setRet_accessible]; exact c43, c44, c45, c46,
    by rw [hmv]; exact c47, by rw [hmv]; exact c48, c49, by rw [view_setRet hsl]; exact c50,
    by rw [hone]; exact c51⟩, hX, hW⟩
  · intro hz
    rcases c38 hz with h | h | ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨z1, by rw [setRet_accessible]; exact z2, z3, z4, natLive.2 z5, z6, z7, z8, z9, z10, z11⟩)
  · intro hz
    obtain ⟨op, hN⟩ := c41 hz
    exact ⟨op, natOneR hlo hhi hN⟩

end FvModexp.Amd64.ExpN
