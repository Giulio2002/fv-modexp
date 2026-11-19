import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Amd64.Exp.SetRetWinX

set_option autoImplicit false

/-!
# `ExpN.Pre` survives installing the return address (amd64, Janus v0.4.0 `hinv` of `ExpN.ens_noEven`; top s54)

`janus64_ensures_old` over the whole precondition ran > 5 min and > 12 GB. Proved by hand from the frame lemmas `SetRetWin` /
`SetRetWinX`: the window `[sp - K, sp + 0x510)` (`sp = RSP - 0x498`) contains the return slot; every memory read of the
precondition (stack header, operands, `natOne`, globals, guard and TLS words) is apart from it, and the stack arguments
lie at `RSP + 8 …`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

open FvModexp.Amd64.SetRetWin

set_option maxHeartbeats 4000000 in
theorem pre_setRet {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s : State} (ret : Nat)
    (h : Pre R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow s) :
    Pre R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow (s.setRet ret) := by
  unfold Pre NPre at h ⊢
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24,
    c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48,
    c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60⟩, hm, hX⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, hce, hsv⟩ := c1
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19⟩ := hce
  have hR : 0x498 ≤ (s.regs 4).toNat := le_of_regs_eq (by decide) e1
  have hlo : (s.regs 4).toNat - 0x498 - K ≤ (s.regs 4).toNat := Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hhi : (s.regs 4).toNat + 8 ≤ (s.regs 4).toNat - 0x498 + 0x510 := slot_hi hR (by decide)
  have hhiA : (s.regs 4).toNat + 8 ≤ (s.regs 4).toNat - 0x498 - K + (K + 0x510) := slot_hiK hR v2 (by decide)
  obtain ⟨hw, hl, hc⟩ := stHdrA (ret := ret) hlo hhiA c43
  have hfree : W4En.free (s.setRet ret).mem st = W4En.free s.mem st := by simp only [W4En.free, hw, hl, hc]
  have hws : ExpHyp.stWs (s.setRet ret).mem st = ExpHyp.stWs s.mem st := by simp only [ExpHyp.stWs, stkWs, hw, hl, hc]
  have hmv : natVal (s.setRet ret).mem mp n = natVal s.mem mp n := rdA hlo hhiA c17.2.1
  have hone : (s.setRet ret).mem.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 := by
    obtain ⟨op, hN, -⟩ := c39
    exact rdO hlo hhi (Outside.of_sub hN.2.2.2.2.2.2.1 (Nat.le_refl _) (Nat.add_le_add_left (by decide) _))
  have hNE : ∀ a k, NE R L ((s.regs 4).toNat - 0x498) K st s.mem a k →
      NE R L ((s.regs 4).toNat - 0x498) K st (s.setRet ret).mem a k := fun a k h => by
    obtain ⟨n1, n2, n3, n4⟩ := h
    refine ⟨n1, n2, n3, ?_⟩
    rw [hfree]; exact n4
  have hacc : s.mem.accessible (s.regs 4).toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ v4 hlo hhiA
  have hsl : Outside (s.regs 4).toNat 8 R.rt := Outside.of_sub v8 hlo hhiA
  refine ⟨⟨⟨e1, e2, e3, e4, e5, e6, e7, ⟨v1, v2, v3, by rw [setRet_accessible]; exact v4, v5,
      by rw [setRet_accessible]; exact v6, by simp only [setRet_regs]; rw [rdA hlo hhiA v9]; exact v7, v8, v9, v10, v11,
      (dataLoaded_setRet_iff hacc).2 v12, v13, v14, v15, by rw [setRet_accessible]; exact v16,
      by simp only [setRet_fsBase]; rw [rdA hlo hhiA v19]; exact v17, v18, v19⟩, hsv⟩,
    globalsR hlo hhi c2, c3, c4, by rw [setRet_accessible]; exact c5, c6,
    stackArg hR (by decide) c7, stackArg hR (by decide) c8, stackArg hR (by decide) c9, stackArg hR (by decide) c10, stackArg hR (by decide) c11,
    stackArg hR (by decide) c12, c13, c14, c15, c16,
    hNE _ _ c17, by rw [setRet_accessible]; exact c18, c19, natNormA hlo hhiA c17.2.1 c20,
    hNE _ _ c21, by rw [setRet_accessible]; exact c22, c23, natNormA hlo hhiA c21.2.1 c24, c25, c26,
    hNE _ _ c27, by rw [setRet_accessible]; exact c28, c29,
    natNormA hlo hhiA (apart_mono c27.2.1 (Nat.mul_le_mul_left 8 c32)) c30, c31, c32, c33, c34, c35, c36,
    ?_, hNE _ _ c38, ?_, c40, c41, ?_, c43, c44, c45, by rw [hc, hw]; exact c46, by rw [hc, hw]; exact c47,
    by rw [setRet_accessible]; exact c48, c49, by rw [hfree]; exact c50, by rw [hfree]; exact c51,
    by rw [hfree]; exact c52, by rw [hl]; exact c53, by rw [hl]; exact c54, by rw [hl]; exact c55,
    by rw [hl, hmv]; exact c56, by rw [hl, hmv]; exact c57, by rw [hl]; exact c58,
    by rw [view_setRet hsl]; exact c59, ?_⟩, by rw [hmv]; exact hm, hX⟩
  · obtain ⟨c37a, c37b⟩ := c37
    refine ⟨fun hz => ?_, c37b⟩
    rcases c37a hz with h | h | ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hNE _ _ z1, by rw [setRet_accessible]; exact z2, z3, z4, natLive.2 z5, z6, z7, z8, z9, z10, z11⟩)
  · obtain ⟨op, hN, hSA⟩ := c39
    rw [hws]
    exact ⟨op, natOneR (rest := [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) hlo hhi hN,
      by simp only [NHyp.StkApart, hw, hl, hc]; exact hSA⟩
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := c42
    refine ⟨k1, k2, by rw [setRet_accessible]; exact k3, k4, ?_, ?_, ?_⟩
    · rw [hw, hc]; exact natLive.2 k5
    · rw [hl, hc]; exact k6
    · rw [hc]; exact k7
  · obtain ⟨x1, x2, x3, x4, x5, x6⟩ := c60
    exact ⟨x1, by rw [hone]; exact x2, by rw [setRet_accessible]; exact x3, by rw [setRet_accessible]; exact x4, x5,
      by rw [hfree]; exact x6⟩

end FvModexp.Amd64.ExpN
