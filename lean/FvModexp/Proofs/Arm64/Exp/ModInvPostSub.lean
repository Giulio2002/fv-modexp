import FvModexp.Proofs.Arm64.Exp.ModInvSegC

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `z = z.subMod2N(z, zz, e)` (agent infra)

`callSub`: at `subMod2N`'s entry (`z` in `X0 … X5`, `zz` in `X6 … X8`, `e` in `X9`), with the round facts: the call
through `SubMod2N.full`; the continuation gets the round facts at the return (`z` kept in place: `cap z ≥ ⌈e/64⌉ + 1`),
its value, and the budget step.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callSub {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains SubMod2N.fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : TruncHyp impl R ns stkT aboveT)
    (hsub : SubMod2N.SubHypR impl R) (hadd : SubMod2N.AddHypR impl R) {kc : Nat} (hkc : 4608 ≤ kc)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat}
    {s : State} (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {e : Nat} (he1 : 1 ≤ e) (he : e ≤ n)
    (hl : l ≤ NW n + 2) (hql : ql ≤ NW n) (hnz : NatNorm M p l) (hnq : NatNorm M q ql)
    (hb : SubMod2N.cost e ≤ b1) {pcv : Nat} (hpcv : pcv < 2 ^ 48 ∧ pcv % 4 = 0)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1805584) (h30 : S'.regs 30 = BitVec.ofNat 64 pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 p) (h1 : S'.regs 1 = BitVec.ofNat 64 l) (h2 : S'.regs 2 = BitVec.ofNat 64 c)
    (h3 : S'.regs 3 = BitVec.ofNat 64 p) (h4 : S'.regs 4 = BitVec.ofNat 64 l) (h5 : S'.regs 5 = BitVec.ofNat 64 c)
    (h6 : S'.regs 6 = BitVec.ofNat 64 q) (h7 : S'.regs 7 = BitVec.ofNat 64 ql)
    (h8 : S'.regs 8 = BitVec.ofNat 64 qc) (h9 : S'.regs 9 = BitVec.ofNat 64 e) {ret : BitVec 64} {Q : State → Prop}
    (K : ∀ (s' : State) (l' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.pc = BitVec.ofNat 64 pcv →
      s'.sp = S'.sp → s'.regs 28 = S'.regs 28 → s'.regs 29 = S'.regs 29 → s'.regs 18 = S'.regs 18 →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 l' → s'.regs 2 = BitVec.ofNat 64 c →
      Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l' c q ql qc →
      natVal s'.mem p l' = Exp.subMod2N (natVal M p l) (natVal M q ql) e → NatNorm s'.mem p l' →
      natVal s'.mem q ql = natVal M q ql → NatNorm s'.mem q ql →
      b1 - SubMod2N.cost e ≤ b' → SlotsKept s M s'.mem → ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S' Q := by
  have hK := sp_K hpre
  have hS' := sp'_eq hsp
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnc : NW n + 1 ≤ c := hmid.2.2.2.2.2.2.2.1
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  have hc40 : c < 2 ^ 40 := hmid.2.2.1.1
  have hp64 : p < 2 ^ 64 := hmid.2.2.1.2.1
  have hq64 : q < 2 ^ 64 := hmid.2.2.2.1.2.1
  have hqc40 : qc < 2 ^ 40 := hmid.2.2.2.1.1
  have hW : SubMod2N.W e + 1 ≤ c := by simp only [SubMod2N.W, NW] at hnc ⊢; omega
  obtain ⟨op, hone⟩ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ReachesRet.call_regions (SubMod2N.full impl hap R hns hnf hkT haT htr hsub hadd b1 L1 op p l c q ql qc e)
    hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hpost⟩ hreg => ?_
  · refine subPre_at hpre hkc hmid hone hsp h28 hm he1 (by omega) (by omega) (by simp only [NW] at hl; omega)
      (by simp only [NW] at hql; omega) hnz hnq hb ?_
    have := hpcv.1; have := hpcv.2
    rw [h30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show pcv < 2 ^ 64 by omega)]; exact ⟨by omega, by omega⟩
  · obtain ⟨p', l', c', f0, f1, f2, hv, hn', hlc', hc40', L', b', hLE, hbud, hinv, hlive, -, hF, hLF, hkeep⟩ := hpost
    obtain ⟨rfl, rfl⟩ := hkeep hW
    rw [hm] at hF hLF hreg hv
    rw [h28] at hinv
    obtain ⟨hF2, hLF2, hsb, se0, se2⟩ := nostk hpre hmid.2.1 hS' hkc (by decide) hmid.2.2.1 hF hLF hLE
    obtain ⟨mid2, hqv, hsl⟩ := after_z hpre hkc hmid hS' hkc (by decide) hreg hF2 hLF2 hLE hinv hsb hlive hc40' hp64
      (Or.inl ⟨rfl, rfl⟩) (fun h => absurd ⟨rfl, rfl⟩ h) hlc' hnc
    have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
    refine K s' l' L' b' (hr.trans h30) e1 e2 e3 e4 (by rw [← f0, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [← f1, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [← f2, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      mid2 hv hn' (hqv ql hqlc) ?_ hbud hsl
    exact norm_keep hqv hqlc hnq

end FvModexp.Arm64.ModInv
