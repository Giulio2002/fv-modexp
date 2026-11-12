import FvModexp.Proofs.Arm64.Exp.ModInvPostSub

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): final round, `S5` → `z = z.subMod2N(z, zz, n)` → return (agent infra)

`0x1b7064`: `zz` and `n` reloaded, `subMod2N` call at `0x1b7080`, returns to `0x1b7084`:
`MOVD -8(RSP), R29; MOVD.P 240(RSP), R30; RET` (nat.go:1339-1340). The result is `z` itself (`subMod2N` keeps `z`'s
array, `cap z ≥ numWords + 1`), its value the model's (`final_step`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

section
variable {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the post from the round facts at the final memory -/
theorem post_mid (s' : State) {L' : List (Nat × Nat)} {b' p l c q ql qc : Nat}
    (mid : Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l c q ql qc)
    (e0 : (s'.regs 0).toNat = p) (e1 : (s'.regs 1).toNat = l) (e2 : (s'.regs 2).toNat = c)
    (hv : natVal s'.mem p l = val (natVal s.mem xp xl) n) (hn : NatNorm s'.mem p l)
    (hb : b - cost sqrC mulC n ≤ b') :
    Post R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨-, ⟨-, hF, hLF, hLE, hinv, hstk, hlen, hstw⟩, ⟨hc40, -, hlive, hold, -⟩, -, -, hlc, -⟩ := mid
  exact ⟨p, l, c, e0, e1, e2, hv, hn, hlc, hc40, L', b', hLE, hb, hinv, hlive, hold, ⟨hstk, hlen, hstw⟩, hF, hLF⟩

/-- the final budget: at most `numWords` rounds before the final one -/
theorem bud_final {j b b1 b' : Nat} (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n)
    (hb : b - spent sqrC mulC n j - P5 sqrC mulC n ≤ b1) (hbud' : b1 - SubMod2N.cost n ≤ b') :
    b - cost sqrC mulC n ≤ b' := by
  have hj : j - 1 < NW n := Nat.lt_trans (Nat.lt_two_pow_self) hjn
  have hm : (j - 1) * roundCost sqrC mulC n + roundCost sqrC mulC n ≤ (NW n + 1) * roundCost sqrC mulC n := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  simp only [spent, cost, roundCost, P5, P4, P3, P2, P1] at hb hm ⊢
  omega

end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- after `subMod2N` returns (`0x1b7084`): restore FP / LR, return -/
theorem retF5 {impl : List Segment} {R : RtInv} {kc : Nat} {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 : Nat} (s' : State)
    (hmid : Mid R kc L s zp zc st xp xl xc n s'.mem L1 b1 p l c q ql qc)
    (hv : natVal s'.mem p l = val (natVal s.mem xp xl) n) (hn : NatNorm s'.mem p l)
    (hb : b - cost sqrC mulC n ≤ b1)
    (hpc : s'.pc = BitVec.ofNat 64 1798276) (hsp : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 240))
    (h28 : s'.regs 28 = s.regs 28) (h18 : s'.regs 18 = s.regs 18)
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h1 : s'.regs 1 = BitVec.ofNat 64 l) (h2 : s'.regs 2 = BitVec.ofNat 64 c) :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  have hK := sp_K hpre
  have hp64 : p < 2 ^ 64 := hmid.2.2.1.2.1
  have hc40 : c < 2 ^ 40 := hmid.2.2.1.1
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  have f1 : s'.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat := hmid.1.1.1
  have f2 : s'.mem.readLE (s.sp.toNat - 240 - 8) 8 = (s.regs 29).toNat := by
    rw [show s.sp.toNat - 240 - 8 = s.sp.toNat - 248 by omega]; exact hmid.1.1.2
  unfold Goal
  janus_run [f1, f2]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, post_mid _ hmid ?_ ?_ ?_ hv hn hb⟩
  · have hsl := s.sp.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals janus_simp
  all_goals omega

set_option maxHeartbeats 4000000 in
/-- the continuation after `subMod2N` (small context): value and budget, then `retF5` -/
theorem contF5 {impl : List Segment} {R : RtInv} {kc : Nat} {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} {j : Nat}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {M : Memory} {p l c q ql Zv b1 : Nat}
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hex : ExF n j M)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hv : natVal M p l = Zv * 2)
    (hvq : natVal M q ql = Zv * Zv % 2 ^ eF n j * natVal s.mem xp (min (kF n j) xl) % 2 ^ eF n j)
    (hb : b - spent sqrC mulC n j - P5 sqrC mulC n ≤ b1) {qc : Nat}
    (s' : State) (l' : Nat) (L' : List (Nat × Nat)) (b' : Nat) (f0 : s'.pc = BitVec.ofNat 64 1798276)
    (f1 : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (f2 : s'.regs 28 = s.regs 28) (f4 : s'.regs 18 = s.regs 18)
    (g0 : s'.regs 0 = BitVec.ofNat 64 p) (g1 : s'.regs 1 = BitVec.ofNat 64 l') (g2 : s'.regs 2 = BitVec.ofNat 64 c)
    (mid2 : Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l' c q ql qc)
    (hv' : natVal s'.mem p l' = Exp.subMod2N (natVal M p l) (natVal M q ql) n)
    (hn' : NatNorm s'.mem p l') (hbud' : b1 - SubMod2N.cost n ≤ b') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  simp only [eF, kF] at hvq
  have hval : natVal s'.mem p l' = val (natVal s.mem xp xl) n := by
    rw [hv', hv, hvq]
    exact final_step hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hn hex hcong
  exact retF5 hpre s' mid2 hval hn' (bud_final hj1 hjn hb hbud') f0 f1 f2 f4 g0 g1 g2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF5 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains SubMod2N.fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubMod2N.SubHypR impl R) (hadd : SubMod2N.AddHypR impl R) {kc : Nat} (hkc : 4608 ≤ kc)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat}
    {s : State} :
    S5 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1798244 (ExF n) (eF n) (kF n) := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hqs h0 h1 h2 hv hnz hl hvq hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have r216 : S.mem.readLE (s.sp.toNat - 240 + 216) 8 = q := by
    rw [show s.sp.toNat - 240 + 216 = s.sp.toNat - 24 by omega]; exact hqs.1
  have r112 : S.mem.readLE (s.sp.toNat - 240 + 112) 8 = ql := by
    rw [show s.sp.toNat - 240 + 112 = s.sp.toNat - 128 by omega]; exact hqs.2.1
  have r120 : S.mem.readLE (s.sp.toNat - 240 + 120) 8 = qc := by
    rw [show s.sp.toNat - 240 + 120 = s.sp.toNat - 120 by omega]; exact hqs.2.2
  have r304 : S.mem.readLE (s.sp.toNat - 240 + 304) 8 = n := by
    rw [show s.sp.toNat - 240 + 304 = s.sp.toNat + 64 by omega]; exact hmidB.h.1.2.2.2.2.2.1
  have hbo : SubMod2N.cost n ≤ b1 :=
    bud_ok hb hbud (m := SubMod2N.cost n) (by simp only [roundCost, P5, P4, P3, P2, P1]; omega) (Nat.le_refl _)
  have hpre := hpreB.h
  have hK' := contF5 (impl := impl) (qc := qc) hpre hn hj1 hjn hex hcong hv hvq hb
  clear hcong hv hvq hbud hjn hex
  unfold Goal
  janus_run [r216, r112, r120, r304] until [1805584]
  refine callSub hap hns hnf hkT haT htr hsub hadd hkc hpre hmidB.h (e := n) (by omega) (Nat.le_refl _) hl hql hnz hnq
    hbo (pcv := 1798276) ⟨by decide, by decide⟩ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun s' l' L' b' f0 f1 f2 f4 g0 g1 g2 mid2 hv' hn' _ _ hbud' _ =>
      hK' s' l' L' b' f0 f1 f2 f4 g0 g1 g2 mid2 hv' hn' hbud')
  all_goals janus_simp

end FvModexp.Arm64.ModInv
