import FvModexp.Proofs.Arm64.Exp.P2PreXTr
import FvModexp.Proofs.Arm64.Exp.P2PreX

/-!
# `buildPrecomputationWindowModPower2` (arm64): `X1J` → `trunc(x)` (agent infra)

From the pointer store of `powers[0]` (`0x1b55dc`): `powers[0].ptr = buf`, the reslice checks of `powers[0][:1:w]`,
`powers[0].len/cap = (1, w)` (now `PwD 0`: value `1 = p2Pow 0`), the bounds check of `powers[1]`, and the call
`powers[1].trunc(x, logM)` (`callTrX` → `JT`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jX1 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s)
    (hx6 : (s.regs 6).toNat = x) (hx7 : (s.regs 7).toNat = xl)
    (kT : JT impl R kc sqC mlC b L st pw pl lm x xl s) :
    X1J impl R kc sqC mlC b L st pw pl lm x xl s := by
  intro S bp L1 b1 hpc hsp h28 h29 h18 h3 h4 h5 h7 h8 h9 hc hd hone hb
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; exact hw
  have hpw48 := hf.pw48
  have hpwa : S.mem.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hwok := wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)
  have hnb0 : 8 ≤ 8 * NB pl lm := by have : 0 < NB pl lm := Nat.mul_pos (show 0 < pl + 1 by omega) hw1; omega
  have hbpw : pw + 24 * pl ≤ bp ∨ bp + 8 * NB pl lm ≤ pw := by
    have := wok_pw hwok hf.pwrt (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by omega) (a := pw) (n := 24 * pl)
      (Nat.le_refl _) (Nat.le_refl _) (by simp only; omega)
    simp only at this; omega
  have hone' : ((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1 |>.writeLE (pw + 8 + 8) 8 (W lm)).readLE bp 8 = 1 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hone
  obtain ⟨-, -, -, -, -, e5, -, e7, -, e9, e10, e11⟩ := hc.sl
  have f152 : S.mem.readLE (s.sp.toNat - 208 + 152) 8 = lm + 63 := by
    rw [show s.sp.toNat - 208 + 152 = s.sp.toNat - 56 by omega]; exact e7
  have f256 : S.mem.readLE (s.sp.toNat - 208 + 256) 8 = lm := by
    rw [show s.sp.toNat - 208 + 256 = s.sp.toNat + 48 by omega]; exact e5
  have f264 : S.mem.readLE (s.sp.toNat - 208 + 264) 8 = x := by
    rw [show s.sp.toNat - 208 + 264 = s.sp.toNat + 56 by omega, e9, hx6]
  have f272 : S.mem.readLE (s.sp.toNat - 208 + 272) 8 = xl := by
    rw [show s.sp.toNat - 208 + 272 = s.sp.toNat + 64 by omega, e10, hx7]
  have f280 : S.mem.readLE (s.sp.toNat - 208 + 280) 8 = (s.regs 8).toNat := by
    rw [show s.sp.toNat - 208 + 280 = s.sp.toNat + 72 by omega, e11]
  obtain ⟨t0, t1, t2⟩ := hd 1 (by omega) (by omega)
  have t0' : S.mem.readLE (pw + 24) 8 = bp + 8 * (1 * W lm) := t0
  have t1' : S.mem.readLE (pw + 24 + 8) 8 = W lm := t1
  have t2' : S.mem.readLE (pw + 40) 8 = 2 * W lm := t2
  have hsh : BitVec.ofNat 64 (lm + 63) >>> 6 = BitVec.ofNat 64 (W lm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : lm + 63 < 2 ^ 64 := by have := hpre.2.2.2.2.2.2.1; omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by simp only [W]; omega)]
  -- the context and `powers` after the three header stores
  have hc3 := ctx_own (ctx_own (ctx_own hc hf bp (a := pw) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩)
    hf 1 (a := pw + 8) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf (W lm) (a := pw + 8 + 8) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  have hr3 : ∀ a n, pw + 24 ≤ a →
      (((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (W lm)).readLE a n = S.mem.readLE a n :=
    fun a n h => by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hd0 : PwD (((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (W lm)) pw bp lm
      (natVal s.mem x xl) 0 := by
    have r0 : (((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (W lm)).readLE pw 8 = bp := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    have r8 : (((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (W lm)).readLE (pw + 8) 8 = 1 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    have r16 : (((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (W lm)).readLE (pw + 16) 8 =
        W lm := by
      rw [show pw + 16 = pw + 8 + 8 by omega, Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    simp only [PwD, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rw [r0, r8, r16]
    refine ⟨rfl, rfl, hw1, ?_, Or.inr ?_⟩
    · simp only [natVal, Nat.mul_one]; rw [hone']; rw [Exp.p2Pow]; simp
    · simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hone']; decide
  have hrs : RS0 R kc L st pw pl lm s (natVal s.mem x xl) bp
      (((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (W lm)) L1 b1 1 :=
    ⟨hc3, fun j hj => by rw [show j = 0 by omega]; exact hd0, fun j hj hjp => by
      obtain ⟨e0, e1, e2⟩ := hd j (by omega) hjp
      exact ⟨(hr3 _ _ (by omega)).trans e0, (hr3 _ _ (by omega)).trans e1, (hr3 _ _ (by omega)).trans e2⟩⟩
  clear hd hc hc3 hr3 hd0 hwok
  unfold Goal
  janus_run [f152, f256, f264, f272, f280, t0', t1', t2', hsh] until [1786000]
  refine callTrX hap hns hnf htr hkT haT hkc hpre kT (xc := (s.regs 8).toNat) hrs hb _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  all_goals janus_simp

end

end FvModexp.Arm64.P2Pre
