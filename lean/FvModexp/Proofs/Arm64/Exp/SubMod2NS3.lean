import FvModexp.Proofs.Arm64.Exp.SubMod2NCall

/-!
# `nat.subMod2N` (arm64): `J2` → `x.cmp(y)` → `z.sub(x, y)` + return, or `z.sub(y, x)` → `J3` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem cmp_neg {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
    (hlt : natVal m p l1 < natVal m q l2) :
    CmpSum.cmpRes l1 l2 (m.readLE p (8 * l1)) (m.readLE q (8 * l2)) = 18446744073709551615#64 := by
  have := (SubMod2N.cmp_lt_iff m p l1 q l2 h1 h2).2 hlt
  unfold CmpSum.cmpRes natVal at *
  rcases this with h | ⟨rfl, h⟩
  · rw [ite_eq_left_iff.2 (fun h' => absurd h h')]
  · simp [h]

theorem cmp_nonneg {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
    (hge : ¬ natVal m p l1 < natVal m q l2) :
    (CmpSum.cmpRes l1 l2 (m.readLE p (8 * l1)) (m.readLE q (8 * l2))).getLsbD 63 = false := by
  have h := mt (SubMod2N.cmp_lt_iff m p l1 q l2 h1 h2).1 hge
  unfold CmpSum.cmpRes natVal at *
  by_cases a : l1 < l2
  · exact absurd (Or.inl a) h
  rw [if_neg a]
  by_cases b' : l2 < l1
  · rw [if_pos b']; decide
  rw [if_neg b']
  have e : l1 = l2 := by omega
  rw [if_neg (fun c => h (Or.inr ⟨e, c⟩))]
  split <;> decide

theorem cmp_nonneg' {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
    (hge : ¬ natVal m p l1 < natVal m q l2) :
    ∃ v, v ≤ 1 ∧ CmpSum.cmpRes l1 l2 (m.readLE p (8 * l1)) (m.readLE q (8 * l2)) = BitVec.ofNat 64 v := by
  have h := mt (SubMod2N.cmp_lt_iff m p l1 q l2 h1 h2).1 hge
  unfold CmpSum.cmpRes natVal at *
  by_cases a : l1 < l2
  · exact absurd (Or.inl a) h
  rw [if_neg a]
  by_cases b' : l2 < l1
  · rw [if_pos b']; exact ⟨1, by omega, rfl⟩
  rw [if_neg b']
  have e : l1 = l2 := by omega
  rw [if_neg (fun c => h (Or.inr ⟨e, c⟩))]
  split
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨0, by omega, rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- from the entry of `x'.cmp(y')` (`+0x1ec`) -/
theorem s3c (impl : List Segment) (hap : ImplApart Extracted.program impl) {R : RtInv} (hsub : SubHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (k3 : J3 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (S : State) {l1 p2 l2 c2 : Nat} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hpc : S.pc = BitVec.ofNat 64 1782608) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18) (h30 : S.regs 30 = BitVec.ofNat 64 (1805584 + 4 * 124))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 l1)
    (h3 : S.regs 3 = BitVec.ofNat 64 p2) (h4 : S.regs 4 = BitVec.ofNat 64 l2)
    (hfw : Fw s S.mem zp zl zc yp n) (r16 : S.mem.readLE (s.sp.toNat - 16) 8 = zp)
    (r40 : S.mem.readLE (s.sp.toNat - 40) 8 = l1) (r32 : S.mem.readLE (s.sp.toNat - 32) 8 = zc)
    (r24 : S.mem.readLE (s.sp.toNat - 24) 8 = p2) (r56 : S.mem.readLE (s.sp.toNat - 56) 8 = l2)
    (r48 : S.mem.readLE (s.sp.toNat - 48) 8 = c2) (hrt : Rt R b L s zp zc n 2 S.mem L2 b2)
    (hv1 : natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n) (hn1 : NatNorm S.mem zp l1) (hW1 : l1 ≤ W n)
    (hv2 : natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n) (hn2 : NatNorm S.mem p2 l2) (hW2 : l2 ≤ W n)
    (hlc2 : l2 ≤ c2) (hc2 : c2 < 2 ^ 40)
    (hacc2 : S.mem.accessible p2 (8 * l2) false = true) (h482 : p2 + 8 * l2 ≤ 2 ^ 48) (hh2 : Held R L2 p2 (8 * l2))
    (hw2 : p2 + 8 * l2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p2) (hzp2 : Apart zp (8 * zc) p2 (8 * l2)) :
    Goal impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -, -, -, -, -, hn1', -, hzl, hW, hzc, -, -,
    -, -, hzlive, hzw, hzg, -⟩ := id hpre
  simp only [W] at hW hW1 hW2
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw hg3 hga
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hzh : Held R L2 zp (8 * zc) := (hrt.2.2.2.2.2.2 (by omega)).2.1
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hacc1 : S.mem.accessible zp (8 * l1) false = true :=
    Memory.accessible_sub _ (hrt.2.2.2.2.2.2 (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hgv : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hrt.2.1.readLE _ _ ?_
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hzg hga
    exact ⟨⟨hgrt, by omega, by omega⟩, by omega⟩
  have tg : (S.regs 28).toNat = (s.regs 28).toNat := by rw [h28]
  refine cmpCall hpc (CmpW.pre_of (sp := s.sp.toNat - 144) (g := (s.regs 28).toNat) hsp
    (h28.trans (Expmc.bv_ofNat_toNat _).symm) h30 h0 h1 h3 h4 (by decide) (by decide) (by omega) (by omega) (by omega)
    (Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega)) hg1 (by rw [hrt.2.1.accessible]; exact hg2)
    (by rw [hgv]; omega) (Or.inr ⟨by omega, hacc1, by unfold Apart; omega⟩)
    (Or.inr ⟨by omega, hacc2, by unfold Apart; omega⟩)) fun S' hpc' hsp' hr0 h18' h28' h29' hF' hrg' => ?_
  rw [h0, h1, h3, h4, tN (show zp < 2 ^ 64 by omega), tN (show l1 < 2 ^ 64 by omega), tN (show p2 < 2 ^ 64 by omega),
    tN (show l2 < 2 ^ 64 by omega)] at hr0
  have hs4 : 4608 ≤ s.sp.toNat := by omega
  obtain ⟨hcfA, hcfG⟩ := cmp_frame (R := R) hs4 hspT hF'
  have hrt' : Rt R b L s zp zc n 2 S'.mem L2 b2 := rt_stk hpre hrt hcfA hrg'
  have hfw' : Fw s S'.mem zp zl zc yp n :=
    fw_call (zr := ((0 : Nat), (0 : Nat))) hs4 hout (by omega) (Or.inr rfl) (by omega) (by omega) hfw hcfG
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw'
  have hfwS := hfw
  obtain ⟨-, -, g3, g4, g5, -, -⟩ := hfwS
  have x152 : S.mem.readLE (s.sp.toNat - 144 + 152) 8 = zp := by rw [show s.sp.toNat - 144 + 152 = s.sp.toNat + 8 by omega]; exact g3
  have x160 : S.mem.readLE (s.sp.toNat - 144 + 160) 8 = zl := by rw [show s.sp.toNat - 144 + 160 = s.sp.toNat + 16 by omega]; exact g4
  have x168 : S.mem.readLE (s.sp.toNat - 144 + 168) 8 = zc := by rw [show s.sp.toNat - 144 + 168 = s.sp.toNat + 24 by omega]; exact g5
  have x120 : S.mem.readLE (s.sp.toNat - 144 + 120) 8 = p2 := by rw [show s.sp.toNat - 144 + 120 = s.sp.toNat - 24 by omega]; exact r24
  have x88 : S.mem.readLE (s.sp.toNat - 144 + 88) 8 = l2 := by rw [show s.sp.toNat - 144 + 88 = s.sp.toNat - 56 by omega]; exact r56
  have x96 : S.mem.readLE (s.sp.toNat - 144 + 96) 8 = c2 := by rw [show s.sp.toNat - 144 + 96 = s.sp.toNat - 48 by omega]; exact r48
  have x128 : S.mem.readLE (s.sp.toNat - 144 + 128) 8 = zp := by rw [show s.sp.toNat - 144 + 128 = s.sp.toNat - 16 by omega]; exact r16
  have x104 : S.mem.readLE (s.sp.toNat - 144 + 104) 8 = l1 := by rw [show s.sp.toNat - 144 + 104 = s.sp.toNat - 40 by omega]; exact r40
  have x112 : S.mem.readLE (s.sp.toNat - 144 + 112) 8 = zc := by rw [show s.sp.toNat - 144 + 112 = s.sp.toNat - 32 by omega]; exact r32
  rw [hspT] at hF'
  have rdl : ∀ a, s.sp.toNat - 56 ≤ a → a + 8 ≤ s.sp.toNat - 8 → S'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hF'.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]; omega
  have q16 := (rdl _ (by omega) (by omega)).trans r16
  have q40 := (rdl _ (by omega) (by omega)).trans r40
  have q32 := (rdl _ (by omega) (by omega)).trans r32
  have q24 := (rdl _ (by omega) (by omega)).trans r24
  have q56 := (rdl _ (by omega) (by omega)).trans r56
  have q48 := (rdl _ (by omega) (by omega)).trans r48
  have hzA : Outside zp (8 * l1) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  have hyA : Outside p2 (8 * l2) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  have hv1' := (natVal_frame hcfA hzA).trans hv1
  have hv2' := (natVal_frame hcfA hyA).trans hv2
  have hn1' := natNorm_frame hcfA hzA hn1
  have hn2' := natNorm_frame hcfA hyA hn2
  have hacc1' : S'.mem.accessible zp (8 * l1) false = true := by rw [hcfA.accessible]; exact hacc1
  have hacc2' : S'.mem.accessible p2 (8 * l2) false = true := by rw [hcfA.accessible]; exact hacc2
  have hacc' : S'.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hcfA.accessible]; exact hacc
  have hsp1 : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) := hsp'.trans hsp
  have hzh1 : Held R L2 zp (8 * l1) := hzh.sub (Nat.le_refl _) (by omega)
  by_cases hlt : natVal S.mem zp l1 < natVal S.mem p2 l2
  · have hR : S'.regs 0 = 18446744073709551615#64 := hr0.trans (cmp_neg hn1 hn2 hlt)
    have hll := (SubMod2N.cmp_lt_iff S.mem zp l1 p2 l2 hn1 hn2).2 hlt
    janus_run [hR, x152, x160, x168, x120, x88, x96, x128, x104, x112] until [1781872]
    refine subCall hap hsub (zp := zp) (zl := zl) (zc := zc) (xp := p2) (xl := l2) (xc := c2) (yp := zp) (yl := l1)
      (yc := zc) (sp' := s.sp.toNat - 144) (g := (s.regs 28).toNat) (M := S'.mem)
      (ra_of hap (by decide) 135 (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
      (subPre_of hpre hrt' ?_ ?_ ?_ (by omega) (by rw [hv1', hv2']; omega) hlc2 (by omega) hc2 hzc hW2 (Or.inr hzp2)
        (Or.inl rfl) hacc2' h482 hh2 hn2' (by omega) hacc1' (by omega) hzh1 hn1' (by omega))
      fun s'' p' n' c' L3 b3 hpc'' hsp'' h28'' h29'' h18'' hrg'' e0 e1 e2 hv hnorm hlc hln hLE hb3 hinv3 hlive3 hor3
        hF3 hLF3 hreuse hc40 => ?qK
    case qK =>
      obtain ⟨rfl, rfl⟩ := hreuse (by omega)
      refine k3 s'' n' L3 b3 hpre (hpc''.trans rfl) hsp'' ?_ ?_ e0 e1 e2
        (fw_call hs4 hout hzw (Or.inl rfl) (by omega) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ hF3)
        (rt_call hrt' hs4 (by omega) (by omega) (Or.inl rfl) hrg'' hF3 hLF3 hLE hb3 (makeCost_le_w (by simp only [W]; omega)) hinv3
          hlive3) (by rw [← hv1, ← hv2]; exact hlt) (by rw [hv, hv1', hv2']) hnorm (by simp only [W]; omega)
      · rw [h28'']; janus_simp
      · rw [h18'']; janus_simp
    all_goals try janus_simp
  · obtain ⟨v, hv01, hcv⟩ := cmp_nonneg' hn1 hn2 hlt
    have hR : S'.regs 0 = BitVec.ofNat 64 v := hr0.trans hcv
    have h63 : (BitVec.ofNat 64 v).getLsbD 63 = false := by
      simp only [BitVec.getLsbD_ofNat]; simp [Nat.testBit, Nat.shiftRight_eq_div_pow]; omega
    have hll := mt (SubMod2N.cmp_lt_iff S.mem zp l1 p2 l2 hn1 hn2).1 hlt
    janus_run [hR, h63, x152, x160, x168, x120, x88, x96, x128, x104, x112] until [1781872]
    refine subCall hap hsub (zp := zp) (zl := zl) (zc := zc) (xp := zp) (xl := l1) (xc := zc) (yp := p2) (yl := l2)
      (yc := c2) (sp' := s.sp.toNat - 144) (g := (s.regs 28).toNat) (M := S'.mem)
      (ra_of hap (by decide) 147 (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (subPre_of hpre hrt' ?_ ?_ ?_ (by omega) (by rw [hv1', hv2']; omega) (by omega) hlc2 hzc hc2 hW1 (Or.inl rfl)
        (Or.inr hzp2) hacc1' (by omega) hzh1 hn1' (by omega) hacc2' h482 hh2 hn2' (by omega))
      fun s'' p' n' c' L3 b3 hpc'' hsp'' h28'' h29'' h18'' hrg'' e0 e1 e2 hv hnorm hlc hln hLE hb3 hinv3 hlive3 hor3
        hF3 hLF3 hreuse hc40 => ?qK
    case qK =>
      obtain ⟨rfl, rfl⟩ := hreuse (by omega)
      have hl4 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hl48 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hfw3 := fw_call hs4 hout hzw (Or.inl rfl) (by omega) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ hF3
      have hrt3 := rt_call hrt' hs4 (by omega) (by omega) (Or.inl rfl) hrg'' hF3 hLF3 hLE hb3
        (makeCost_le_w (by simp only [W]; omega)) hinv3 hlive3
      obtain ⟨u1, u2, -⟩ := hfw3
      janus_run [u1, u2]
      refine ⟨⟨?_, ?_⟩, post_of hrt3 (by omega) ?_ ?_ ?_ ?_ hnorm hlc hc40 hlive3 (Or.inl ⟨rfl, rfl⟩)⟩
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, tN (by omega)]; simp only [BitVec.toNat_ofNat]; omega
      · rw [show s.sp.toNat - 144 - 8 = s.sp.toNat - 152 by omega, hfw.2.1, Expmc.bv_ofNat_toNat]
      · janus_simp
      · janus_simp
      · janus_simp
      · rw [hv, hv1', hv2']
        exact (SubMod2N.ge_branch _ _ _ (by rw [← hv1, ← hv2]; omega)).symm
    all_goals try janus_simp

end FvModexp.Arm64.SubMod2N

namespace FvModexp.Arm64.SubMod2N

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s3 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (hsub : SubHypR impl R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (k3 : J3 impl R b L op zp zl zc yp yl yc n s) : J2 impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 p2 l2 c2 L2 b2 hpre hpc hsp h28 h18 h3 h4 h5 h6 h7 h8 hfw r16 r40 r32 hrt hv1 hn1 hW1 hv2 hn2 hW2 hlc2 hc2
    hacc2 h482 hh2 hw2 hzp2
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -, -, -, -, -, hn1', -, hzl, hW, hzc, -, -,
    -, -, hzlive, hzw, hzg, -⟩ := id hpre
  simp only [W] at hW hW1 hW2
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw hg3 hga
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hzA : Outside zp (8 * l1) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  have hyA : Outside p2 (8 * l2) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw
  unfold Goal
  janus_run until [1782608]
  refine s3c impl hap hsub k3 hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (rt_stk hpre hrt ?_ ?_) ?_ ?_ hW1 ?_ ?_
    hW2 hlc2 hc2 ?_ h482 hh2 hw2 hzp2
  all_goals try janus_simp
  · refine fw_loc (M := S.mem) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_
    janus_frame
  · exact r16
  · exact r40
  · exact r32
  · simp only [winA, K, A]; janus_frame
  · exact hv1
  · refine natNorm_frame (m := S.mem) (rs := winA s K A) ?_ hzA hn1
    simp only [winA, K, A]; janus_frame
  · exact hv2
  · refine natNorm_frame (m := S.mem) (rs := winA s K A) ?_ hyA hn2
    simp only [winA, K, A]; janus_frame
  · exact hacc2

end FvModexp.Arm64.SubMod2N
