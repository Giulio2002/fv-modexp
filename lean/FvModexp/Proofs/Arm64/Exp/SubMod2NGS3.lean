import FvModexp.Proofs.Arm64.Exp.SubMod2NGC

/-!
# `nat.subMod2N` (arm64), general form: `J2G` → `x.cmp(y)` → `z.sub(x, y)` + return, or `z.sub(y, x)` → `J3G`
(empty-tolerant `SubHypR0`; the result of `z.sub(y, x)` in `z`'s array or a fresh one) (agent infra)
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem cmpG_neg {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
    (hlt : natVal m p l1 < natVal m q l2) :
    CmpSum.cmpRes l1 l2 (m.readLE p (8 * l1)) (m.readLE q (8 * l2)) = 18446744073709551615#64 := by
  have := (SubMod2N.cmp_lt_iff m p l1 q l2 h1 h2).2 hlt
  unfold CmpSum.cmpRes natVal at *
  rcases this with h | ⟨rfl, h⟩
  · rw [ite_eq_left_iff.2 (fun h' => absurd h h')]
  · simp [h]

theorem cmpG_nonneg {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
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

theorem cmpG_nonneg' {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
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
set_option maxHeartbeats 64000000 in
/-- from the entry of `x'.cmp(y')` (`+0x1ec`) -/
theorem s3Gc (impl : List Segment) (hap : ImplApart Extracted.program impl) {R : RtInv} (hsub : SubHypR0 impl R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (k3 : J3G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
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
    (hlc1 : l1 ≤ zc)
    (hv2 : natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n) (hn2 : NatNorm S.mem p2 l2) (hW2 : l2 ≤ W n)
    (hlc2 : l2 ≤ c2) (hc2 : c2 < 2 ^ 40) (hp2 : p2 < 2 ^ 64)
    (hy2 : 0 < l2 → S.mem.accessible p2 (8 * l2) false = true ∧ p2 + 8 * l2 ≤ 2 ^ 48 ∧ Held R L2 p2 (8 * l2) ∧
      (p2 + 8 * l2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p2) ∧ (0 < zc → Apart zp (8 * zc) p2 (8 * l2))) :
    GoalG impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -, -, -, -, -, hn1', -, hzl, ⟨hz64, -⟩, hzc, -, -,
    -, -, hzlive, hzw, hzg, -⟩ := id hpre
  simp only [W] at hW1 hW2
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw hg3 hga
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hz48 : 0 < l1 → zp + 8 * zc ≤ 2 ^ 48 := fun h => (hzlive (by omega)).2.2.2
  have hacc1 : 0 < l1 → S.mem.accessible zp (8 * l1) false = true := fun h =>
    Memory.accessible_sub _ (hrt.2.2.2.2.2.2 (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hzh1 : 0 < l1 → Held R L2 zp (8 * l1) := fun h =>
    (hrt.2.2.2.2.2.2 (by omega)).2.1.sub (Nat.le_refl _) (by omega)
  have hgv : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hrt.2.1.readLE _ _ ?_
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hzg hga
    exact ⟨⟨hgrt, by omega, by omega⟩, by omega⟩
  have hcx : l1 = 0 ∨ (zp + 8 * l1 ≤ 2 ^ 48 ∧ S.mem.accessible zp (8 * l1) false = true ∧
      Apart zp (8 * l1) (s.sp.toNat - 144 - 24) 64) := by
    rcases Nat.eq_zero_or_pos l1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by have := hz48 h; omega, hacc1 h, by unfold Apart; omega⟩
  have hcy : l2 = 0 ∨ (p2 + 8 * l2 ≤ 2 ^ 48 ∧ S.mem.accessible p2 (8 * l2) false = true ∧
      Apart p2 (8 * l2) (s.sp.toNat - 144 - 24) 64) := by
    rcases Nat.eq_zero_or_pos l2 with h | h
    · exact Or.inl h
    · obtain ⟨a1, a2, -, a4, -⟩ := hy2 h
      exact Or.inr ⟨a2, a1, by unfold Apart; omega⟩
  refine cmpCall hpc (CmpW.pre_of (sp := s.sp.toNat - 144) (g := (s.regs 28).toNat) hsp
    (h28.trans (Expmc.bv_ofNat_toNat _).symm) h30 h0 h1 h3 h4 (by decide) (by decide) (by omega) (by omega) (by omega)
    (Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega)) hg1 (by rw [hrt.2.1.accessible]; exact hg2)
    (by rw [hgv]; omega) hcx hcy) fun S' hpc' hsp' hr0 h18' h28' h29' hF' hrg' => ?_
  rw [h0, h1, h3, h4, tN hz64, tN (show l1 < 2 ^ 64 by omega), tN hp2, tN (show l2 < 2 ^ 64 by omega)] at hr0
  have hs4 : 4608 ≤ s.sp.toNat := by omega
  obtain ⟨hcfA, hcfG⟩ := cmp_frame (R := R) hs4 hspT hF'
  have hrt' : Rt R b L s zp zc n 2 S'.mem L2 b2 := rtG_stk hpre hrt hcfA hrg'
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
  have hzA : Outside zp (8 * l1) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  have hv1' := (natVal_frame hcfA hzA).trans hv1
  have hn1' := natNorm_frame hcfA hzA hn1
  have hv2' : natVal S'.mem p2 l2 = natVal s.mem yp yl % 2 ^ n := by
    rcases Nat.eq_zero_or_pos l2 with h | h
    · subst h; rw [← hv2]; rfl
    · have := (hy2 h).2.2.2.1
      exact (natVal_frame hcfA (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)).trans hv2
  have hn2' : NatNorm S'.mem p2 l2 := by
    rcases Nat.eq_zero_or_pos l2 with h | h
    · exact Or.inl h
    · have := (hy2 h).2.2.2.1
      exact natNorm_frame hcfA (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega) hn2
  have hsp1 : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) := hsp'.trans hsp
  have hx1 : 0 < l1 → S'.mem.accessible zp (8 * l1) false = true ∧ zp + 8 * l1 ≤ 2 ^ 48 ∧ Held R L2 zp (8 * l1) ∧
      (zp + 8 * l1 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ zp) := fun h =>
    ⟨by rw [hcfA.accessible]; exact hacc1 h, by have := hz48 h; omega, hzh1 h, by omega⟩
  have hx2 : 0 < l2 → S'.mem.accessible p2 (8 * l2) false = true ∧ p2 + 8 * l2 ≤ 2 ^ 48 ∧ Held R L2 p2 (8 * l2) ∧
      (p2 + 8 * l2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ p2) := fun h => by
    obtain ⟨a1, a2, a3, a4, -⟩ := hy2 h
    exact ⟨by rw [hcfA.accessible]; exact a1, a2, a3, by omega⟩
  by_cases hlt : natVal S.mem zp l1 < natVal S.mem p2 l2
  · have hR : S'.regs 0 = 18446744073709551615#64 := hr0.trans (cmpG_neg hn1 hn2 hlt)
    have hll := (SubMod2N.cmp_lt_iff S.mem zp l1 p2 l2 hn1 hn2).2 hlt
    janus_run [hR, x152, x160, x168, x120, x88, x96, x128, x104, x112] until [1781872]
    refine subCall0 hap hsub (zp := zp) (zl := zl) (zc := zc) (xp := p2) (xl := l2) (xc := c2) (yp := zp) (yl := l1)
      (yc := zc) (sp' := s.sp.toNat - 144) (g := (s.regs 28).toNat) (M := S'.mem) (bx39 := by omega)
      (ra_of hap (by decide) 135 (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
      (subPre0_of hpre hrt' (Nat.le_refl _) ?_ ?_ ?_ (by omega) (by rw [hv1', hv2']; rw [← hv1, ← hv2]; omega) hlc2
        hlc1 hc2 hzc hW2 hp2 hz64 (fun hz h => Or.inr ((hy2 h).2.2.2.2 hz)) (fun _ _ => Or.inl rfl) hx2 hn2' hx1 hn1')
      fun s'' p' n' c' L3 b3 hpc'' hsp'' h28'' h29'' h18'' hrg'' e0 e1 e2 hv hnorm hlc hln hLE hb3 hinv3 hlive3 hor3
        hF3 hLF3 hreuse hc40 => ?qK
    case qK =>
      refine k3 s'' p' n' c' L3 b3 hpre (hpc''.trans rfl) hsp'' ?_ ?_ e0 e1 e2
        (fw_call hs4 hout hzw (Or.inl rfl) (by omega) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ hF3)
        (rt_call hrt' hs4 (by omega) (by omega) (Or.inl rfl) hrg'' hF3 hLF3 hLE hb3 (makeCost_le_w (by simp only [W]; omega)) hinv3
          (fun hc => ?_)) hlive3 (by rcases hor3 with h | ⟨h1, h2⟩; exact Or.inl h; exact Or.inr ⟨h1, fresh_of hrt'.2.2.2.1 h2⟩)
        hc40 hlc (fun hW => hreuse (by simp only [W] at hW; omega))
        (by rw [← hv1, ← hv2]; exact hlt) (by rw [hv, hv1', hv2']) hnorm (by simp only [W]; omega)
      · rw [h28'']; janus_simp
      · rw [h18'']; janus_simp
      · obtain ⟨c1, c2, c3, c4⟩ := hrt'.2.2.2.2.2.2 hc
        exact ⟨c1, hLE.held c2, by rw [hF3.accessible]; exact c3, c4⟩
    all_goals try janus_simp
  · obtain ⟨v, hv01, hcv⟩ := cmpG_nonneg' hn1 hn2 hlt
    have hR : S'.regs 0 = BitVec.ofNat 64 v := hr0.trans hcv
    have h63 : (BitVec.ofNat 64 v).getLsbD 63 = false := by
      simp only [BitVec.getLsbD_ofNat]; simp [Nat.testBit, Nat.shiftRight_eq_div_pow]; omega
    have hll := mt (SubMod2N.cmp_lt_iff S.mem zp l1 p2 l2 hn1 hn2).1 hlt
    janus_run [hR, h63, x152, x160, x168, x120, x88, x96, x128, x104, x112] until [1781872]
    refine subCall0 hap hsub (zp := zp) (zl := zl) (zc := zc) (xp := zp) (xl := l1) (xc := zc) (yp := p2) (yl := l2)
      (yc := c2) (sp' := s.sp.toNat - 144) (g := (s.regs 28).toNat) (M := S'.mem) (bx39 := by omega)
      (ra_of hap (by decide) 147 (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (subPre0_of hpre hrt' (Nat.le_refl _) ?_ ?_ ?_ (by omega) (by rw [hv1', hv2']; rw [← hv1, ← hv2]; omega) hlc1 hlc2
        hzc hc2 hW1 hz64 hp2 (fun _ _ => Or.inl rfl) (fun hz h => Or.inr ((hy2 h).2.2.2.2 hz)) hx1 hn1' hx2 hn2')
      fun s'' p' n' c' L3 b3 hpc'' hsp'' h28'' h29'' h18'' hrg'' e0 e1 e2 hv hnorm hlc hln hLE hb3 hinv3 hlive3 hor3
        hF3 hLF3 hreuse hc40 => ?qK
    case qK =>
      obtain ⟨rfl, rfl⟩ := hreuse hlc1
      have hl4 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hl48 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hfw3 := fw_call hs4 hout hzw (Or.inl rfl) (by omega) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ hF3
      have hrt3 := rt_call hrt' hs4 (by omega) (by omega) (Or.inl rfl) hrg'' hF3 hLF3 hLE hb3
        (makeCost_le_w (by simp only [W]; omega)) hinv3 hlive3
      obtain ⟨u1, u2, -⟩ := hfw3
      have hs144 : 144 ≤ s.sp.toNat := by omega
      janus_run [u1, u2]
      refine ⟨⟨?_, ?_⟩, post_ofG0 hrt3 (by omega) ?_ ?_ ?_ ?_ hnorm hlc hc40 hlive3 (Or.inl ⟨rfl, rfl⟩)
        (fun _ => ⟨rfl, rfl⟩)⟩
      · exact sp_ret hs144
      · rw [Nat.sub_sub, hfw.2.1, Expmc.bv_ofNat_toNat]
      · janus_simp
      · janus_simp
      · janus_simp
      · rw [hv, hv1', hv2']
        exact (SubMod2N.ge_branch _ _ _ (by rw [← hv1, ← hv2]; omega)).symm
    all_goals try janus_simp

end FvModexp.Arm64.SubMod2N

