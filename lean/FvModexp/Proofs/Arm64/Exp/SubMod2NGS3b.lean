import FvModexp.Proofs.Arm64.Exp.SubMod2NGS3

/-!
# `nat.subMod2N` (arm64), general form: `J2G` (the spills before) → `x.cmp(y)` → `z.sub(x, y)` + return, or `z.sub(y, x)` → `J3G`
(empty-tolerant `SubHypR0`; the result of `z.sub(y, x)` in `z`'s array or a fresh one) (agent infra)
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s3G (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (hsub : SubHypR0 impl R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (k3 : J3G impl R b L op zp zl zc yp yl yc n s) : J2G impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 p2 l2 c2 L2 b2 hpre hpc hsp h28 h18 h3 h4 h5 h6 h7 h8 hfw r16 r40 r32 hrt hv1 hn1 hW1 hlc1 hv2 hn2 hW2
    hlc2 hc2 hp2 hy2
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -, -, -, -, -, hn1', -, hzl, ⟨hz64, -⟩, hzc,
    -, -, -, -, hzlive, hzw, hzg, -⟩ := id hpre
  simp only [W] at hW1 hW2
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw hg3 hga
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hzA : Outside zp (8 * l1) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw
  unfold GoalG
  janus_run until [1782608]
  refine s3Gc impl hap hsub k3 hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (rtG_stk hpre hrt ?_ ?_) ?_ ?_ hW1
    hlc1 ?_ ?_ hW2 hlc2 hc2 hp2 ?_
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
  · rcases Nat.eq_zero_or_pos l2 with h | h
    · subst h; rw [← hv2]; rfl
    · have := (hy2 h).2.2.2.1
      refine (natVal_frame (rs := winA s K A) ?_ (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)).trans hv2
      simp only [winA, K, A]; janus_frame
  · rcases Nat.eq_zero_or_pos l2 with h | h
    · exact Or.inl h
    · have := (hy2 h).2.2.2.1
      refine natNorm_frame (rs := winA s K A) ?_ (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega) hn2
      simp only [winA, K, A]; janus_frame
  · exact hy2

end FvModexp.Arm64.SubMod2N
