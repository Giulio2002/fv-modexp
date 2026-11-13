import FvModexp.Proofs.Amd64.Exp.SubMod2NGS3L
import FvModexp.Proofs.Amd64.Exp.SubMod2NGS3G

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): `J2` → `x.cmp(y)` → `z.sub(x, y)` + return, or `z.sub(y, x)` → `J3` (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

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

/-- the frame words survive stores below `e - 8` -/
theorem fwG_lo {s : State} {M M' : Memory} {zp zl zc yp n lo : Nat} (hs : 152 ≤ (s.regs 4).toNat)
    (h : Fw s M zp zl zc yp n) (hF : MemFrame M M' [(lo, (s.regs 4).toNat - 8)]) :
    Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (s.regs 4).toNat - 8 ≤ a → M'.readLE a 8 = M.readLE a 8 :=
    fun a ha => hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨(r _ ?_).trans f1, (r _ ?_).trans f2, (r _ ?_).trans f3, (r _ ?_).trans f4, (r _ ?_).trans f5,
    (r _ ?_).trans f6, (r _ ?_).trans f7⟩ <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the entry of `x'.cmp(y')` (`RSP_c = e - 136`, return address `+0x26c`) -/
theorem s3Gc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hsub : SubHypR0 impl R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (k3 : J3G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    (S : State) {l1 p2 l2 c2 : Nat} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hpc : S.rip = BitVec.ofNat 64 6184128) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 136))
    (hab : Abi s S) (hra : S.mem.readLE ((s.regs 4).toNat - 136) 8 = 6216460)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 l1)
    (h7 : S.regs 7 = BitVec.ofNat 64 p2) (h6 : S.regs 6 = BitVec.ofNat 64 l2)
    (hfw : Fw s S.mem zp zl zc yp n) (r16 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = zp)
    (r40 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = l1) (r32 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = zc)
    (r24 : S.mem.readLE ((s.regs 4).toNat - 24) 8 = p2) (r56 : S.mem.readLE ((s.regs 4).toNat - 56) 8 = l2)
    (r48 : S.mem.readLE ((s.regs 4).toNat - 48) 8 = c2) (hrt : Rt R b L s zp zc n 2 S.mem L2 b2)
    (hv1 : natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n) (hn1 : NatNorm S.mem zp l1) (hW1 : l1 ≤ W n)
    (hv2 : natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n) (hn2 : NatNorm S.mem p2 l2) (hW2 : l2 ≤ W n)
    (hlc2 : l2 ≤ c2) (hc2 : c2 < 2 ^ 40) (hlc1 : l1 ≤ zc) (hp2 : p2 < 2 ^ 64) (hy2 : Y2 R L2 S.mem s zp zc p2 l2) :
    GoalG impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, hn1', -, hzl, ⟨hz64, -⟩, hzc, -, -,
    -, -, hzlive, hzw, -⟩ := id hpre
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  have hent := hpre.ent
  have hx1 := x1_of hpre hrt hlc1
  simp only [W] at hW1 hW2
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hspT : (S.regs 4).toNat = (s.regs 4).toNat - 136 := by rw [hsp]; exact tN (by omega)
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hw
  refine CmpW.call (cmpSumW impl hap) hpc (cmpPre_of hspT h0 h3 h7 h6 (by rw [hra]; decide) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega))
    (by
      rcases Nat.eq_zero_or_pos l1 with h | h
      · exact Or.inl h
      · obtain ⟨a1, a2, -, a4⟩ := hx1 h; exact Or.inr ⟨a2, a1, by unfold Apart; omega⟩)
    (by
      rcases Nat.eq_zero_or_pos l2 with h | h
      · exact Or.inl h
      · obtain ⟨a1, a2, -, a4, -⟩ := hy2 h; exact Or.inr ⟨a2, a1, by unfold Apart; omega⟩))
    fun S' hpc' hsp' hr0 hrs hxm hfs' hdf' hF' hrg' => ?_
  rw [h0, h3, h7, h6, tN hz64, tN (show l1 < 2 ^ 64 by omega), tN hp2, tN (show l2 < 2 ^ 64 by omega)] at hr0
  simp only [FvModexp.Asm.lv] at hr0
  have hs4 : 4576 ≤ (s.regs 4).toNat := by omega
  obtain ⟨hcfA, hcfG⟩ := cmp_frame (R := R) hs4 hspT hF'
  have hrt' : Rt R b L s zp zc n 2 S'.mem L2 b2 := rtG_stk hpre hrt hcfA hrg'
  have hfw' : Fw s S'.mem zp zl zc yp n :=
    fw_call (zr := ((0 : Nat), (0 : Nat))) hs4 hout (by omega) (Or.inr rfl) (by omega) (by omega) hfw hcfG
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw'
  unfold CmpSum.frame at hF'
  rw [hspT] at hF'
  have rdl : ∀ a, (s.regs 4).toNat - 56 ≤ a → a + 8 ≤ (s.regs 4).toNat - 8 → S'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hF'.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]; omega
  have q16 := (rdl _ (by omega) (by omega)).trans r16
  have q40 := (rdl _ (by omega) (by omega)).trans r40
  have q32 := (rdl _ (by omega) (by omega)).trans r32
  have q24 := (rdl _ (by omega) (by omega)).trans r24
  have q56 := (rdl _ (by omega) (by omega)).trans r56
  have q48 := (rdl _ (by omega) (by omega)).trans r48
  have hzA : Outside zp (8 * l1) (win s K A) := by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  have hyA : 0 < l2 → Outside p2 (8 * l2) (win s K A) := fun h => by
    have := (hy2 h).2.2.2.1
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  have hv1' := (natVal_frame hcfA hzA).trans hv1
  have hv2' := (nat_frame0 hcfA hyA).1.trans hv2
  have hn1' := natNorm_frame hcfA hzA hn1
  have hn2' := (nat_frame0 hcfA hyA).2 hn2
  have hy2' := hy2.frame hcfA
  have hacc' : S'.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hcfA.accessible]; exact hacc
  have hsp1 : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) := by
    rw [hsp', hsp]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  have h14' : S'.regs 14 = s.regs 14 := (hrs 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14
  have hpc1 : S'.rip = BitVec.ofNat 64 6216460 := by rw [hpc', retAddrOf_eq, hspT, hra]
  have a16 : (s.regs 4).toNat - 128 + 144 = (s.regs 4).toNat + 16 := by omega
  have a24 : (s.regs 4).toNat - 128 + 152 = (s.regs 4).toNat + 24 := by omega
  have a32 : (s.regs 4).toNat - 128 + 160 = (s.regs 4).toNat + 32 := by omega
  have b16 : (s.regs 4).toNat - 128 + 112 = (s.regs 4).toNat - 16 := by omega
  have b40 : (s.regs 4).toNat - 128 + 88 = (s.regs 4).toNat - 40 := by omega
  have b32 : (s.regs 4).toNat - 128 + 96 = (s.regs 4).toNat - 32 := by omega
  have b24 : (s.regs 4).toNat - 128 + 104 = (s.regs 4).toNat - 24 := by omega
  have b56 : (s.regs 4).toNat - 128 + 72 = (s.regs 4).toNat - 56 := by omega
  have b48 : (s.regs 4).toNat - 128 + 80 = (s.regs 4).toNat - 48 := by omega
  have hx0 : S'.xmm 15 = 0 := by rw [hxm, hx15]; exact hent.2.2.2.1
  have hdf0 : S'.df = false := by rw [hdf', hdf]
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  have fr : ∀ M', MemFrame S'.mem M' (win s K A) →
      natVal M' zp l1 = natVal s.mem zp zl % 2 ^ n ∧ natVal M' p2 l2 = natVal s.mem yp yl % 2 ^ n ∧
      NatNorm M' zp l1 ∧ NatNorm M' p2 l2 := fun M' h =>
    ⟨(natVal_frame h hzA).trans hv1', (nat_frame0 h hyA).1.trans hv2', natNorm_frame h hzA hn1',
      (nat_frame0 h hyA).2 hn2'⟩
  by_cases hlt : natVal S.mem zp l1 < natVal S.mem p2 l2
  · have hR : S'.regs 0 = 18446744073709551615#64 := hr0.trans (cmpG_neg hn1 hn2 hlt)
    have hll := (SubMod2N.cmp_lt_iff S.mem zp l1 p2 l2 hn1 hn2).2 hlt
    janus64_run [hR, b136, hsp1, a16, a24, a32, b16, b40, b32, b24, b56, b48, f3, f4, f5, q16, q40, q32, q24, q56, q48]
      until [6183136]
    all_goals first | (exact absurd hbr (by decide)) | skip
    refine s3Glt impl hap hsub hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (rtG_stk hpre hrt' ?_ ?_) (fwG_lo (lo := (s.regs 4).toNat - 4576) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_)
      (fr _ ?_).1 (fr _ ?_).2.2.1 hW1 (fr _ ?_).2.1 (fr _ ?_).2.2.2 hW2 hlc2 hc2 hlc1 hp2
      (hy2'.frame (ws := win s K A) ?_) k3 (by rw [← hv1, ← hv2]; exact hlt)
    all_goals first
      | (simp only [win, K, A]; janus_frame)
      | janus_frame
      | (janus64_simp; done)
      | (janus64_simp <;> first | exact hx0 | exact hdf0 | exact h14' | exact hfs'.trans hfs | exact tN (by omega) | omega)
  · obtain ⟨v, hv01, hcv⟩ := cmpG_nonneg' hn1 hn2 hlt
    have hR : S'.regs 0 = BitVec.ofNat 64 v := hr0.trans hcv
    have h63 : (BitVec.ofNat 64 v).msb = false := by
      rw [BitVec.msb_eq_decide]; simp; omega
    have hll := mt (SubMod2N.cmp_lt_iff S.mem zp l1 p2 l2 hn1 hn2).1 hlt
    janus64_run [hR, h63, b136, hsp1, a16, a24, a32, b16, b40, b32, b24, b56, b48, f3, f4, f5, q16, q40, q32, q24, q56, q48]
      until [6183136]
    all_goals first | (exact absurd h63 hbr) | skip
    refine s3Gge impl hap hsub hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (rtG_stk hpre hrt' ?_ ?_) (fwG_lo (lo := (s.regs 4).toNat - 4576) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_)
      (fr _ ?_).1 (fr _ ?_).2.2.1 hW1 (fr _ ?_).2.1 (fr _ ?_).2.2.2 hW2 hlc2 hc2 hlc1 hp2
      (hy2'.frame (ws := win s K A) ?_) (by rw [← hv1, ← hv2]; exact hlt)
    all_goals first
      | (simp only [win, K, A]; janus_frame)
      | janus_frame
      | (janus64_simp; done)
      | (janus64_simp <;> first | exact hx0 | exact hdf0 | exact h14' | exact hfs'.trans hfs | exact tN (by omega) | omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `J2` → `x'.cmp(y')` (spill `y'`, call at `+0x267`) → `s3Gc` -/
theorem s3G (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hsub : SubHypR0 impl R) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (k3 : J3G impl R b L op zp zl zc yp yl yc n s) : J2G impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 p2 l2 c2 L2 b2 hpre hpc hsp hab h7 h6 h8 h9 h10 h11 hfw r16 r40 r32 hrt hv1 hn1 hW1 hlc1 hv2 hn2 hW2 hlc2
    hc2 hp2 hy2
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, -, -, hzl, -, hzc, -, -,
    -, -, hzlive, hzw, -⟩ := id hpre
  have hent := hpre.ent
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  simp only [W] at hW1 hW2
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hw
  have hzA : Outside zp (8 * l1) (win s K A) := by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  have hyA : 0 < l2 → Outside p2 (8 * l2) (win s K A) := fun h => by
    have := (hy2 h).2.2.2.1
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw
  have b24 : (s.regs 4).toNat - 128 + 104 = (s.regs 4).toNat - 24 := by omega
  have b56 : (s.regs 4).toNat - 128 + 72 = (s.regs 4).toNat - 56 := by omega
  have b48 : (s.regs 4).toNat - 128 + 80 = (s.regs 4).toNat - 48 := by omega
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  unfold GoalG
  janus64_run [hsp, b24, b56, b48, b136] until [6184128]
  refine s3Gc impl hap hsub k3 hpre _ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (rtG_stk hpre hrt ?_ ?_)
    ((natVal_frame (rs := win s K A) ?_ hzA).trans hv1) (natNorm_frame (rs := win s K A) ?_ hzA hn1) hW1
    ((nat_frame0 (ws := win s K A) ?_ hyA).1.trans hv2) ((nat_frame0 (ws := win s K A) ?_ hyA).2 hn2) hW2 hlc2 hc2
    hlc1 hp2 (Y2.frame (ws := win s K A) ?_ hy2)
  all_goals first
    | (simp only [win, K, A]; janus_frame)
    | (janus64_simp; done)
    | exact fwG_lo (lo := (s.regs 4).toNat - 4576) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ (by janus_frame)
    | (janus64_simp <;> first | exact h14 | exact hfs | exact hx15 | exact hdf)
    | (janus64_simp <;> first | exact r16 | exact r40 | exact r32)
    | (janus64_simp <;> first | exact tN (by omega) | exact Nat.mod_eq_of_lt (by omega))
    | (janus64_simp <;> (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

end FvModexp.Amd64.SubMod2N
