import FvModexp.Proofs.Arm64.Exp.SubMod2NGAlloc

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: `J5G` → return: `z = z.trunc(z, n)`, `return z.add(z, natOne)`
(nat.go:1754-1755) on the current array `(p, c)` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem natOneG_eq : natOneA = 7356432 := by decide

/-- the budget base after `g` growths still covers the remaining calls -/
theorem bb_ok {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {g : Nat} (hg : g ≤ W n) (hgz : W n ≤ zc → g = 0) :
    cost n ≤ b - g * gA n := by
  have hc := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases h : W n ≤ zc
  · rw [hgz h, Nat.zero_mul, Nat.sub_zero]; exact hc.1
  · have h1 := hc.2 (by omega)
    have h2 : g * gA n ≤ W n * gA n := Nat.mul_le_mul_right _ hg
    simp only [costG] at h1; omega

set_option maxRecDepth 20000 in
/-- the global `natOne` survives the function's writes -/
theorem oneG_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R bb L s zp zc n k M L1 b1) :
    M.readLE 7356432 8 = op ∧ M.readLE (7356432 + 8) 8 = 1 ∧ M.readLE (7356432 + 16) 8 = 1 ∧ M.readLE op 8 = 1 ∧
      M.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L1 op 8 ∧
      (op + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ op) ∧ M.accessible 7356432 24 false = true := by
  obtain ⟨⟨-, -, -, hout, -, -, -, -⟩, -, -, ⟨o1, o2, o3, o4, oa, ort, ow, opa, op48, oph, opw⟩, hz1, hz2, -⟩ := id hpre
  obtain ⟨hreg, hF, hLF, hLE, -, -, -⟩ := hrt
  simp only [win, K, A, outside_cons, outside_nil, and_true] at ow opw hout
  rw [natOneG_eq] at o1 o2 o3 oa ort ow hz1
  unfold Apart at hz1 hz2
  have r : ∀ a, 7356432 ≤ a → a + 8 ≤ 7356432 + 24 → M.readLE a 8 = s.mem.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨ort.of_sub h1 h2, by omega, by omega⟩, by omega⟩
  refine ⟨(r _ (by omega) (by omega)).trans o1, (r _ (by omega) (by omega)).trans o2, (r _ (by omega) (by omega)).trans o3,
    ?_, by rw [hF.accessible]; exact opa, op48, hLE.held oph, by omega, by rw [hF.accessible]; exact oa⟩
  rw [Expmc.held_readLE oph hF hLF (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)]
  exact o4

/-- the written range `(p, p + 8c)` of a call on the current array, in `rt_callG`'s form -/
theorem zr_cur {R : RtInv} {L : List (Nat × Nat)} {zp zc p c : Nat} (h : CurA R L zp zc p c) :
    (p, p + 8 * c) = (zp, zp + 8 * zc) ∨ (p + 8 * c) = 0 ∨
      (p ≤ p + 8 * c ∧ InRanges p (p + 8 * c - p) R.rt ∧ ApartAll p (p + 8 * c - p) L) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨by omega, by rwa [show p + 8 * c - p = 8 * c by omega], by
      rwa [show p + 8 * c - p = 8 * c by omega]⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `z = z.trunc(z, n)` returns (`+0x2c0`): load `natOne`, `z.add(z, natOne)`, return -/
theorem s4tG (impl : List Segment) (hap : ImplApart Extracted.program impl) {R : RtInv} (hadd : AddHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88)
    {p c g : Nat} (hcur : CurA R L zp zc p c) (hc40 : c < 2 ^ 40) (hp64 : p < 2 ^ 64) (hWc : W n ≤ c)
    (hg : g ≤ W n) (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0)
    (M0 : Memory) {L3 : List (Nat × Nat)} {b3 : Nat} (hrt0 : Rt R (b - g * gA n) L s zp zc n 3 M0 L3 b3)
    (hlv0 : NatLive M0 R L3 p c)
    (hfw0 : Fw s M0 zp zl zc yp n) (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hv0 : natVal M0 p (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n))
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : S0.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h280 : S0.regs 28 = s.regs 28)
    (s' : State) (hpc' : s'.pc = BitVec.ofNat 64 (1805584 + 4 * 176)) (hsp' : s'.sp = S0.sp)
    (h28' : s'.regs 28 = S0.regs 28) (h18' : s'.regs 18 = s.regs 18) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b3 L3 stkT aboveT p c p (W n) n S0 s') :
    GoalG impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨⟨-, -, -⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, -, hzc, -, -, -, -, hzlive,
    hzw, -⟩ := id hpre
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hs4 : 4608 ≤ s.sp.toNat := by omega
  have hbb := bb_ok hpre hg fun h => (hgz h).2.2
  obtain ⟨hpw, hpg, hpo1, hpo⟩ := curA_win hpre hcur
  have hW1 : 1 ≤ W n := by simp only [W]; omega
  obtain ⟨-, hph0, hpacc0, hp48⟩ := hlv0 (by omega)
  obtain ⟨p', l4, c', e0, e1, e2, L4, b4, ⟨hv4, hn4, hlc4, -, hlive4, hreuse4, -⟩, -, ⟨hLE4, hb4, hinv4⟩, hF4, hLF4⟩ :=
    hpost
  obtain ⟨hp, hc⟩ := hreuse4 (by unfold truncNeed; simp only [W] at hWc ⊢; omega)
  subst p' c'
  have hspT : S0.sp.toNat = s.sp.toNat - 144 := by rw [hsp0]; exact tN (by omega)
  simp only [winA, hspT] at hF4
  rw [hS0] at hF4 hLF4 hreg' hv4
  rw [h280] at hinv4
  have hrt4 := rt_callG hrt0 hs4 hkT (by omega) (zr_cur hcur) hreg' hF4 hLF4 hLE4 hb4 (truncNeed_le_w _ _) hinv4
    (fun hc => by
      obtain ⟨c1, c2, c3, c4⟩ := hrt0.2.2.2.2.2.2 hc
      exact ⟨c1, hLE4.held c2, by rw [hF4.accessible]; exact c3, c4⟩)
  have hfw4 := fw_callG hs4 hout (Or.inr (by simp only; omega)) hkT haT hfw0 hF4
  obtain ⟨o1, o2, o3, o4, oa, o48, oh, ow, ona⟩ := oneG_at hpre hrt4
  have hW4 : l4 ≤ W n := len_le_W hn4 (by rw [hv4]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  have hsp1 : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) := hsp'.trans hsp0
  have hacc' : s'.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by
    rw [hrt4.2.1.accessible]; exact hw
  have hzacc : s'.mem.accessible p (8 * c) true = true := by rw [hF4.accessible]; exact hpacc0
  have hlv4 : NatLive s'.mem R L4 p c := hlive4
  have hzh4 : Held R L4 p (8 * c) := (hlv4 (by omega)).2.1
  unfold GoalG
  have hon : NatNorm s'.mem op 1 := Or.inr (by rw [show op + 8 * (1 - 1) = op by omega, o4]; decide)
  janus_run [o1, o2, o3] until [1781184]
  refine addCall hap hadd (zp := p) (zl := l4) (zc := c) (xp := p) (xl := l4) (xc := c) (yp := op) (yl := 1)
    (yc := 1) (sp' := s.sp.toNat - 144) (g := (s.regs 28).toNat) (M := s'.mem)
    (bx39 := by have := hW4; simp only [W] at this; omega) (by39 := by omega)
    (ra_of hap (by decide) 185 (by omega)) (by omega) hp64 (by omega) hp64 (by omega) (by omega)
    (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (addPreG_of hpre hbb hrt4 (Nat.le_refl _) ?_ ?_ ?_ (by omega) hc40 hlv4 hp64 (fun _ => ⟨hpw, hpg⟩) hlc4
      (Nat.le_refl _) hc40 (by omega) hW4 (by simp only [W]; omega)
      (Or.inl rfl) (Or.inr hpo) (Memory.accessible_sub _ hzacc (Or.inr rfl) (Nat.le_refl _) (by omega)) (by omega)
      (hzh4.sub (Nat.le_refl _) (by omega)) hn4 (by omega) oa o48 oh hon (by omega))
    fun s'' p5 n5 c5 L5 b5 hpc5 hsp5 h285 h295 h185 hrg5 q0 q1 q2 hv5 hn5 hlc5 hln5 hLE5 hb5 hinv5 hlive5 hor5 hF5 hLF5
      hreuse5 hc405 hb64 => ?qK
  case qK =>
    simp only [W] at hW4
    have hrt5 := rt_callG hrt4 hs4 (show 4464 ≤ 4464 by omega) (show 80 ≤ 136 by omega) (zr_cur hcur) hrg5 hF5 hLF5
      hLE5 hb5 (makeCost_le_w (by simp only [W]; split <;> omega)) hinv5 (fun hc => ?_)
    · have hfw5 := fw_callG hs4 hout (Or.inr (by simp only; omega)) (show 4464 ≤ 4464 by omega)
        (show 80 ≤ 88 by omega) hfw4 hF5
      obtain ⟨u1, u2, -⟩ := hfw5
      have hs144 : 144 ≤ s.sp.toNat := by omega
      janus_run [u1, u2]
      refine ⟨⟨?_, ?_⟩, post_ofG hrt5 (by omega) hg (fun h => (hgz h).2.2) ?_ ?_ ?_ ?_ hn5 hlc5 hc405 hlive5 ?_
        (fun h => ?_)⟩
      · exact sp_ret hs144
      · rw [Nat.sub_sub, hfw0.2.1, Expmc.bv_ofNat_toNat]
      · janus_simp
      · janus_simp
      · janus_simp
      · dsimp only
        have h1 : natVal s'.mem op 1 = 1 := by unfold natVal; simpa using o4
        rw [hv5, hv4, hv0, h1, SubMod2N.lt_branch _ _ n _ (by omega) rfl hlt, SubMod2N.Bpow]
      · rcases hor5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases hcur with ⟨e1, e2⟩ | ⟨h3, h4⟩
          · exact Or.inl ⟨h1.trans e1, h2.trans e2⟩
          · exact Or.inr ⟨h1 ▸ h2 ▸ h3, h1 ▸ h2 ▸ h4⟩
        · exact Or.inr ⟨h1, fresh_of hrt4.2.2.2.1 h2⟩
      · have hW' : W n ≤ zc := Nat.le_of_succ_le h
        obtain ⟨e1, e2, -⟩ := hgz hW'
        have hn' : (if min l4 1 = 0 then max l4 1 else max l4 1 + 1) ≤ c := by
          rw [e2]; simp only [W] at h; split <;> omega
        exact ⟨(hreuse5 hn').1.trans e1, (hreuse5 hn').2.trans e2⟩
    · obtain ⟨c1, c2, c3, c4⟩ := hrt4.2.2.2.2.2.2 hc
      exact ⟨c1, hLE5.held c2, by rw [hF5.accessible]; exact c3, c4⟩
  all_goals try janus_simp

end FvModexp.Arm64.SubMod2N
