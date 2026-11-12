import FvModexp.Proofs.Arm64.Exp.SubMod2NSeg2

/-!
# `nat.subMod2N` (arm64): `J5` → return: `z = z.trunc(z, n)`, `return z.add(z, natOne)` (nat.go:1754-1755) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem natOneA_eq : natOneA = 7356432 := by decide

set_option maxRecDepth 20000 in
/-- the global `natOne` survives the function's writes -/
theorem one_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) :
    M.readLE 7356432 8 = op ∧ M.readLE (7356432 + 8) 8 = 1 ∧ M.readLE (7356432 + 16) 8 = 1 ∧ M.readLE op 8 = 1 ∧
      M.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L1 op 8 ∧
      (op + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ op) ∧ Apart zp (8 * zc) op 8 ∧
      M.accessible 7356432 24 false = true := by
  obtain ⟨⟨-, -, -, hout, -, -, -, -⟩, -, -, ⟨o1, o2, o3, o4, oa, ort, ow, opa, op48, oph, opw⟩, hz1, hz2, -⟩ := id hpre
  obtain ⟨hreg, hF, hLF, hLE, -, -, -⟩ := hrt
  simp only [win, K, A, outside_cons, outside_nil, and_true] at ow opw hout
  rw [natOneA_eq] at o1 o2 o3 oa ort ow hz1
  unfold Apart at hz1 hz2
  have r : ∀ a, 7356432 ≤ a → a + 8 ≤ 7356432 + 24 → M.readLE a 8 = s.mem.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨ort.of_sub h1 h2, by omega, by omega⟩, by omega⟩
  refine ⟨(r _ (by omega) (by omega)).trans o1, (r _ (by omega) (by omega)).trans o2, (r _ (by omega) (by omega)).trans o3,
    ?_, by rw [hF.accessible]; exact opa, op48, hLE.held oph, by omega, by unfold Apart; omega,
    by rw [hF.accessible]; exact oa⟩
  rw [Expmc.held_readLE oph hF hLF (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)]
  exact o4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `z = z.trunc(z, n)` returns (`+0x2c0`): load `natOne`, `z.add(z, natOne)`, return -/
theorem s4t (impl : List Segment) (hap : ImplApart Extracted.program impl) {R : RtInv} (hadd : AddHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88)
    (M0 : Memory) {L3 : List (Nat × Nat)} {b3 : Nat} (hrt0 : Rt R b L s zp zc n 3 M0 L3 b3)
    (hfw0 : Fw s M0 zp zl zc yp n) (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hv0 : natVal M0 zp (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n))
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : S0.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h280 : S0.regs 28 = s.regs 28)
    (s' : State) (hpc' : s'.pc = BitVec.ofNat 64 (1805584 + 4 * 176)) (hsp' : s'.sp = S0.sp)
    (h28' : s'.regs 28 = S0.regs 28) (h18' : s'.regs 18 = s.regs 18) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b3 L3 stkT aboveT zp zc zp (W n) n S0 s') :
    Goal impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨⟨-, -, -⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  simp only [W] at hW
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hs4 : 4608 ≤ s.sp.toNat := by omega
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hrt0.2.2.2.2.2.2 (by omega)).2.2.2
  obtain ⟨p', l4, c', e0, e1, e2, L4, b4, ⟨hv4, hn4, hlc4, -, hlive4, hreuse4, -⟩, -, ⟨hLE4, hb4, hinv4⟩, hF4, hLF4⟩ :=
    hpost
  obtain ⟨hp, hc⟩ := hreuse4 (by unfold truncNeed; simp only [W]; omega)
  subst p' c'
  have hspT : S0.sp.toNat = s.sp.toNat - 144 := by rw [hsp0]; exact tN (by omega)
  simp only [winA, hspT] at hF4
  rw [hS0] at hF4 hLF4 hreg' hv4
  rw [h280] at hinv4
  have hrt4 := rt_call hrt0 hs4 hkT (by omega) (Or.inl rfl) hreg' hF4 hLF4 hLE4 hb4 (truncNeed_le_w _ _) hinv4 hlive4
  have hfw4 := fw_call hs4 hout hzw (Or.inl rfl) hkT haT hfw0 hF4
  obtain ⟨o1, o2, o3, o4, oa, o48, oh, ow, ozo, ona⟩ := one_at hpre hrt4
  have hW4 : l4 ≤ W n := len_le_W hn4 (by rw [hv4]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  have hsp1 : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) := hsp'.trans hsp0
  have hacc' : s'.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by
    rw [hrt4.2.1.accessible]; exact hw
  have hzacc : s'.mem.accessible zp (8 * zc) true = true := (hrt4.2.2.2.2.2.2 (by omega)).2.2.1
  unfold Goal
  have hzh4 : Held R L4 zp (8 * zc) := (hrt4.2.2.2.2.2.2 (by omega)).2.1
  have hon : NatNorm s'.mem op 1 := Or.inr (by rw [show op + 8 * (1 - 1) = op by omega, o4]; decide)
  janus_run [o1, o2, o3] until [1781184]
  refine addCall hap hadd (zp := zp) (zl := l4) (zc := zc) (xp := zp) (xl := l4) (xc := zc) (yp := op) (yl := 1)
    (yc := 1) (sp' := s.sp.toNat - 144) (g := (s.regs 28).toNat) (M := s'.mem)
    (bx39 := by have := hW4; simp only [W] at this; omega) (by39 := by omega)
    (ra_of hap (by decide) 185 (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (addPre_of hpre hrt4 (Nat.le_refl _) ?_ ?_ ?_ hlc4 (Nat.le_refl _) hzc (by omega) hW4 (by simp only [W]; omega)
      (Or.inl rfl) (Or.inr ozo) (Memory.accessible_sub _ hzacc (Or.inr rfl) (Nat.le_refl _) (by omega)) (by omega)
      (hzh4.sub (Nat.le_refl _) (by omega)) hn4 (by omega) oa o48 oh hon (by omega))
    fun s'' p5 n5 c5 L5 b5 hpc5 hsp5 h285 h295 h185 hrg5 q0 q1 q2 hv5 hn5 hlc5 hln5 hLE5 hb5 hinv5 hlive5 hor5 hF5 hLF5
      hreuse5 hc405 hb64 => ?qK
  case qK =>
    simp only [W] at hW4
    have hrt5 := rt_call hrt4 hs4 (show 4464 ≤ 4464 by omega) (show 80 ≤ 136 by omega) (Or.inl rfl) hrg5 hF5 hLF5
      hLE5 hb5 (makeCost_le_w (by simp only [W]; split <;> omega)) hinv5 (fun hc => ?_)
    · have hfw5 := fw_call hs4 hout hzw (Or.inl rfl) (show 4464 ≤ 4464 by omega) (show 80 ≤ 88 by omega) hfw4 hF5
      obtain ⟨u1, u2, -⟩ := hfw5
      janus_run [u1, u2]
      refine ⟨⟨?_, ?_⟩, post_of hrt5 (by omega) ?_ ?_ ?_ ?_ hn5 hlc5 hc405 hlive5 ?_
        (fun h => hreuse5 (by simp only [W] at h; split <;> omega))⟩
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, tN (by omega)]; simp only [BitVec.toNat_ofNat]; omega
      · rw [show s.sp.toNat - 144 - 8 = s.sp.toNat - 152 by omega, hfw0.2.1, Expmc.bv_ofNat_toNat]
      · janus_simp
      · janus_simp
      · janus_simp
      · dsimp only
        have h1 : natVal s'.mem op 1 = 1 := by unfold natVal; simpa using o4
        rw [hv5, hv4, hv0, h1, SubMod2N.lt_branch _ _ n _ (by omega) rfl hlt, SubMod2N.Bpow]
      · rcases hor5 with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, fresh_of hrt4.2.2.2.1 h2⟩
    · obtain ⟨c1, c2, c3, c4⟩ := hrt4.2.2.2.2.2.2 hc
      exact ⟨c1, hLE5.held c2, by rw [hF5.accessible]; exact c3, c4⟩
  all_goals try janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s4c (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hadd : AddHypR impl R) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
    J5 impl R b L op zp zl zc yp yl yc n s := by
  intro S L3 b3 hpre hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlt hv
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -,
    -, -, hzlive, hzw, hzg, -⟩ := id hpre
  simp only [W] at hW
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw hg3 hga
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hs4 : 4608 ≤ s.sp.toNat := by omega
  have hzh : Held R L3 zp (8 * zc) := (hrt.2.2.2.2.2.2 (by omega)).2.1
  have haccz : S.mem.accessible zp (8 * zc) true = true := (hrt.2.2.2.2.2.2 (by omega)).2.2.1
  rw [show (1805584 + 0x2ac : Nat) = 1806268 from rfl] at hpc
  unfold Goal
  janus_run until [1786000]
  refine truncCall hap hns htr (zp := zp) (zl := W n) (zc := zc) (x := zp) (xl := W n) (xc := zc) (n := n)
    (ra_of hap hnf 176 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega)
    (by simp only [W]; omega) (by omega) (by omega)
    (truncPre_of hpre hrt (by omega) ?_ ?_ ?_ hkT haT (Or.inl ⟨rfl, rfl⟩) (by simp only [W]; omega)
      (by simp only [W]; omega) ?_ (by simp only [W]; omega) (hzh.sub (Nat.le_refl _) (by simp only [W]; omega))
      (by omega) (by simp only [W]; omega) (Or.inl rfl))
    (Or.inr (by simp only [W]; omega)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost => ?qK
  case qK =>
    refine s4t impl hap hadd hpre hkT haT S.mem hrt hfw hlt hv _ ?_ ?_ ?_ s' hpc' hsp' h28' ?_ hreg' hpost
    · rfl
    · janus_simp
    · janus_simp
    · rw [h18']; janus_simp
  all_goals try janus_simp
  exact Memory.accessible_sub _ haccz (Or.inr rfl) (Nat.le_refl _) (by simp only [W]; omega)

end FvModexp.Arm64.SubMod2N
