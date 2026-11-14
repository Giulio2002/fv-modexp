import FvModexp.Proofs.Amd64.Exp.P2PreTr

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): after `mul` (`JC`) → header store of `powers[i+1]`, write barrier,
`powers[i+1] = powers[i+1].trunc(powers[i+1], logM)` → `JD` (agent divmc s65; twin of infra's `Arm64/Exp/P2PreC`)

`jC2`: the join after the write barrier (`+0x539`, the pointer store), memory abstract (reads of `powers` and `buf` kept
from `M0`, the locals given). `segC`: `JC` → `jC2` (the `(len, cap)` stores `+0x512/+0x517`, the barrier test `+0x51c`,
`gcWriteBarrier2` `+0x52d` with its buffer stores).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

theorem p2_odd {lm X i : Nat} (h2 : 2 ≤ i) (he : i % 2 = 0) :
    Exp.p2Pow lm X (i + 1) = Exp.p2Pow lm X i * Exp.p2Pow lm X 1 % 2 ^ lm := by
  rw [Exp.p2Pow]
  simp only [show i + 1 ≠ 0 by omega, show i + 1 ≠ 1 by omega, show (i + 1) % 2 ≠ 0 by omega, dite_false,
    if_false, Nat.add_sub_cancel]
  rw [show Exp.p2Pow lm X 1 = X % 2 ^ lm by rw [Exp.p2Pow]; simp]

/-- the pointer store of `powers[i+1]` after the second barrier -/
abbrev pcPC : Nat := 0x5e8900 + 0x539

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jC2 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s) {i : Nat}
    (kD : JD impl R kc b L st pw pl ws lm x xl s i) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 l : Nat} (S : State) (hpc : S.rip = BitVec.ofNat 64 pcPC) (hfr : Frm s S 176) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * ((i + 1) * W lm))) (h3 : S.regs 3 = BitVec.ofNat 64 l)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * W lm)) (h2 : S.regs 2 = BitVec.ofNat 64 (3 * i))
    (h10 : S.regs 10 = BitVec.ofNat 64 pw)
    (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {M0 : Memory}
    (hrd : ∀ c n, 0 < n → ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
      M.readLE c n = M0.readLE c n) (hlo : Lo s i M)
    (hrs0 : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M0 L1 b1 i (i + 1)) (hl : l ≤ 2 * W lm)
    (hv0 : natVal M0 (bp + 8 * ((i + 1) * W lm)) l = PV lm x xl s i * PV lm x xl s 1)
    (hn0 : NatNorm M0 (bp + 8 * ((i + 1) * W lm)) l) (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl)
    (hb : b - (tC lm + (i / 2 - 1) * rc lm + (sqrCQ (W lm) + tC lm + mulCQ (W lm) (W lm))) ≤ b1) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S (GoalQ R kc b L st pw pl lm x xl s) := by
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hR64 := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hwm : M.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hrs : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M L1 b1 i (i + 1) := by
    have hkn : (i + 1) * W lm ≤ NB pl lm := Nat.mul_le_mul_right _ (by omega)
    have h0 := rs0_rd hrs0.to0 hc fun c n h0 h => hrd c n h0 (by omega)
    exact ⟨h0.c, h0.d, h0.t, hlo⟩
  have hkb : KeepB bp (NB pl lm) M0 M := fun c n h0 h1 h2 => hrd c n h0 (Or.inr ⟨h1, h2⟩)
  obtain ⟨ev0, en0⟩ := nat_keepB hkb (p := bp + 8 * ((i + 1) * W lm)) (l := l)
    (by omega) (by have := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i + 1) (by omega); omega)
  have hv : natVal M (bp + 8 * ((i + 1) * W lm)) l = PV lm x xl s i * PV lm x xl s 1 := ev0.trans hv0
  have hn : NatNorm M (bp + 8 * ((i + 1) * W lm)) l := en0 hn0
  clear hrs0 hrd ev0 en0 hv0 hn0 hkb
  have hpw48 := hf.pw48
  have hpwa : M.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hfr' := hfr
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr'
  obtain ⟨-, -, -, -, e4, -, -, -, -, -, -⟩ := hc.sl
  have f224 : M.readLE ((s.regs 4).toNat - 176 + 224) 8 = lm := by
    rw [show (s.regs 4).toNat - 176 + 224 = (s.regs 4).toNat + 48 by omega]; exact e4
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i + 1) (by omega)
  have hrs5 := rs_st hpre hkc hrs (by omega) (bp + 8 * ((i + 1) * W lm)) (a0 := pw + 3 * i * 8 + 24) (n0 := 8)
    (by omega) ⟨by omega, by omega⟩
  have hk5 := keepB_st hpre hkc hc (bp + 8 * ((i + 1) * W lm)) (a0 := pw + 3 * i * 8 + 24) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨ev, en⟩ := nat_keepB hk5 (p := bp + 8 * ((i + 1) * W lm)) (l := l) (by omega) (by omega)
  have hvT : PV lm x xl s (i + 1) = PV lm x xl s i * PV lm x xl s 1 % 2 ^ lm := p2_odd hi hi2
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  subst hm
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hk5 hrs hc hpre
  janus64_run [f224, hwm, hpwa] until [6188320]
  refine callTr hap hns hnf htr hkT haT hkc hpreB.h (pcR := 0x554) (by decide) kD (Nat.le_succ _) (Nat.le_refl _)
    (by simp only [rc]; omega) (Nat.le_refl _) hrs5 hi2 hi hip hb hl (en hn) (ev.trans hv) hvT _ rfl
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | exact hfs | exact hdf | exact hsub8 | (janus64_simp <;> first | exact hx15 | rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segC (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc) {i : Nat}
    (kD : JD impl R kc b L st pw pl ws lm x xl s i) :
    JC impl R kc b L st pw pl ws lm x xl s i := by
  intro S bp L1 b1 l hpre hpc hfr h0 h3 h1 hrs hl hv hn hi2 hi hip hb
  replace hrs : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp S.mem L1 b1 i (i + 1) := hrs
  replace h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * ((i + 1) * W lm)) := h0
  replace hv : natVal S.mem (bp + 8 * ((i + 1) * W lm)) l = PV lm x xl s i * PV lm x xl s 1 := hv
  replace hn : NatNorm S.mem (bp + 8 * ((i + 1) * W lm)) l := hn
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hc := hrs.c
  have hpw48 := hf.pw48
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hfr' := hfr
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr'
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hR64 := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hadd8 : BitVec.ofNat 64 ((s.regs 4).toNat - 184) + 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hwm : S.mem.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hpwm : S.mem.accessible pw (24 * pl) true = true := by
    rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hwbf : S.mem.accessible RunIface.wbA 4 false = true := by
    rw [hc.fr.accessible]; exact hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.1
  have hwbv : RunIface.wbA = 12283968 := rfl
  rw [hwbv] at hwbf
  have hwbpw : pw + 24 * pl ≤ 12283968 ∨ 12283968 + 4 ≤ pw := by
    have g := hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2
    simp only [win, outside_cons, outside_append, outside_nil, and_true] at g; omega
  obtain ⟨-, -, -, e3, -, -, -, -, -, -, -⟩ := hc.sl
  have f192 : S.mem.readLE ((s.regs 4).toNat - 176 + 192) 8 = pw := by
    rw [show (s.regs 4).toNat - 176 + 192 = (s.regs 4).toNat + 16 by omega]; exact e3
  have f112 : S.mem.readLE ((s.regs 4).toNat - 176 + 112) 8 = 3 * i := by
    rw [show (s.regs 4).toNat - 176 + 112 = (s.regs 4).toNat - 64 by omega]; exact hrs.lo.2
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i + 1) (by omega)
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hboF : bp + 8 * NB pl lm ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ bp := by
    have := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
      (by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; simp only; omega)
    simp only [K, A] at this; omega
  have hrs3 := rs_st hpre hkc (rs_st hpre hkc hrs (by omega) l (a0 := pw + 3 * i * 8 + 32) (n0 := 8) (by omega)
    ⟨by omega, by omega⟩) (by omega) (2 * W lm) (a0 := pw + 3 * i * 8 + 40) (n0 := 8) (by omega) ⟨by omega, by omega⟩
  have hk3 := keepB_trans (keepB_st hpre hkc hc l (a0 := pw + 3 * i * 8 + 32) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs_st hpre hkc hrs (by omega) l
      (a0 := pw + 3 * i * 8 + 32) (n0 := 8) (by omega) ⟨by omega, by omega⟩).c (2 * W lm)
    (a0 := pw + 3 * i * 8 + 40) (n0 := 8) (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨ev, en⟩ := nat_keepB hk3 (p := bp + 8 * ((i + 1) * W lm)) (l := l) (by omega) (by omega)
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have t184 : (BitVec.ofNat 64 ((s.regs 4).toNat - 184)).toNat = (s.regs 4).toNat - 184 := tN (by omega)
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hk3 hrs hpre
  unfold Goal
  janus64_run [f192, f112, hwbf, hwbpw, hpwm, hwm, hsub8, t184] until [wbE, pcPC]
  · -- the barrier is off
    refine jC2 hap hns hnf htr hkT haT hkc hpreB.h kD _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_ hrs3.c
      (fun _ _ _ _ => rfl) hrs3.lo hrs3 hl (ev.trans hv) (en hn) hi2 hi hip hb
    all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hx15 | rfl)
  · -- the barrier is on
    have hc6 := ctx_own hrs3.c hf (0x5e8900 + 0x532) (a := (s.regs 4).toNat - 184) (k := 8)
      ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
    refine wbCall hwb hpreB.h hkc hc6 rfl (by janus64_simp) (by janus64_simp) rfl ?_ ?_
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · intro buf f2 xm2 yh2 m' zh2 kr2 hb16 hb8 hbacc hctx hrdW
      have hb8a : m'.accessible buf.toNat 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
      have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (by omega) (by omega)
      have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
      janus64_run [hb8a, hb8b, hbuf64, hadd8] until [pcPC]
      have hr : ∀ v1 v2 c n, 0 < n → ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
          (W2 m' buf.toNat v1 v2).readLE c n =
            ((S.mem.writeLE (pw + 3 * i * 8 + 32) 8 l).writeLE (pw + 3 * i * 8 + 40) 8 (2 * W lm)).readLE c n := by
        intro v1 v2 c n h0 h
        refine (hrdW v1 v2 c n h0 (by simp only [RdR]; omega)).trans ?_
        exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
      have hlo : ∀ v1 v2, Lo s i (W2 m' buf.toNat v1 v2) := fun v1 v2 =>
        ⟨(hrdW v1 v2 _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩))).trans
          ((Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans hrs3.lo.1),
         (hrdW v1 v2 _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩))).trans
          ((Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans hrs3.lo.2)⟩
      refine jC2 hap hns hnf htr hkT haT hkc hpreB.h kD _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_
        (hctx _ _) (hr _ _) (hlo _ _) hrs3 hl (ev.trans hv) (en hn) hi2 hi hip hb
      all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hadd8 | exact hx15 | rfl)

end

end FvModexp.Amd64.P2Pre
