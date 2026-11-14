import FvModexp.Proofs.Amd64.Exp.P2PreRS0

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): after `trunc(x)` (`JT`) → header store of `powers[1]`, write barrier,
`cap ≥ w` / `len ≤ w` checks, `cap := w`, `i := 2` → loop head (`HeadJ 2`) (agent divmc s64; twin of infra's
`Arm64/Exp/P2PreXT`)

`jT2`: the join after the write barrier (`+0x344`, the pointer store), memory abstract. `segT`: `JT` → `jT2` (the
`(len, cap)` stores `+0x323/+0x327`, the barrier test `+0x32b`, `gcWriteBarrier2` `+0x338` with its buffer stores).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

/-- the pointer store of `powers[1]` after the barrier -/
abbrev pcP : Nat := 0x5e8900 + 0x344

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jT2 (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s)
    (kH : HeadJ impl R kc b L st pw pl ws lm x xl s 2) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 l : Nat} (S : State) (hpc : S.rip = BitVec.ofNat 64 pcP) (hfr : Frm s S 176) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * (1 * W lm))) (h3 : S.regs 3 = BitVec.ofNat 64 l)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * W lm)) (h2 : S.regs 2 = BitVec.ofNat 64 pw)
    (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {M0 : Memory}
    (hrd : ∀ c n, 0 < n → ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
      M.readLE c n = M0.readLE c n)
    (hrs0 : RS0 R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M0 L1 b1 1) (hl : l ≤ W lm)
    (hlen0 : M0.readLE (pw + 24 * 1 + 8) 8 = l)
    (hv0 : natVal M0 (bp + 8 * (1 * W lm)) l = PV lm x xl s 1)
    (hn0 : NatNorm M0 (bp + 8 * (1 * W lm)) l) (hb : b - tC lm ≤ b1) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S (GoalQ R kc b L st pw pl lm x xl s) := by
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hin0 := pw_in (pl := pl) (lm := lm) (bp := bp) (j := 1) (by omega)
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hwm : M.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hrs := rs0_rd hrs0 hc fun c n h0 h => hrd c n h0 (by omega)
  obtain ⟨ev0, en0⟩ := nat_keepB (M := M0) (M' := M) (fun c n h0 h1 h2 => hrd c n h0 (Or.inr ⟨h1, h2⟩))
    (p := bp + 8 * (1 * W lm)) (l := l) (by omega) (by omega)
  have hlen : M.readLE (pw + 24 * 1 + 8) 8 = l := (hrd _ 8 (by decide) (Or.inl ⟨by omega, by omega⟩)).trans hlen0
  have hv : natVal M (bp + 8 * (1 * W lm)) l = PV lm x xl s 1 := ev0.trans hv0
  have hn : NatNorm M (bp + 8 * (1 * W lm)) l := en0 hn0
  clear hrs0 hrd ev0 en0 hlen0 hv0 hn0
  have hpw48 := hf.pw48
  have hpwa : M.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hfr' := hfr
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, e10⟩ := hc.sl
  have f128 : M.readLE ((s.regs 4).toNat - 176 + 128) 8 = W lm := by
    rw [show (s.regs 4).toNat - 176 + 128 = (s.regs 4).toNat - 48 by omega]; exact e10
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := 1) (by omega)
  have hrs5 := rs0_st hpre hkc (rs0_st hpre hkc hrs (by omega) (bp + 8 * W lm) (a0 := pw + 24) (n0 := 8)
    (by omega) ⟨by omega, by omega⟩) (by omega) (W lm) (a0 := pw + 40) (n0 := 8) (by omega) ⟨by omega, by omega⟩
  have hk5 := keepB_trans (keepB_st hpre hkc hc (bp + 8 * W lm) (a0 := pw + 24) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs0_st hpre hkc hrs (by omega) (bp + 8 * W lm)
      (a0 := pw + 24) (n0 := 8) (by omega) ⟨by omega, by omega⟩).c (W lm)
    (a0 := pw + 40) (n0 := 8) (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨ev, en⟩ := nat_keepB hk5 (p := bp + 8 * (1 * W lm)) (l := l) (by omega) (by omega)
  have hd5 : PwD ((M.writeLE (pw + 24) 8 (bp + 8 * W lm)).writeLE (pw + 40) 8 (W lm)) pw bp lm
      (natVal s.mem x xl) 1 := by
    have r16 : ((M.writeLE (pw + 24) 8 (bp + 8 * W lm)).writeLE (pw + 40) 8 (W lm)).readLE
        (pw + 24 * 1 + 16) 8 = W lm := by
      rw [show pw + 24 * 1 + 16 = pw + 40 by omega, Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    have r0 : ((M.writeLE (pw + 24) 8 (bp + 8 * W lm)).writeLE (pw + 40) 8 (W lm)).readLE
        (pw + 24 * 1) 8 = bp + 8 * (1 * W lm) := by
      rw [show pw + 24 * 1 = pw + 24 by omega, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega), Nat.one_mul]
    have r8 : ((M.writeLE (pw + 24) 8 (bp + 8 * W lm)).writeLE (pw + 40) 8 (W lm)).readLE
        (pw + 24 * 1 + 8) 8 = M.readLE (pw + 24 * 1 + 8) 8 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    simp only [PwD]; rw [r0, r16, r8, hlen]
    exact ⟨rfl, rfl, hl, ev.trans hv, en hn⟩
  have hrs6 := rs0_next hrs5 hd5
  subst hm
  rw [Nat.one_mul] at h0
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hk5 ev en hd5 hrs hc hlen hv hn hpre hin0
  janus64_run [f128, hwm] until [pcH]
  refine kH _ bp L1 b1 hpreB.h rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ hrs6.c (fun j hj => hrs6.d j hj)
    (fun j hj hjp => hrs5.t j (by omega) hjp) (by decide) (Nat.le_refl _) (by omega)
    (by rw [show (2 : Nat) / 2 - 1 = 0 from rfl, Nat.zero_mul, Nat.add_zero]; exact hb)
  all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hx15 | rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segT (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (kH : HeadJ impl R kc b L st pw pl ws lm x xl s 2) :
    JT impl R kc b L st pw pl ws lm x xl s := by
  intro S bp L1 b1 l hpre hpc hfr h0 h3 h1 hrs hl hv hn hb
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
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hadd8 : BitVec.ofNat 64 ((s.regs 4).toNat - 184) + 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t184 : (BitVec.ofNat 64 ((s.regs 4).toNat - 184)).toNat = (s.regs 4).toNat - 184 := tN (by omega)
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
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := 1) (by omega)
  have hrs3 := rs0_st hpre hkc (rs0_st hpre hkc hrs (by omega) l (a0 := pw + 32) (n0 := 8) (by omega)
    ⟨by omega, by omega⟩) (by omega) (2 * W lm) (a0 := pw + 40) (n0 := 8) (by omega) ⟨by omega, by omega⟩
  have hk3 := keepB_trans (keepB_st hpre hkc hc l (a0 := pw + 32) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs0_st hpre hkc hrs (by omega) l (a0 := pw + 32)
      (n0 := 8) (by omega) ⟨by omega, by omega⟩).c (2 * W lm) (a0 := pw + 40) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨ev, en⟩ := nat_keepB hk3 (p := bp + 8 * (1 * W lm)) (l := l) (by omega) (by omega)
  have hlen3 : ((S.mem.writeLE (pw + 32) 8 l).writeLE (pw + 40) 8 (2 * W lm)).readLE
      (pw + 24 * 1 + 8) 8 = l := by
    rw [show pw + 24 * 1 + 8 = pw + 32 by omega, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  -- the ranges `RS0` reads are apart from the callee's return-address slot
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hboF : bp + 8 * NB pl lm ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ bp := by
    have := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
      (by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; simp only; omega)
    simp only [K, A] at this; omega
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hk3 hrs hc hpre e3
  janus64_run [f192, hwbf, hwbpw, hpwm, hwm, hsub8, t184] until [wbE, pcP]
  · -- the barrier is off
    refine jT2 hkc hpreB.h kH _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ hrs3.c (fun _ _ _ _ => rfl) hrs3 hl hlen3
      (ev.trans hv) (en hn) hb
    all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hx15 | rfl)
  · -- the barrier is on
    have hc6 := ctx_own hrs3.c hf (0x5e8900 + 0x33d) (a := (s.regs 4).toNat - 184) (k := 8)
      ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
    refine wbCall hwb hpreB.h hkc hc6 rfl (by janus64_simp) (by janus64_simp) rfl ?_ ?_
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · intro buf f2 xm2 yh2 m' zh2 kr2 hb16 hb8 hbacc hctx hrdW
      have hb8a : m'.accessible buf.toNat 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
      have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (by omega) (by omega)
      have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
      janus64_run [hb8a, hb8b, hbuf64, hadd8] until [pcP]
      have hr : ∀ v1 v2 c n, 0 < n → ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
          (W2 m' buf.toNat v1 v2).readLE c n =
            ((S.mem.writeLE (pw + 32) 8 l).writeLE (pw + 40) 8 (2 * W lm)).readLE c n := by
        intro v1 v2 c n h0 h
        refine (hrdW v1 v2 c n h0 (by simp only [RdR]; omega)).trans ?_
        exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
      refine jT2 hkc hpreB.h kH _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ (hctx _ _) (hr _ _) hrs3 hl hlen3
        (ev.trans hv) (en hn) hb
      all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hadd8 | exact hx15 | rfl)

end

end FvModexp.Amd64.P2Pre
