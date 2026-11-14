import FvModexp.Proofs.Amd64.Exp.P2PreTr

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): after the second `trunc` (`JD`) → header store of `powers[i+1]`, write
barrier, `cap ≥ w` / `len ≤ w` checks, `cap := w`, `i += 2` → loop head (`HeadJ (i + 2)`) (agent divmc s65; twin of
infra's `Arm64/Exp/P2PreD`)

`jD2`: the join after the write barrier (`+0x58c`, the pointer store), memory abstract (reads of `powers` and `buf` kept
from `M0`, the locals given): the reslice checks (`+0x599/+0x5a0`), `cap := w` (`+0x374`), `i + 2` (`+0x379`), the
loop head. `segD`: `JD` → `jD2` (the `(len, cap)` stores `+0x561/+0x566`, the barrier test `+0x56b`,
`gcWriteBarrier2` `+0x580` with its buffer stores).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

/-- the pointer store of `powers[i+1]` after the last barrier -/
abbrev pcPD : Nat := 0x5e8900 + 0x58c

theorem bud_next {c0 r i b b1 : Nat} (hi : 2 ≤ i) (hb : b - (c0 + (i / 2 - 1) * r + r) ≤ b1) :
    b - (c0 + ((i + 2) / 2 - 1) * r) ≤ b1 := by
  rw [show (i + 2) / 2 - 1 = (i / 2 - 1) + 1 by omega, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]; exact hb

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jD2 (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s) {i : Nat}
    (kH : HeadJ impl R kc b L st pw pl ws lm x xl s (i + 2)) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 l : Nat} (S : State) (hpc : S.rip = BitVec.ofNat 64 pcPD) (hfr : Frm s S 176) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * ((i + 1) * W lm))) (h3 : S.regs 3 = BitVec.ofNat 64 l)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * W lm)) (h2 : S.regs 2 = BitVec.ofNat 64 (3 * i))
    (h10 : S.regs 10 = BitVec.ofNat 64 pw)
    (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {M0 : Memory}
    (hrd : ∀ c n, 0 < n → ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
      M.readLE c n = M0.readLE c n) (hlo : Lo s i M)
    (hrs0 : RS0 R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M0 L1 b1 (i + 1)) (hl : l ≤ W lm)
    (hlen0 : M0.readLE (pw + 24 * (i + 1) + 8) 8 = l)
    (hv0 : natVal M0 (bp + 8 * ((i + 1) * W lm)) l = PV lm x xl s (i + 1))
    (hn0 : NatNorm M0 (bp + 8 * ((i + 1) * W lm)) l) (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl)
    (hb : b - (tC lm + (i / 2 - 1) * rc lm + rc lm) ≤ b1) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S (GoalQ R kc b L st pw pl lm x xl s) := by
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hin0 := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i + 1) (by omega)
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hwm : M.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hkn : (i + 1) * W lm ≤ NB pl lm := Nat.mul_le_mul_right _ (by omega)
  have hrs := rs0_rd hrs0 hc fun c n h0 h => hrd c n h0 (by omega)
  obtain ⟨ev0, en0⟩ := nat_keepB (M := M0) (M' := M) (fun c n h0 h1 h2 => hrd c n h0 (Or.inr ⟨h1, h2⟩))
    (p := bp + 8 * ((i + 1) * W lm)) (l := l) (by omega) (by omega)
  have hlen : M.readLE (pw + 24 * (i + 1) + 8) 8 = l :=
    (hrd _ 8 (by decide) (Or.inl ⟨by omega, by omega⟩)).trans hlen0
  have hv : natVal M (bp + 8 * ((i + 1) * W lm)) l = PV lm x xl s (i + 1) := ev0.trans hv0
  have hn : NatNorm M (bp + 8 * ((i + 1) * W lm)) l := en0 hn0
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
  have f120 : M.readLE ((s.regs 4).toNat - 176 + 120) 8 = i := by
    rw [show (s.regs 4).toNat - 176 + 120 = (s.regs 4).toNat - 56 by omega]; exact hlo.1
  have hrs5 := rs0_st hpre hkc (rs0_st hpre hkc hrs (by omega) (bp + 8 * ((i + 1) * W lm)) (a0 := pw + 3 * i * 8 + 24)
    (n0 := 8) (by omega) ⟨by omega, by omega⟩) (by omega) (W lm) (a0 := pw + 3 * i * 8 + 40) (n0 := 8) (by omega)
    ⟨by omega, by omega⟩
  have hk5 := keepB_trans (keepB_st hpre hkc hc (bp + 8 * ((i + 1) * W lm)) (a0 := pw + 3 * i * 8 + 24) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs0_st hpre hkc hrs (by omega) (bp + 8 * ((i + 1) * W lm))
      (a0 := pw + 3 * i * 8 + 24) (n0 := 8) (by omega) ⟨by omega, by omega⟩).c (W lm)
    (a0 := pw + 3 * i * 8 + 40) (n0 := 8) (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨ev, en⟩ := nat_keepB hk5 (p := bp + 8 * ((i + 1) * W lm)) (l := l) (by omega) (by omega)
  have hd5 : PwD ((M.writeLE (pw + 3 * i * 8 + 24) 8 (bp + 8 * ((i + 1) * W lm))).writeLE (pw + 3 * i * 8 + 40) 8
      (W lm)) pw bp lm (natVal s.mem x xl) (i + 1) := by
    have r16 : ((M.writeLE (pw + 3 * i * 8 + 24) 8 (bp + 8 * ((i + 1) * W lm))).writeLE (pw + 3 * i * 8 + 40) 8
        (W lm)).readLE (pw + 24 * (i + 1) + 16) 8 = W lm := by
      rw [show pw + 24 * (i + 1) + 16 = pw + 3 * i * 8 + 40 by omega, Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    have r0 : ((M.writeLE (pw + 3 * i * 8 + 24) 8 (bp + 8 * ((i + 1) * W lm))).writeLE (pw + 3 * i * 8 + 40) 8
        (W lm)).readLE (pw + 24 * (i + 1)) 8 = bp + 8 * ((i + 1) * W lm) := by
      rw [show pw + 24 * (i + 1) = pw + 3 * i * 8 + 24 by omega,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    have r8 : ((M.writeLE (pw + 3 * i * 8 + 24) 8 (bp + 8 * ((i + 1) * W lm))).writeLE (pw + 3 * i * 8 + 40) 8
        (W lm)).readLE (pw + 24 * (i + 1) + 8) 8 = M.readLE (pw + 24 * (i + 1) + 8) 8 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    simp only [PwD]; rw [r0, r16, r8, hlen]
    exact ⟨rfl, rfl, hl, ev.trans hv, en hn⟩
  have hrs6 := rs0_next hrs5 hd5
  have hadd2 : BitVec.ofNat 64 i + 2#64 = BitVec.ofNat 64 (i + 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  subst hm
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hk5 ev en hd5 hrs hc hlen hv hn hpre hin0
  janus64_run [f128, f120, hwm, hpwa, hl] until [pcH]
  refine kH _ bp L1 b1 hpreB.h rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ hrs6.c (fun j hj => hrs6.d j hj)
    (fun j hj hjp => hrs5.t j (by omega) hjp) (by omega) (by omega) hip (bud_next hi hb)
  all_goals first | exact hfs | exact hdf | exact hadd2 | (janus64_simp <;> first | exact hadd2 | exact hx15 | rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segD (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc) {i : Nat}
    (kH : HeadJ impl R kc b L st pw pl ws lm x xl s (i + 2)) :
    JD impl R kc b L st pw pl ws lm x xl s i := by
  intro S bp L1 b1 l hpre hpc hfr h0 h3 h1 hrs hl hv hn hi2 hi hip hb
  replace hrs : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp S.mem L1 b1 i (i + 1) := hrs
  replace h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * ((i + 1) * W lm)) := h0
  replace hv : natVal S.mem (bp + 8 * ((i + 1) * W lm)) l = PV lm x xl s (i + 1) := hv
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
  have hlen3 : ((S.mem.writeLE (pw + 3 * i * 8 + 32) 8 l).writeLE (pw + 3 * i * 8 + 40) 8 (2 * W lm)).readLE
      (pw + 24 * (i + 1) + 8) 8 = l := by
    rw [show pw + 24 * (i + 1) + 8 = pw + 3 * i * 8 + 32 by omega,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have t184 : (BitVec.ofNat 64 ((s.regs 4).toNat - 184)).toNat = (s.regs 4).toNat - 184 := tN (by omega)
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hk3 hrs hpre
  unfold Goal
  janus64_run [f192, f112, hwbf, hwbpw, hpwm, hwm, hsub8, t184] until [wbE, pcPD]
  · -- the barrier is off
    refine jD2 hkc hpreB.h kH _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_ hrs3.c
      (fun _ _ _ _ => rfl) hrs3.lo hrs3.to0 hl hlen3 (ev.trans hv) (en hn) hi2 hi hip hb
    all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hx15 | rfl)
  · -- the barrier is on
    have hc6 := ctx_own hrs3.c hf (0x5e8900 + 0x585) (a := (s.regs 4).toNat - 184) (k := 8)
      ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
    refine wbCall hwb hpreB.h hkc hc6 rfl (by janus64_simp) (by janus64_simp) rfl ?_ ?_
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · intro buf f2 xm2 yh2 m' zh2 kr2 hb16 hb8 hbacc hctx hrdW
      have hb8a : m'.accessible buf.toNat 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
      have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (by omega) (by omega)
      have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
      janus64_run [hb8a, hb8b, hbuf64, hadd8] until [pcPD]
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
      refine jD2 hkc hpreB.h kH _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_
        (hctx _ _) (hr _ _) (hlo _ _) hrs3.to0 hl hlen3 (ev.trans hv) (en hn) hi2 hi hip hb
      all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hadd8 | exact hx15 | rfl)

end

end FvModexp.Amd64.P2Pre
