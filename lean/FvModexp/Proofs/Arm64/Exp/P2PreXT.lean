import FvModexp.Proofs.Arm64.Exp.P2PreX0

/-!
# `buildPrecomputationWindowModPower2` (arm64): after `trunc(x)` (`JT`) → header store of `powers[1]`, write barrier,
`cap ≥ w` / `len ≤ w` checks, `cap := w`, `i := 2` → loop head (`HeadJ 2`) (agent infra)

`jT2`: the join after the write barrier (`0x1b563c`, the pointer store), memory abstract. `segT`: `JT` → `jT2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jT2 (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s)
    (kH : HeadJ impl R kc sqC mlC b L st pw pl lm x xl s 2) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 l : Nat}
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1791548) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 208))
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216))
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * (1 * W lm))) (h1 : S.regs 1 = BitVec.ofNat 64 l)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * W lm)) (h7 : S.regs 7 = BitVec.ofNat 64 pw)
    (hrs : RS0 R kc L st pw pl lm s (natVal s.mem x xl) bp M L1 b1 1) (hl : l ≤ W lm)
    (hlen : M.readLE (pw + 24 * 1 + 8) 8 = l)
    (hv : natVal M (bp + 8 * (1 * W lm)) l = PV lm x xl s 1)
    (hn : NatNorm M (bp + 8 * (1 * W lm)) l)
    (hb : b - c0 (stLen s.mem st) pl lm ≤ b1) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hc := hrs.c
  have hwS : M.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; exact hw
  have hpw48 := hf.pw48
  have hpwa : M.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  obtain ⟨-, -, -, -, -, -, e6, e7, -, -, -, -⟩ := hc.sl
  have f144 : M.readLE (s.sp.toNat - 208 + 144) 8 = W lm := by
    rw [show s.sp.toNat - 208 + 144 = s.sp.toNat - 64 by omega]; exact e6
  have f152 : M.readLE (s.sp.toNat - 208 + 152) 8 = lm + 63 := by
    rw [show s.sp.toNat - 208 + 152 = s.sp.toNat - 56 by omega]; exact e7
  have hsh : BitVec.ofNat 64 (lm + 63) >>> 6 = BitVec.ofNat 64 (W lm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : lm + 63 < 2 ^ 64 := by have := hpre.2.2.2.2.2.2.1; omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by simp only [W]; omega)]
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
      rw [show pw + 24 * 1 + 16 = pw + 40 by omega, Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    have r0 : ((M.writeLE (pw + 24) 8 (bp + 8 * W lm)).writeLE (pw + 40) 8 (W lm)).readLE
        (pw + 24 * 1) 8 = bp + 8 * (1 * W lm) := by
      rw [show pw + 24 * 1 = pw + 24 by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := hc.scr.b48; omega), Nat.one_mul]
    have r8 : ((M.writeLE (pw + 24) 8 (bp + 8 * W lm)).writeLE (pw + 40) 8 (W lm)).readLE
        (pw + 24 * 1 + 8) 8 = M.readLE (pw + 24 * 1 + 8) 8 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    simp only [PwD]; rw [r0, r16, r8, hlen]
    exact ⟨rfl, rfl, hl, ev.trans hv, en hn⟩
  have hrs6 := rs0_next hrs5 hd5
  subst hm
  rw [Nat.one_mul] at h0
  janus_run [f144, f152, hsh] until [pcH]
  refine kH _ bp L1 b1 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ hrs6.c (fun j hj => hrs6.d j hj)
    (fun j hj hjp => hrs5.t j (by omega) hjp) (by decide) (Nat.le_refl _) (by omega)
    (by rw [show (2 : Nat) / 2 - 1 = 0 from rfl, Nat.zero_mul, Nat.add_zero]; exact hb)
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segT (hwb : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s)
    (kH : HeadJ impl R kc sqC mlC b L st pw pl lm x xl s 2) :
    JT impl R kc sqC mlC b L st pw pl lm x xl s := by
  intro S bp L1 b1 l hpc hsp h28 h29 h18 h0 h1 h2 hrs hl hv hn hb
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hc := hrs.c
  have hwS : S.mem.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; exact hw
  have hpw48 := hf.pw48
  have hpwa : S.mem.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  have hgl := globals_ctx hpre hc (S' := S) (by rw [hsp, BitVec.toNat_ofNat]; omega) (stk := 4096) (above := 8)
    (by omega) (by omega)
  have hwbf : S.mem.accessible RunIface.wbA 4 false = true := hgl.2.2.2.2.2.2.2.2.2.2.1
  have hwbv : RunIface.wbA = 7616064 := rfl
  rw [hwbv] at hwbf
  have hwbpw : 7616064 + 4 ≤ pw ∨ pw + 24 * pl ≤ 7616064 := by
    have := hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true] at this
    rw [hwbv] at this; omega
  obtain ⟨-, -, -, e3, -, -, -, -, -, -, -, -⟩ := hc.sl
  have f224 : S.mem.readLE (s.sp.toNat - 208 + 224) 8 = pw := by
    rw [show s.sp.toNat - 208 + 224 = s.sp.toNat + 16 by omega]; exact e3
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
    rw [show pw + 24 * 1 + 8 = pw + 32 by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.one_mul] at h0
  unfold Goal
  janus_run [f224, hwbf, hwbpw] until [wbE, 1791548]
  · -- the barrier is off
    refine jT2 hkc hpre kH _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ hrs3 hl hlen3 (ev.trans hv) (en hn) hb
    all_goals janus_simp
  · -- the barrier is on
    refine wbCall hwb hpre hkc hrs3.c rfl rfl (by janus_simp) rfl (ra := 1791544) (by janus_simp) (by decide) (by decide)
      fun buf junk f v m' ex ep hb48 hbal hbacc hctx hrd => ?_
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hbacc (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    janus_run [hb8a, hb8b, hbuf64] until [1791548]
    obtain ⟨hrsW, hkW⟩ := rs0_of_rdr hrs3 (hctx (bp + 8 * W lm)
      (S.mem.readLE (pw + 24) 8)) (by omega) (hrd _ _)
    obtain ⟨ev', en'⟩ := nat_keepB (keepB_trans hk3 hkW) (p := bp + 8 * (1 * W lm)) (l := l) (by omega)
      (by omega)
    refine jT2 hkc hpre kH _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ hrsW hl
      ((hrd _ _ _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans hlen3) (ev'.trans hv) (en' hn) hb
    all_goals janus_simp

end

end FvModexp.Arm64.P2Pre
