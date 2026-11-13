import FvModexp.Proofs.Arm64.Exp.P2PreWbC
import FvModexp.Proofs.Arm64.Exp.P2PreMu

/-!
# `buildPrecomputationWindowModPower2` (arm64): after the first `trunc` (`JB`) → header store, write barrier,
`cap ≥ w` / `len ≤ w` checks, `powers[i] = (…)[: :w]` → `nat.mul` → `JC` (agent infra)

`jB2`: the join after the write barrier (`0x1b577c`, the pointer store), memory abstract. `segB`: `JB` → `jB2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jB2 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c') (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (kC : JC impl R kc sqC mlC b L st pw pl lm x xl s i) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 l : Nat}
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1791868) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 208))
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216))
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * (i * W lm))) (h1 : S.regs 1 = BitVec.ofNat 64 l)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * W lm)) (h7 : S.regs 7 = BitVec.ofNat 64 (pw + 24 * i))
    (h10 : S.regs 10 = BitVec.ofNat 64 (24 * i)) (h11 : S.regs 11 = BitVec.ofNat 64 pw)
    (hrs : RS R kc L st pw pl lm s (natVal s.mem x xl) bp M L1 b1 i i) (hlo2 : Lo2 s pw i M) (hl : l ≤ W lm)
    (hv : natVal M (bp + 8 * (i * W lm)) l = PV lm x xl s i) (hn : NatNorm M (bp + 8 * (i * W lm)) l)
    (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl)
    (hb : b - (c0 (stLen s.mem st) pl lm + (i / 2 - 1) * rc sqC mlC (stLen s.mem st) pl lm +
      (sqC (lvl1 (stLen s.mem st) pl lm) (W lm) + tC lm)) ≤ b1) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
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
  obtain ⟨-, -, e2, e3, -, -, e6, e7, -, -, -, -⟩ := hc.sl
  obtain ⟨-, -, l2, -⟩ := hrs.lo
  have f128 : M.readLE (s.sp.toNat - 208 + 128) 8 = 24 * i + 24 := by
    rw [show s.sp.toNat - 208 + 128 = s.sp.toNat - 80 by omega]; exact l2
  have f144 : M.readLE (s.sp.toNat - 208 + 144) 8 = W lm := by
    rw [show s.sp.toNat - 208 + 144 = s.sp.toNat - 64 by omega]; exact e6
  have f152 : M.readLE (s.sp.toNat - 208 + 152) 8 = lm + 63 := by
    rw [show s.sp.toNat - 208 + 152 = s.sp.toNat - 56 by omega]; exact e7
  have f184 : M.readLE (s.sp.toNat - 208 + 184) 8 = pw + 24 * i + 24 := by
    rw [show s.sp.toNat - 208 + 184 = s.sp.toNat - 24 by omega]; exact hlo2
  have f216 : M.readLE (s.sp.toNat - 208 + 216) 8 = st := by
    rw [show s.sp.toNat - 208 + 216 = s.sp.toNat + 8 by omega]; exact e2
  obtain ⟨t0, t1, t2⟩ := hrs.t (i + 1) (by omega) (by omega)
  obtain ⟨d0, d2, d1, -, -⟩ := hrs.d 1 (by omega)
  have hsh : BitVec.ofNat 64 (lm + 63) >>> 6 = BitVec.ofNat 64 (W lm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : lm + 63 < 2 ^ 64 := by have := hpre.2.2.2.2.2.2.1; omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by simp only [W]; omega)]
  have m0 : S.mem.readLE (pw + (24 * i + 24)) 8 = bp + 8 * ((i + 1) * W lm) := by
    rw [hm, show pw + (24 * i + 24) = pw + 24 * (i + 1) by omega]; exact t0
  have m1 : S.mem.readLE (pw + 24 * i + 24 + 8) 8 = W lm := by
    rw [hm, show pw + 24 * i + 24 + 8 = pw + 24 * (i + 1) + 8 by omega]; exact t1
  have m2 : S.mem.readLE (pw + 24 * i + 24 + 16) 8 = 2 * W lm := by
    rw [hm, show pw + 24 * i + 24 + 16 = pw + 24 * (i + 1) + 16 by omega]; exact t2
  have m24 : S.mem.readLE (pw + 24) 8 = bp + 8 * W lm := by rw [hm]; simpa using d0
  have m40 : S.mem.readLE (pw + 40) 8 = W lm := by rw [hm]; simpa using d2
  have hip' : i < pl := by omega
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i) (by omega)
  -- the memory at the `mul` call: `powers[i] = (ptr, l, w)`
  have hrs5 := rs_st hpre hkc (rs_st hpre hkc (rs_st hpre hkc hrs hip' (bp + 8 * (i * W lm)) (a0 := pw + 24 * i)
    (n0 := 8) (by omega) (Or.inl ⟨by omega, by omega⟩)) hip' l (a0 := pw + 24 * i + 8) (n0 := 8) (by omega)
    (Or.inl ⟨by omega, by omega⟩)) hip' (W lm) (a0 := pw + 24 * i + 16) (n0 := 8) (by omega)
    (Or.inl ⟨by omega, by omega⟩)
  have hk5 := keepB_trans (keepB_trans (keepB_st hpre hkc hc (bp + 8 * (i * W lm)) (a0 := pw + 24 * i) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs_st hpre hkc hrs hip' (bp + 8 * (i * W lm))
      (a0 := pw + 24 * i) (n0 := 8) (by omega) (Or.inl ⟨by omega, by omega⟩)).c l (a0 := pw + 24 * i + 8) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩))) (keepB_st hpre hkc (rs_st hpre hkc (rs_st hpre hkc hrs hip' (bp + 8 * (i * W lm))
      (a0 := pw + 24 * i) (n0 := 8) (by omega) (Or.inl ⟨by omega, by omega⟩)) hip' l (a0 := pw + 24 * i + 8)
      (n0 := 8) (by omega) (Or.inl ⟨by omega, by omega⟩)).c (W lm) (a0 := pw + 24 * i + 16) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨ev, en⟩ := nat_keepB hk5 (p := bp + 8 * (i * W lm)) (l := l) (by omega) (by omega)
  have r16 : (((M.writeLE (pw + 24 * i) 8 (bp + 8 * (i * W lm))).writeLE (pw + 24 * i + 8) 8 l).writeLE
      (pw + 24 * i + 16) 8 (W lm)).readLE (pw + 24 * i + 16) 8 = W lm := by
    rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have r8 : (((M.writeLE (pw + 24 * i) 8 (bp + 8 * (i * W lm))).writeLE (pw + 24 * i + 8) 8 l).writeLE
      (pw + 24 * i + 16) 8 (W lm)).readLE (pw + 24 * i + 8) 8 = l := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have r0 : (((M.writeLE (pw + 24 * i) 8 (bp + 8 * (i * W lm))).writeLE (pw + 24 * i + 8) 8 l).writeLE
      (pw + 24 * i + 16) 8 (W lm)).readLE (pw + 24 * i) 8 = bp + 8 * (i * W lm) := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := hc.scr.b48; omega)]
  have r32 : (((M.writeLE (pw + 24 * i) 8 (bp + 8 * (i * W lm))).writeLE (pw + 24 * i + 8) 8 l).writeLE
      (pw + 24 * i + 16) 8 (W lm)).readLE (pw + 24 * 1 + 8) 8 = M.readLE (pw + 32) 8 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hd5 : PwD (((M.writeLE (pw + 24 * i) 8 (bp + 8 * (i * W lm))).writeLE (pw + 24 * i + 8) 8 l).writeLE
      (pw + 24 * i + 16) 8 (W lm)) pw bp lm (natVal s.mem x xl) i := by
    simp only [PwD]; rw [r0, r16, r8]; exact ⟨rfl, rfl, hl, ev.trans hv, en hn⟩
  have hlo5 := lo2_st hpre hkc (W lm) (lo2_st hpre hkc l (lo2_st hpre hkc (bp + 8 * (i * W lm)) hlo2
    (a0 := pw + 24 * i) (n0 := 8) ⟨by omega, by omega⟩) (a0 := pw + 24 * i + 8) (n0 := 8) ⟨by omega, by omega⟩)
    (a0 := pw + 24 * i + 16) (n0 := 8) ⟨by omega, by omega⟩
  subst hm
  janus_run [f128, f144, f152, f184, f216, m0, m1, m2, m24, m40, hsh] until [1814128]
  refine callMulH hap hns hnf hmu hkM haM hmm hkc hpre kC (rs_next hrs5 hd5) hlo5 hi2 hi hip hb _ ?_ ?_ ?_ ?_ rfl ?_ ?_
    ?_ ?_ ?_ ?_ ?_ r8 ?_ ?_ ?_ r32 ?_ ?_
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segB (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (kC : JC impl R kc sqC mlC b L st pw pl lm x xl s i) :
    JB impl R kc sqC mlC b L st pw pl lm x xl s i := by
  intro S bp L1 b1 l hpc hsp h28 h29 h18 h0 h1 h2 hrs hlo2 hl hv hn hi2 hi hip hb
  replace hrs : RS R kc L st pw pl lm s (natVal s.mem x xl) bp S.mem L1 b1 i i := hrs
  replace h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * (i * W lm)) := h0
  replace hv : natVal S.mem (bp + 8 * (i * W lm)) l = PV lm x xl s i := hv
  replace hn : NatNorm S.mem (bp + 8 * (i * W lm)) l := hn
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
  obtain ⟨-, -, -, e3, -, -, -, -, -, -, -, -⟩ := hc.sl
  obtain ⟨-, l1, -, l3⟩ := hrs.lo
  have f192 : S.mem.readLE (s.sp.toNat - 208 + 192) 8 = pw + 24 * i := by
    rw [show s.sp.toNat - 208 + 192 = s.sp.toNat - 16 by omega]; exact l3
  have f136 : S.mem.readLE (s.sp.toNat - 208 + 136) 8 = 24 * i := by
    rw [show s.sp.toNat - 208 + 136 = s.sp.toNat - 72 by omega]; exact l1
  have f224 : S.mem.readLE (s.sp.toNat - 208 + 224) 8 = pw := by
    rw [show s.sp.toNat - 208 + 224 = s.sp.toNat + 16 by omega]; exact e3
  have hip' : i < pl := by omega
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i) (by omega)
  have hrs3 := rs_st hpre hkc (rs_st hpre hkc hrs hip' l (a0 := pw + 24 * i + 8) (n0 := 8) (by omega)
    (Or.inl ⟨by omega, by omega⟩)) hip' (2 * W lm) (a0 := pw + 24 * i + 16) (n0 := 8) (by omega)
    (Or.inl ⟨by omega, by omega⟩)
  have hlo3 := lo2_st hpre hkc (2 * W lm) (lo2_st hpre hkc l hlo2 (a0 := pw + 24 * i + 8) (n0 := 8)
    ⟨by omega, by omega⟩) (a0 := pw + 24 * i + 16) (n0 := 8) ⟨by omega, by omega⟩
  have hk3 := keepB_trans (keepB_st hpre hkc hc l (a0 := pw + 24 * i + 8) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs_st hpre hkc hrs hip' l (a0 := pw + 24 * i + 8) (n0 := 8)
      (by omega) (Or.inl ⟨by omega, by omega⟩)).c (2 * W lm) (a0 := pw + 24 * i + 16) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩))
  obtain ⟨ev, en⟩ := nat_keepB hk3 (p := bp + 8 * (i * W lm)) (l := l) (by omega) (by omega)
  unfold Goal
  janus_run [f192, f136, f224, hwbf] until [wbE, 1791868]
  · -- the barrier is off
    refine jB2 hap hns hnf hmu hkM haM hmm hkc hpre kC _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ hrs3 hlo3 hl
      (ev.trans hv) (en hn) hi2 hi hip hb
    all_goals janus_simp
  · -- the barrier is on
    refine wbCall hwb hpre hkc hrs3.c rfl rfl (by janus_simp) rfl (ra := 1791864) (by janus_simp) (by decide) (by decide)
      fun buf junk f v m' ex ep hb48 hbal hbacc hctx hrd => ?_
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hbacc (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    janus_run [hb8a, hb8b, hbuf64] until [1791868]
    obtain ⟨hrsW, hloW, hkW⟩ := rs_of_rdr hrs3 (hctx (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 24 * i) 8)) (by omega)
      (by omega) (hrd _ _)
    obtain ⟨ev', en'⟩ := nat_keepB (keepB_trans hk3 hkW) (p := bp + 8 * (i * W lm)) (l := l) (by omega) (by omega)
    refine jB2 hap hns hnf hmu hkM haM hmm hkc hpre kC _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ hrsW (hloW hlo3) hl
      (ev'.trans hv) (en' hn) hi2 hi hip hb
    all_goals janus_simp

end

end FvModexp.Arm64.P2Pre
