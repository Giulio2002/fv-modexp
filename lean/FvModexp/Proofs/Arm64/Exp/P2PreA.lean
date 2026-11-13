import FvModexp.Proofs.Arm64.Exp.P2PreWbC
import FvModexp.Proofs.Arm64.Exp.P2PreTr

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (arm64): after `sqr` (`JA`) → header store, write barrier → `trunc` → `JB`
(agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat} {mlC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segA (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (kB : JB impl R kc sqC mlC b L st pw pl lm x xl s i) :
    JA impl R kc sqC mlC b L st pw pl lm x xl s i := by
  intro S bp L1 b1 l hpc hsp h28 h29 h18 h0 h1 h2 hrs _ hl hv hn hi2 hi hip hb
  replace hrs : RS R kc L st pw pl lm s (natVal s.mem x xl) bp S.mem L1 b1 i i := hrs
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
  obtain ⟨-, -, -, e3, -, e5, -, -, -, -, -, -⟩ := hc.sl
  obtain ⟨l0, l1, l2, l3⟩ := hrs.lo
  have f192 : S.mem.readLE (s.sp.toNat - 208 + 192) 8 = pw + 24 * i := by
    rw [show s.sp.toNat - 208 + 192 = s.sp.toNat - 16 by omega]; exact l3
  have f128 : S.mem.readLE (s.sp.toNat - 208 + 128) 8 = 24 * i + 24 := by
    rw [show s.sp.toNat - 208 + 128 = s.sp.toNat - 80 by omega]; exact l2
  have f136 : S.mem.readLE (s.sp.toNat - 208 + 136) 8 = 24 * i := by
    rw [show s.sp.toNat - 208 + 136 = s.sp.toNat - 72 by omega]; exact l1
  have f224 : S.mem.readLE (s.sp.toNat - 208 + 224) 8 = pw := by
    rw [show s.sp.toNat - 208 + 224 = s.sp.toNat + 16 by omega]; exact e3
  have f256 : S.mem.readLE (s.sp.toNat - 208 + 256) 8 = lm := by
    rw [show s.sp.toNat - 208 + 256 = s.sp.toNat + 48 by omega]; exact e5
  have hip' : i < pl := by omega
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i) (by omega)
  have hsp24 : s.sp.toNat - 208 + 184 = s.sp.toNat - 24 := by omega
  -- the memory before the barrier: header (len, cap), `&powers[i+1]` at `SP - 24`
  have hrs3 := rs_st hpre hkc (rs_st hpre hkc (rs_st hpre hkc hrs hip' l (a0 := pw + 24 * i + 8) (n0 := 8) (by omega)
    (Or.inl ⟨by omega, by omega⟩)) hip' (2 * W lm) (a0 := pw + 24 * i + 16) (n0 := 8) (by omega)
    (Or.inl ⟨by omega, by omega⟩)) hip' (24 * i + 24 + pw) (a0 := s.sp.toNat - 208 + 184) (n0 := 8) (by omega)
    (Or.inr ⟨by omega, by omega⟩)
  have hlo3 : Lo2 s pw i (((S.mem.writeLE (pw + 24 * i + 8) 8 l).writeLE (pw + 24 * i + 16) 8 (2 * W lm)).writeLE
      (s.sp.toNat - 208 + 184) 8 (24 * i + 24 + pw)) := lo2_set hsp24 (by omega) (by omega)
  have hk3 := keepB_trans (keepB_trans (keepB_st hpre hkc hc l (a0 := pw + 24 * i + 8) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩)) (keepB_st hpre hkc (rs_st hpre hkc hrs hip' l (a0 := pw + 24 * i + 8) (n0 := 8)
      (by omega) (Or.inl ⟨by omega, by omega⟩)).c (2 * W lm) (a0 := pw + 24 * i + 16) (n0 := 8)
    (Or.inl ⟨by omega, by omega⟩))) (keepB_st hpre hkc (rs_st hpre hkc (rs_st hpre hkc hrs hip' l
      (a0 := pw + 24 * i + 8) (n0 := 8) (by omega) (Or.inl ⟨by omega, by omega⟩)) hip' (2 * W lm)
      (a0 := pw + 24 * i + 16) (n0 := 8) (by omega) (Or.inl ⟨by omega, by omega⟩)).c (24 * i + 24 + pw)
    (a0 := s.sp.toNat - 208 + 184) (n0 := 8) (Or.inr ⟨by omega, by omega⟩))
  have hvT : PV lm x xl s i = PV lm x xl s (i / 2) * PV lm x xl s (i / 2) % 2 ^ lm := p2_even hi hi2
  unfold Goal
  janus_run [f192, f128, f136, f224, f256, hwbf] until [wbE, 1786000]
  · -- the barrier is off
    have hrs4 := rs_st hpre hkc hrs3 hip' (bp + 8 * (i * W lm)) (a0 := pw + 24 * i) (n0 := 8) (by omega)
      (Or.inl ⟨by omega, by omega⟩)
    have hk4 := keepB_trans hk3 (keepB_st hpre hkc hrs3.c (bp + 8 * (i * W lm)) (a0 := pw + 24 * i) (n0 := 8)
      (Or.inl ⟨by omega, by omega⟩))
    obtain ⟨ev, en⟩ := nat_keepB hk4 (p := bp + 8 * (i * W lm)) (l := l) (by omega) (by omega)
    refine callTr hap hns hnf htr hkT haT hkc hpre (ri := 222) (by decide) (by decide) kB (Nat.le_refl _)
      (Nat.le_succ _) rfl (by simp only [rc]; omega) hrs4 (lo2_st hpre hkc _ hlo3 ⟨by omega, by omega⟩) hi2 hi hip hb hl
      (en hn) (ev.trans hv) hvT _ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals janus_simp
  · -- the barrier is on
    refine wbCall hwb hpre hkc hrs3.c rfl rfl (by janus_simp) rfl (ra := 1791788) (by janus_simp) (by decide) (by decide)
      fun buf junk f v m' ex ep hb48 hbal hbacc hctx hrd => ?_
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hbacc (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hacc' : ∀ a n w, m'.accessible a n w = s.mem.accessible a n w := fun a n w => by
      have := (hctx 0 0).fr.accessible a n w
      simp only [W2, Memory.accessible_writeLE] at this
      exact this
    have hpwa' : m'.accessible pw (24 * pl) true = true := by rw [hacc']; exact hpre.2.2.2.2.2.2.2.2.2.1
    have hwS' : m'.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by rw [hacc']; exact hw
    have hlmW : ∀ v1 v2, ((m'.writeLE buf.toNat 8 v1).writeLE (buf.toNat + 8) 8 v2).readLE
        (s.sp.toNat - 208 + 256) 8 = lm := fun v1 v2 => by
      rw [show ((m'.writeLE buf.toNat 8 v1).writeLE (buf.toNat + 8) 8 v2) = W2 m' buf.toNat v1 v2 from rfl,
        hrd v1 v2 _ 8 (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact f256
    janus_run [hb8a, hb8b, hbuf64, hpwa', hwS', hlmW] until [1786000]
    obtain ⟨hrsW, hloW, hkW⟩ := rs_of_rdr hrs3 (hctx (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 24 * i) 8)) (by omega)
      (by omega) (hrd _ _)
    have hrs4 := rs_st hpre hkc hrsW hip' (bp + 8 * (i * W lm)) (a0 := pw + 24 * i) (n0 := 8) (by omega)
      (Or.inl ⟨by omega, by omega⟩)
    have hk4 := keepB_trans (keepB_trans hk3 hkW) (keepB_st hpre hkc hrsW.c (bp + 8 * (i * W lm)) (a0 := pw + 24 * i)
      (n0 := 8) (Or.inl ⟨by omega, by omega⟩))
    obtain ⟨ev, en⟩ := nat_keepB hk4 (p := bp + 8 * (i * W lm)) (l := l) (by omega) (by omega)
    refine callTr hap hns hnf htr hkT haT hkc hpre (ri := 222) (by decide) (by decide) kB (Nat.le_refl _)
      (Nat.le_succ _) rfl (by simp only [rc]; omega) hrs4 (lo2_st hpre hkc _ (hloW hlo3) ⟨by omega, by omega⟩) hi2 hi
      hip hb hl (en hn) (ev.trans hv) hvT _ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals janus_simp
end

end FvModexp.Arm64.P2Pre
