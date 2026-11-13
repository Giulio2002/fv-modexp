import FvModexp.Proofs.Arm64.NatQ.SqrKPre
import FvModexp.Proofs.Arm64.Nat.DivmcCall
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.WinLemmas

/-!
# [Q-form copy of Arm64/Nat/SqrKS.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `80 ≤ n`, `stk ≠ nil`: `karatsubaSqr(stk, z, x); return z.norm()` (natmul.go:105-106)

`ks`: the join (`+0x104`) → `CALL karatsubaSqr` (`+0x220`); `ks2`: the call through the induction hypothesis of the SCC
(`IH … (true, a)`, measure `2n < 2n + 1`; precondition `ks_pre`), `normK` and `post_of`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem ks2 (impl : List Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 M)
    (hih : ∀ a, IH impl R H (2 * xl.toNat + 1) (true, a))
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hna : p + 8 * c ≠ xp.toNat + 8 * xc.toNat) (hx80 : 80 ≤ xl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb640) (hsp : S.sp = s.sp - 176#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 184#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = st) (r1 : S.regs 1 = BitVec.ofNat 64 p) (r2 : S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat))
    (r3 : S.regs 3 = BitVec.ofNat 64 c) (r4 : S.regs 4 = xp) (r5 : S.regs 5 = xl) (r6 : S.regs 6 = xc)
    (hF : MemFrame M S.mem (winA s W 64)) (hreg : S.mem.regions = s.mem.regions)
    (m64 : S.mem.readLE (s.sp.toNat - 64) 8 = p) (m80 : S.mem.readLE (s.sp.toNat - 80) 8 = 2 * xl.toNat)
    (m88 : S.mem.readLE (s.sp.toNat - 88) 8 = c) (m89 : S.mem.readLE (s.sp.toNat - 89) 1 = 0)
    (mlr : S.mem.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩ := hce
  have hsp' : S.sp.toNat = s.sp.toNat - 176 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := hJ.live (by omega); omega
  have e1 : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 (2 * xl.toNat)).toNat = 2 * xl.toNat := by simp only [BitVec.toNat_ofNat]; omega
  have e3 : (BitVec.ofNat 64 c).toNat = c := by simp only [BitVec.toNat_ofNat]; omega
  have hBS : Summary (LibSqr.program.link impl) 0x1bc2b0 _ _ := Summary.mono (hih ⟨b1, L1, W - 176, st, BitVec.ofNat 64 p, BitVec.ofNat 64 (2 * xl.toNat),
      BitVec.ofNat 64 c, xp, xl, xc⟩)
    (pre' := fun s1 => (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48 ∧
      s1.regs 0 = st ∧ s1.regs 1 = BitVec.ofNat 64 p ∧ s1.regs 2 = BitVec.ofNat 64 (2 * xl.toNat) ∧
      s1.regs 3 = BitVec.ofNat 64 c ∧ s1.regs 4 = xp ∧ s1.regs 5 = xl ∧ s1.regs 6 = xc ∧ s1.sp = S.sp ∧
      s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (post' := fun s1 s2 => Kept s1 s2 ∧ KPost R b1 H L1 (W - 176) st.toNat p (2 * xl.toNat) xp.toNat xl.toNat s1 s2)
    (fun s1 ⟨hr4, hr48, h0, h1, h2, h3, h4, h5, h6, hs, hg, hm⟩ => by
      refine ⟨⟨⟨hr4, hr48, h0, h1, h2, h3, h4, h5, h6⟩, ?_⟩, ?_⟩
      · show KPre R b1 H L1 (W - 176) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * xl.toNat)).toNat
          (BitVec.ofNat 64 c).toNat xp.toNat xl.toNat xc.toNat s1
        rw [e1, e2, e3]
        exact ks_pre hJ hpx hna hx80 (by rw [hs]; exact hsp') (by rw [hg, h28]) (by rw [hm]; exact hF)
          (by rw [hm]; exact hreg)
      · show 2 * xl.toNat < 2 * xl.toNat + 1; omega)
    (fun s1 s2 _ ⟨hk, hq⟩ => by
      refine ⟨hk, ?_⟩
      have hq' : KPost R b1 H L1 (W - 176) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * xl.toNat)).toNat
          xp.toNat xl.toNat s1 s2 := hq
      rw [e1, e2] at hq'; exact hq')
  janus_run until [0x1bb644] calls [hBS]
  rename_i hpc2 hsp2 h282 h292 h182 hval L2 b2 hext hbud kmem k1 k2 k5 k6 k7 kl kor hF2 hLF2 hinv2 k3 k4
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hpc2 hsp2 h282 h292 h182
  have e176 : (s.sp - 176#64).toNat = s.sp.toNat - 176 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  simp only [winA, e176] at hF2
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hrd' : ∀ a n, s.sp.toNat - 184 ≤ a → a + n ≤ s.sp.toNat - 168 ∨ s.sp.toNat - 112 ≤ a →
      a + n ≤ s.sp.toNat → s'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    have hst := (hJ.stk)
    refine hF2.readLE _ _ ?_
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
    simp only [win, outside_cons, outside_nil, and_true] at hstw
    have hfw := hJ.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
    obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
    simp only [win, outside_cons, outside_nil, and_true] at hfw
    simp only [BasicSqr.ws, stkWs, outside_append, outside_cons, outside_nil, and_true]
    simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
    rw [eW, eL, eC]
    exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega, by omega⟩
  have hrd : ∀ a, s.sp.toNat - 184 ≤ a → a + 8 ≤ s.sp.toNat - 168 ∨ s.sp.toNat - 112 ≤ a → a + 8 ≤ s.sp.toNat →
      s'.mem.readLE a 8 = S.mem.readLE a 8 := fun a => hrd' a 8
  have q89 := (hrd' _ 1 (by omega) (Or.inr (by omega)) (by omega)).trans m89
  have q64 := (hrd _ (by omega) (Or.inr (by omega)) (by omega)).trans m64
  have q80 := (hrd _ (by omega) (Or.inr (by omega)) (by omega)).trans m80
  have q88 := (hrd _ (by omega) (Or.inr (by omega)) (by omega)).trans m88
  have qlr := (hrd _ (by omega) (Or.inl (by omega)) (by omega)).trans mlr
  have qfp := (hrd _ (by omega) (Or.inl (by omega)) (by omega)).trans mfp
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF.accessible]
  have hsacc : s'.mem.accessible (s.sp.toNat - 184) 184 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsacc' : s'.mem.accessible (s.sp.toNat - 184) 184 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  janus_run [q64, q80] until [hnormK]
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hxv := hJ.xv (by omega)
  have hval' : natVal s'.mem p (2 * xl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [hval, natVal_frame hF (by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hxw, -⟩ := hJ.pre
      exact winA_of_win (hxw (by omega))), hxv]
  have hsb : StackBackL R L1 L2 st.toNat S.mem s'.mem :=
    ⟨⟨⟨k1, k2, by rw [hacc2]; exact k3, by omega, k5, k6, k7⟩, kl, kor⟩, kmem⟩
  have hsc : sqrCQ xl.toNat = makeB (2 * xl.toNat) + ksqrCQ xl.toNat := by
    unfold sqrCQ; rw [if_pos (by omega)]
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  refine normK impl s s'.mem p c (2 * xl.toNat) (natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat) _
    (fun s3 n' hF3 q0 q1 q2 hn' hv' hnn => post_of hJ hF hval' hext
      (k := ksqrCQ xl.toNat) (Or.inl hbud) (by omega) hinv2 hsb
      (hF2.mono fun a n h => by
        simp only [stkWs, winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        have hk := Nat.le_of_eq (Nat.add_sub_cancel' (Nat.le_trans (show 176 ≤ 4880 by decide) hW))
        exact ⟨⟨h.1.1, (winA_in (c := 176) (k := (W - 176)) (ab := 48) hb0 hk (by decide) h.1.2.1).1, (winA_in (c := 176) (k := (W - 176)) (ab := 48) hb0 hk (by decide) h.1.2.1).2⟩, h.2⟩)
      hLF2
      (hF3.mono fun a n h => by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
      q0 q1 q2 hn' (by rw [hv', hval']) hnn)
    hcap (by omega) (by omega) (by rw [hacc2]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qlr qfp q88 q89 hal0 (by omega) (by omega) hsacc hl4 hl48 (2 * xl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    hval'
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ks (impl : List Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem)
    (hih : ∀ a, IH impl R H (2 * xl.toNat + 1) (true, a))
    (hA : JoinAt s S p c st xp xl xc) (hx80 : 80 ≤ xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  obtain ⟨h12, h80, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r1, r2, r3, r4, r5, r6, hsp, h28, h29, h18, mlr, mfp, m64, m80, m88, hreg, hpx, hna⟩ := hA
  have hst0 : st ≠ 0#64 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    intro e; apply h; rw [e]; rfl
  have hst0' : (st = 0#64) = False := by simp only [eq_iff_iff, iff_false]; exact hst0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hJ.pre
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -⟩, hsw, -, -, -, -, -, hxl12, -⟩ := hpre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hsacc : S.mem.accessible (s.sp.toNat - 184) 184 true = true := by
    rw [hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  janus_run [h12, h80, hst0', toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 12) (by decide),
    toInt_small (BitVec.ofNat 64 80) (by decide)] until [0x1bb640]
  refine ks2 impl R hJ hih hpx hna hx80 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [winA]; janus_frame)
    ?qreg ?q64 ?q80 ?q88 ?q89 ?qlr ?qfp hl4 hl48
  case qreg => janus_simp; exact hreg
  case q64 => janus_simp; exact m64
  case q80 => janus_simp; exact m80
  case q88 => janus_simp; exact m88
  case q89 => janus_simp
  case qlr => janus_simp; exact mlr
  case qfp => janus_simp; exact mfp
  all_goals janus_simp

end FvModexp.Arm64.Q.NatSqr
