import FvModexp.Proofs.Arm64.Nat.SqrCall
import FvModexp.Proofs.Arm64.Nat.DivmcCall
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.sqr` (arm64), `12 ≤ n < 80`, `stk ≠ nil`: `basicSqr(stk, z, x); return z.norm()` (natmul.go:100-103)

`bs`: the join (`+0x104`) → `CALL basicSqr` (`+0x1f4`; the defer bit `87(SP')` cleared); `bs2`: the call (`BasicSqr.ens`
with `StackNat.hyp`, its precondition `bs_pre` through `Summary.mono`), `normS` and `post_of`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem bs2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hx12 : 12 ≤ xl.toNat) (hsm : xl.toNat < 80)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb614) (hsp : S.sp = s.sp - 176#64) (h28 : S.regs 28 = s.regs 28)
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
      Kept s s' ∧ SPost R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments BasicSqr.names).link impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩ := hce
  have hsp' : S.sp.toNat = s.sp.toNat - 176 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := hJ.live (by omega); omega
  have hP := bs_pre hJ hpx hx12 hsp' h28 hF hreg
  have hBS := Summary.mono (Ensures.toSummaryRegs7 (fun a0 a1 a2 a3 a4 a5 a6 =>
    BasicSqr.ens impl hap R hmc 4208 24 (StackNat.hypL impl hap R hgr hmc hwb) (by decide) (by decide) b1 L1
      a0 a1 a2 a3 a4 a5 a6) (noExit_restrict hap BasicSqr.names) hc)
    (pre' := fun s1 => RetAddr ((Extracted.program.onlySegments BasicSqr.names).link impl) (s1.regs 30).toNat ∧
      s1.regs 0 = st ∧ s1.regs 1 = BitVec.ofNat 64 p ∧ s1.regs 2 = BitVec.ofNat 64 (2 * xl.toNat) ∧
      s1.regs 3 = BitVec.ofNat 64 c ∧ s1.regs 4 = xp ∧ s1.regs 5 = xl ∧ s1.regs 6 = xc ∧ s1.sp = S.sp ∧
      s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (fun s1 ⟨hr, h0, h1, h2, h3, h4, h5, h6, hs, hg, hm⟩ => ⟨hr, by
      rw [h0, h1, h2, h3, h4, h5]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt (show 2 * xl.toNat < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
      exact bs_pre hJ hpx hx12 (by rw [hs]; exact hsp') (by rw [hg, h28]) (by rw [hm]; exact hF)
        (by rw [hm]; exact hreg)⟩)
    (fun _ _ _ h => h)
  clear hc hP
  janus_run until [0x1bb618] calls [hBS]
  rename_i hpc2 hsp2 h282 h292 h182 L2 b2 hext hval hbud hinv2 k1 k2 k3 k4 k5 k6 k7 kl kor kmem hF2 hLF2
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
  janus_run [q64, q80] until [hnormS]
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hxv := hJ.xv (by omega)
  have hval' : natVal s'.mem p (2 * xl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [hval, natVal_frame hF (by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hxw, -⟩ := hJ.pre
      exact winA_of_win (hxw (by omega))), hxv]
  have hsb : StackBackL R L1 L2 st.toNat S.mem s'.mem :=
    ⟨⟨⟨k1, k2, by rw [hacc2]; exact k3, by omega, k5, k6, k7⟩, kl, kor⟩, kmem⟩
  have hkc : stackNatCost (stLen s.mem st.toNat) (2 * xl.toNat) ≤ ksqrC (stLen s.mem st.toNat) xl.toNat := by
    by_cases h : 80 ≤ xl.toNat
    · rw [ksqrC_big h]; omega
    · rw [ksqrC_small (by omega)]; exact Nat.le_refl _
  have hsc : sqrC (stLen s.mem st.toNat) xl.toNat = makeB (2 * xl.toNat) + ksqrC (stLen s.mem st.toNat) xl.toNat := by
    unfold sqrC; rw [if_pos hx12]
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  refine normS impl s s'.mem p c (2 * xl.toNat) (natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat) _
    (fun s3 n' hF3 q0 q1 q2 hn' hv' hnn => post_of hJ hF hval' hext
      (k := stackNatCost (stLen s.mem st.toNat) (2 * xl.toNat)) (by rw [← eL]; exact hbud) (by omega) hinv2 hsb
      (hF2.mono fun a n h => by
        simp only [BasicSqr.ws, stkWs, winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        exact ⟨⟨h.1.1, by omega, by omega⟩, h.2⟩)
      hLF2
      (hF3.mono fun a n h => by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
      q0 q1 q2 hn' (by rw [hv', hval']) hnn)
    hcap (by omega) (by omega) (by rw [hacc2]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qlr qfp q88 q89 hal0 (by omega) (by omega) hsacc hl4 hl48 (2 * xl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    hval'
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bs (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc) (hx12 : 12 ≤ xl.toNat) (hsm : xl.toNat < 80)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ SPost R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  obtain ⟨h12, h80, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r1, r2, r3, r4, r5, r6, hsp, h28, h29, h18, mlr, mfp, m64, m80, m88, hreg, hpx⟩ := hA
  have hst0 : st ≠ 0#64 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    intro e; apply h; rw [e]; rfl
  have hst0' : (st = 0#64) = False := by simp only [eq_iff_iff, iff_false]; exact hst0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hJ.pre
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -⟩, hsw, -⟩ := hpre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hsacc : S.mem.accessible (s.sp.toNat - 184) 184 true = true := by
    rw [hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  janus_run [h12, h80, hst0', toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 12) (by decide),
    toInt_small (BitVec.ofNat 64 80) (by decide)] until [0x1bb614]
  refine bs2 impl hap R hgr hmc hwb hJ hpx hx12 hsm _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [winA]; janus_frame)
    ?qreg ?q64 ?q80 ?q88 ?q89 ?qlr ?qfp hl4 hl48
  case qreg => janus_simp; exact hreg
  case q64 => janus_simp; exact m64
  case q80 => janus_simp; exact m80
  case q88 => janus_simp; exact m88
  case q89 => janus_simp
  case qlr => janus_simp; exact mlr
  case qfp => janus_simp; exact mfp
  all_goals janus_simp

end FvModexp.Arm64.NatSqr
