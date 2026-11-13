import FvModexp.Proofs.Arm64.NatQ.SqrCall
import FvModexp.Proofs.Arm64.Nat.DivmcCall
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.WinLemmas

/-!
# [Q-form copy of Arm64/Nat/SqrBM.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `2 ≤ n < 12`: `basicMul(z, x, x); return z.norm()` (natmul.go:90-93)

`bm`: the join (`+0x104`) → `CALL basicMul` (`+0x13c`, both thresholds loaded); `bm2`: the call (`BasicMul.ens`, its
`CallEnv` from `Core.callee`), then `normM` and `post_of`.
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
theorem bm2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hx2 : 2 ≤ xl.toNat) (hsm : xl.toNat < 12)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb55c) (hsp : S.sp = s.sp - 176#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 184#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = BitVec.ofNat 64 p) (r1 : S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat))
    (r2 : S.regs 2 = BitVec.ofNat 64 c) (r3 : S.regs 3 = xp) (r4 : S.regs 4 = xl) (r5 : S.regs 5 = xc)
    (r6 : S.regs 6 = xp) (r7 : S.regs 7 = xl) (r8 : S.regs 8 = xc)
    (hF : MemFrame M S.mem (winA s W 64)) (hreg : S.mem.regions = s.mem.regions)
    (m64 : S.mem.readLE (s.sp.toNat - 64) 8 = p) (m80 : S.mem.readLE (s.sp.toNat - 80) 8 = 2 * xl.toNat)
    (m88 : S.mem.readLE (s.sp.toNat - 88) 8 = c)
    (mlr : S.mem.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments BasicMul.names).link impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hBM := Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b1 L1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (noExit_restrict hap BasicMul.names) hc
  clear hc
  simp only [BasicMul.Pre, CallEnv] at hBM
  have hpre := hJ.pre
  obtain ⟨hce, hsw, hsv, -, -, hxlc, hxc40, hxl12, hxacc, hxh, hxw, -, -, -, -, -, hstk, -, -, -, -⟩ := hpre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, hLs0, -⟩ := hce
  have hsp' : S.sp.toNat = s.sp.toNat - 176 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hce1 := hJ.callee (stk1 := 4224) (above1 := 72) hsp' h28 hF hreg (by omega) (by omega)
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce1
  simp only [LiveSep, win, outside_cons, outside_nil, and_true] at hLs
  rw [h28] at hg1 hg2 hg3 hga hgr
  rw [hsp'] at hg3 hga hout hLs hw
  unfold Apart at hga
  have hinv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S.mem) :=
    inv_frame_winA hF hout0 (by omega) (by decide) hJ.inv
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hpg : Apart p (8 * c) ((s.regs 28).toNat + 16) 8 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hzg, -⟩ := hJ.pre
    rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
    · exact (hzg (by omega)).1
    · obtain ⟨-, -, -, -, -, hgr0, -⟩ := hJ.pre.1
      have := NatAdd.outside_of_inRanges hgr0 hin; unfold Apart; omega
  unfold Apart at hpx hpg
  have hxw' := hxw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hxw'
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  have hxh1 : Held R L1 xp.toNat (8 * xl.toNat) := hJ.ext.held (hxh'.sub (Nat.le_refl _) (by omega))
  have hpaccS : S.mem.accessible p (8 * (xl.toNat + xl.toNat)) true = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)
  have hxaccS : S.mem.accessible xp.toNat (8 * xl.toNat) false = true := by
    rw [hF.accessible, hJ.F.accessible]; exact hxacc
  have hph1 : Held R L1 p (8 * (xl.toNat + xl.toNat)) := hph.sub (Nat.le_refl _) (by omega)
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [p, 8 * (xl.toNat + xl.toNat)] := hsv.2.2.1 _ _ (by omega)
  have hp64 : p < 2 ^ 64 := by omega
  have e2 : (BitVec.ofNat 64 (2 * xl.toNat)).toNat = xl.toNat + xl.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  janus_run [e2] until [0x1bb560] calls [hBM]
  rename_i hpc2 hsp2 h282 h292 h182 L2 b2 hext hbb hval hinv2 hF2 hLF2
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hpc2 hsp2 h282 h292 h182
  have e176 : (s.sp - 176#64).toNat = s.sp.toNat - 176 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  simp only [winA, e176] at hF2
  have hrd : ∀ a, s.sp.toNat - 184 ≤ a → a + 8 ≤ s.sp.toNat - 168 ∨ s.sp.toNat - 104 ≤ a → a + 8 ≤ s.sp.toNat →
      s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2 h3
    refine hF2.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
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
  janus_run [q64, q80] until [hnormM]
  have hxv := hJ.xv (by omega)
  have hval' : natVal s'.mem p (2 * xl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [show 2 * xl.toNat = xl.toNat + xl.toNat by omega, hval]; show natVal M _ _ * natVal M _ _ = _; rw [hxv]
  have hstkS : StkOK S.mem R L1 st.toNat := stkOK_frame hJ.stk hF (by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
    exact winA_of_win hstw)
  have hpst := hJ.pst (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hpst
  have hsbk := stackBack_keepC hstkS (ws := [(s.sp.toNat - 176 - 4224, s.sp.toNat - 176 - 8),
          (s.sp.toNat - 176 + 8, s.sp.toNat - 176 + 72)] ++ [(p, p + 8 * (xl.toNat + xl.toNat))])
        (by rw [← List.append_assoc]; exact hF2)
        (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by simp only [outside_append] at h; exact h.2)
        (by simp only [outside_append, outside_cons, outside_nil, and_true]; omega) hext
  refine normM impl s s'.mem p c (2 * xl.toNat) (natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat) _
    (fun s3 n' hF3 q0 q1 q2 hn' hv' hnn => post_of hJ hF hval' hext (k := 0) (Or.inr ⟨by omega, hsbk.2⟩)
      (by unfold sqrCQ; rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; omega) hinv2
      hsbk.1
      (hF2.mono fun a n h => by
        simp only [stkWs, winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        have hk := Nat.le_trans (show 176 + 4224 ≤ 4880 by decide) hW
        exact ⟨⟨h.1.1, (winA_in (c := 176) (k := 4224) (ab := 72) hb0 hk (by decide) h.1.2.1).1, (winA_in (c := 176) (k := 4224) (ab := 72) hb0 hk (by decide) h.1.2.1).2⟩,
          by have := h.2.1; first | exact this | (rwa [Nat.two_mul] at this)⟩)
      (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      (hF3.mono fun a n h => by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
      q0 q1 q2 hn' (by rw [hv', hval']) hnn)
    hcap (by omega) (by omega) (by rw [hacc2]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qlr qfp q88 hal0 (by omega) (by omega) hsacc
    hl4 hl48 (2 * xl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hval'
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bm (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc) (hx2 : 2 ≤ xl.toNat) (hsm : xl.toNat < 12)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  obtain ⟨h12, h80, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r1, r2, r3, r4, r5, r6, hsp, h28, h29, h18, mlr, mfp, m64, m80, m88, hreg, hpx⟩ := hA
  have hxl12 : xl.toNat < 2 ^ 13 := by omega
  janus_run [h12, h80, toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 12) (by decide),
    toInt_small (BitVec.ofNat 64 80) (by decide)] until [0x1bb55c]
  refine bm2 impl hap R hmc hJ hpx hx2 hsm _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [winA]; janus_frame)
    hreg m64 m80 m88 mlr mfp hl4 hl48
  all_goals janus_simp

end FvModexp.Arm64.Q.NatSqr
