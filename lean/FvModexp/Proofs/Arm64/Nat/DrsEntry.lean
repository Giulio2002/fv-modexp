import FvModexp.Proofs.Arm64.Nat.DrsFin

/-!
# `divRecursiveStep` (arm64): entry → after `u = u.norm(); v = v.norm()` (composition, no execution of its own)

`entry`: `pro0` → `norm1` (`u.norm()`) → `pro1` → `norm2` (`v.norm()`, which keeps `n = len v` since the top word is
`≥ 2^63`: `norm_v`) → `AtE2` with the normalised `len u = ul' ≤ ul` (`U` unchanged, `NatNorm`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW)

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → `AtE2` -/
theorem entry (impl : List Segment) (R : RtInv) (a : Args) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1ba3a0)
    (hE : Entry a s) {c : Nat} (hpre : DrsPreW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat
      a.ul.toNat a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat s) (hW : 30608 ≤ a.W) (Q : State → Prop)
    (k : ∀ (P : State) (ul' : Nat), AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat
      a.vp.toNat a.vl.toNat a.vc.toNat a.d.toNat → ul' ≤ a.ul.toNat →
      natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat → NatNorm s.mem a.up.toNat ul' →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) s Q := by
  obtain ⟨hce, -, hgl, -, -, hul, huc, hvlc, hvc, hv2, -, htop, -, -, -, ⟨hua, hu48, -, huo, -⟩,
    ⟨hva, hv48, -, hvo, -⟩, -, -, -, ⟨⟨-, -, hsta, hst48, -⟩, hsto, -⟩, -⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hce'
  obtain ⟨-, -, -, h40, -, -, -, hgacc, -, hgw, -⟩ := hgl
  replace h40 : s.mem.readLE 7147136 8 = 40 := h40
  replace hgacc : s.mem.accessible 7147136 32 false = true := hgacc
  replace hgw : Outside 7147136 32 (win s a.W 96) := hgw
  obtain ⟨h30a, h30b, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
  simp only [win, outside_cons, outside_nil, and_true] at huo hvo hsto hgw
  refine pro0 impl s a.W hpc hce (by omega) Q fun P hpc0 hF hR hs1 hs2 hs3 hd hb => ?_
  have hPm : MemFrame s.mem P.mem (fw s) := hF.fr
  have hrd : ∀ p n, p + n ≤ s.sp.toNat - a.W ∨ s.sp.toNat + 96 ≤ p → P.mem.readLE p n = s.mem.readLE p n :=
    fun p n h => hPm.readLE p n (fw_out (W := a.W) (by omega) (by simp only [win, outside_cons, outside_nil, and_true]; omega))
  have hacc : ∀ p n w, P.mem.accessible p n w = s.mem.accessible p n w := fun p n w => hPm.accessible p n w
  have hU : ∀ n, n ≤ a.ul.toNat → natVal P.mem a.up.toNat n = natVal s.mem a.up.toNat n := fun n hn => by
    unfold natVal; exact hrd _ _ (by omega)
  have hV : ∀ n, n ≤ a.vl.toNat → natVal P.mem a.vp.toNat n = natVal s.mem a.vp.toNat n := fun n hn => by
    unfold natVal; exact hrd _ _ (by omega)
  refine norm1 impl (s.regs 30) P.mem a.up.toNat a.ul.toNat (natVal P.mem a.up.toNat a.ul.toNat) P Q ?_ (by omega)
    hu48 (by rw [hacc]; exact Memory.accessible_read_of_write _ hua)
    (by rw [hR 4 (by omega), e4, bv_ofNat_toNat]) a.ul.toNat P (Nat.le_refl _) hpc0 (by rw [hR 5 (by omega), e5, bv_ofNat_toNat])
    rfl (fun _ _ _ _ => rfl) rfl rfl
  intro s1 ul' hpc1 hm1 h51 hsp1 hS1 hle1 hv1 hN1
  refine pro1 impl (s.regs 30) s1 ul' a.uc.toNat hpc1 h51
    (by rw [hS1 6 (by decide) (by decide) (by decide), hR 6 (by omega), e6, bv_ofNat_toNat]) (by omega) huc Q ?_
  intro P2 hpc2 hm2 hsp2 hR2
  refine norm2 impl (s.regs 30) P.mem a.vp.toNat a.vl.toNat (natVal P.mem a.vp.toNat a.vl.toNat) P2 Q ?_ (by omega)
    hv48 (by rw [hacc]; exact hva)
    (by rw [hR2 7 (by decide) (by decide), hS1 7 (by decide) (by decide) (by decide), hR 7 (by omega), e7, bv_ofNat_toNat])
    a.vl.toNat P2 (Nat.le_refl _) hpc2
    (by rw [hR2 8 (by decide) (by decide), hS1 8 (by decide) (by decide) (by decide), hR 8 (by omega), e8, bv_ofNat_toNat])
    rfl (fun _ _ _ _ => rfl) (by rw [hm2, hm1]) rfl
  intro s2 vl' hpc3 hm3 h83 hsp3 hS3 hle3 hv3 hN3
  have hvl' : vl' = a.vl.toNat := by
    refine norm_v (M := P.mem) (by omega) ?_ hle3 hv3
    rw [hrd _ _ (by omega)]; exact htop
  subst hvl'
  have hm : s2.mem = P.mem := hm3
  have hreg : ∀ j, j ≤ 10 → j ≠ 5 → j ≠ 8 → s2.regs j = s.regs j := fun j hj h5 h8 => by
    rw [hS3 j h8 (by omega) (by omega), hR2 j (by omega) (by omega), hS1 j h5 (by omega) (by omega), hR j hj]
  have hsp : s2.sp = P.sp := by rw [hsp3, hsp2, hsp1]
  have hFr : Fr s s2 := by
    refine ⟨by rw [hsp]; exact hF.sp, ?_, ?_, ?_, by rw [hm]; exact hF.reg, by rw [hm]; exact hF.fr,
      by rw [hm]; exact hF.lr, by rw [hm]; exact hF.fp⟩
    · rw [hS3 28 (by decide) (by decide) (by decide), hR2 28 (by decide) (by decide),
        hS1 28 (by decide) (by decide) (by decide)]; exact hF.r28
    · rw [hS3 29 (by decide) (by decide) (by decide), hR2 29 (by decide) (by decide),
        hS1 29 (by decide) (by decide) (by decide)]; exact hF.r29
    · rw [hS3 18 (by decide) (by decide) (by decide), hR2 18 (by decide) (by decide),
        hS1 18 (by decide) (by decide) (by decide)]; exact hF.r18
  have hspn : s2.sp.toNat = s.sp.toNat - 400 := by
    rw [hFr.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  refine k s2 ul' ⟨hpc3, hFr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvlc, hvc, by omega, ?_, ?_, hspn,
    by omega, by omega, ?_, ?_, hst48, hal, ?_, by omega⟩ hle1 ?_ ?_
  · rw [hreg 0 (by omega) (by omega) (by omega), e0, bv_ofNat_toNat]
  · rw [hreg 1 (by omega) (by omega) (by omega), e1, bv_ofNat_toNat]
  · rw [hreg 2 (by omega) (by omega) (by omega), e2, bv_ofNat_toNat]
  · rw [hreg 3 (by omega) (by omega) (by omega), e3, bv_ofNat_toNat]
  · rw [hreg 4 (by omega) (by omega) (by omega), e4, bv_ofNat_toNat]
  · rw [hS3 5 (by decide) (by decide) (by decide), hR2 5 (by decide) (by decide)]; exact h51
  · rw [hreg 6 (by omega) (by omega) (by omega), e6, bv_ofNat_toNat]
  · rw [hreg 7 (by omega) (by omega) (by omega), e7, bv_ofNat_toNat]
  · exact h83
  · rw [hreg 9 (by omega) (by omega) (by omega), e9, bv_ofNat_toNat]
  · rw [hreg 10 (by omega) (by omega) (by omega), e10, bv_ofNat_toNat]
  · rw [hm, hrd _ _ (by omega)]; exact h40
  · rw [hm, hacc]; exact Memory.accessible_mono _ hgacc (by omega) (by omega)
  · rw [hm, hacc]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [hm, hacc]; exact Memory.accessible_read_of_write _ hsta
  · rw [hm, hrd _ _ (by omega)]
  · rw [← hU ul' hle1, hv1, hU _ (Nat.le_refl _)]
  · rcases Nat.eq_zero_or_pos ul' with h0 | h0
    · exact Or.inl h0
    · rcases hN1 with h | h
      · exact Or.inl h
      · right; rw [← hrd _ _ (by omega)]; exact h

end FvModexp.Arm64.DivRec

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`len u < n`**: nothing to do (`fn + 0x11c`) -/
theorem pathC (impl : List Segment) (R : RtInv) (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp.toNat a.vl.toNat a.vc.toNat s) (hW : 30608 ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat
      a.d.toNat)
    (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat) (h0 : 0 < ul') (h40 : 40 ≤ a.vl.toNat)
    (hlt : ul' < a.vl.toNat) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp.toNat a.vl.toNat s s') := by
  have hpre' := hpre
  obtain ⟨hce, -, -, -, -, -, -, -, -, hv2, -, htop, hq0, -, -, -, ⟨hva, -⟩, -⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -⟩ := hce
  have hlt' := u_lt_v (by omega) htop hlt hU
  refine pro2c impl (s.regs 30) hA h0 h40 hlt _ fun T hpc hm hsp h28 h29 h18 => ?_
  have hFT : Fr s T := by
    have hF := hA.fr
    exact ⟨by rw [hsp]; exact hF.sp, by rw [h28]; exact hF.r28, by rw [h29]; exact hF.r29, by rw [h18]; exact hF.r18,
      by rw [hm]; exact hF.reg, by rw [hm]; exact hF.fr, by rw [hm]; exact hF.lr, by rw [hm]; exact hF.fp⟩
  refine epiC impl s T hpc hFT.sp hFT.r28 hFT.r18 hFT.lr hFT.fp (by omega) (by omega) hal ?_ hE.1 hE.2.1 _ fun s' ⟨e1, e2, e3, e4, e5⟩ => ⟨⟨e1, e2, e3, e4⟩, ?_⟩
  · rw [hFT.fr.accessible]; exact Memory.accessible_mono _ (Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  · refine post_frame hpre (by omega) (by rw [e5]; exact hFT.fr) ?_ ?_
    · rw [hq0, Nat.div_eq_of_lt hlt']
    · rw [Nat.mod_eq_of_lt hlt']

end FvModexp.Arm64.DivRec

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`len u == 0`**: `clear(z)` (`memclrNoHeapPointers(z, 8·len z)` when `len z > 0`) and return -/
theorem pathA (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp.toNat a.vl.toNat a.vc.toNat s) (hW : 30608 ≤ a.W) (P : State)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat 0 a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat
      a.d.toNat)
    (hU : natVal s.mem a.up.toNat 0 = natVal s.mem a.up.toNat a.ul.toNat) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp.toNat a.vl.toNat s s') := by
  have hpre' := hpre
  obtain ⟨hce, hsv, -, hqlc, hqc, -, -, -, -, hv2, ⟨-, hql9⟩, htop, hq0, -, ⟨hqa, hq48, hqh, hqo, hqg⟩, -, -, -, -, -,
    hsti, -, ⟨hqs, -⟩, -, -, -, -, -, -, -, hinv⟩ := hpre'
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce'
  have hU0 : natVal s.mem a.up.toNat a.ul.toNat = 0 := by rw [← hU]; rfl
  have hqo' := hqo
  simp only [win, outside_cons, outside_nil, and_true] at hqo'
  unfold Apart at hga
  have hpost : ∀ M : Memory, natVal M a.qp.toNat a.ql.toNat = 0 → natVal M a.up.toNat a.ul.toNat = 0 →
      natVal M a.qp.toNat a.ql.toNat = natVal s.mem a.up.toNat a.ul.toNat / natVal s.mem a.vp.toNat a.vl.toNat ∧
      natVal M a.up.toNat a.ul.toNat = natVal s.mem a.up.toNat a.ul.toNat % natVal s.mem a.vp.toNat a.vl.toNat := by
    intro M h1 h2; rw [h1, h2, hU0]; simp
  refine pro2a impl (s.regs 30) hA rfl _ fun T0 hpc0 hm0 hsp0 h0 h1 h28 h29 h18 => ?_
  have hF := hA.fr
  have hspT : T0.sp = s.sp - 400#64 := by rw [hsp0]; exact hF.sp
  have h28' : T0.regs 28 = s.regs 28 := by rw [h28]; exact hF.r28
  have h29' : T0.regs 29 = s.sp - 408#64 := by rw [h29]; exact hF.r29
  have h18' : T0.regs 18 = s.regs 18 := by rw [h18]; exact hF.r18
  have hFT0 : Fr s T0 := ⟨hspT, h28', h29', h18', by rw [hm0]; exact hF.reg, by rw [hm0]; exact hF.fr,
      by rw [hm0]; exact hF.lr, by rw [hm0]; exact hF.fp⟩
  have hacc8 : T0.mem.accessible (s.sp.toNat - 408) 16 false = true := by
    rw [hFT0.fr.accessible]; exact Memory.accessible_mono _ (Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  rcases Nat.eq_zero_or_pos a.ql.toNat with hz | hz
  · -- `len z == 0`: nothing to clear
    rw [hz] at h1
    janus_run until [0x1ba4e4]
    refine epiZ impl s _ rfl ?esp ?e28 ?e18 ?elr ?efp (by omega) (by omega) hal ?eacc hE.1 hE.2.1 _
      fun s' ⟨e1, e2, e3, e4, e5⟩ => ⟨⟨e1, e2, e3, e4⟩, ?epost⟩
    case esp => exact hF.sp
    case e28 => exact h28'
    case e18 => exact h18'
    case elr => exact hF.lr
    case efp => exact hF.fp
    case eacc => exact hm0 ▸ hacc8
    case epost =>
      refine post_frame hpre (by omega) (by rw [e5]; exact hF.fr) ?_ ?_
      · rw [hq0, hU0]; simp
      · rw [hU0]; simp
  · -- `clear(z)`
    have hl3 := lsl3_ofNat a.ql.toNat (by omega)
    have hne : (BitVec.ofNat 64 a.ql.toNat = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    janus_run [hl3, hne] until [cA "runtime.memclrNoHeapPointers"]
    refine ReachesRet.call_regions (hmc a.L a.b) rfl (mc_pre (dst := a.qp.toNat) (n := 8 * a.ql.toNat) hce (by omega)
      (LiveExt.refl R a.L) _ ?msp ?q28 ?qg ?qa ?l1 ?l2 ?qi ?q0 ?q1 (hsv.2.2.1 _ _ (by omega)) (by omega) ?dacc ?dh ?dw) ?qk
    case msp => exact hF.sp
    case q28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28']
    case qg => exact hF.fr.readLE _ _ (by simp only [fw, winA, outside_cons, outside_nil, and_true]; omega)
    case qa => intro a' n w; exact hF.fr.accessible a' n w
    case l1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    case l2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    case qi =>
      refine RtInv.inv_frame' hF.fr (fun r hr => ?_) hinv
      simp only [fw, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by simp only; omega) (by simp only; omega))
    case q0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h0, BitVec.toNat_ofNat]; omega
    case q1 =>
      simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
      have e := hl3; rw [bv_ofNat_toNat] at e; rw [e, BitVec.toNat_ofNat]; omega
    case dacc => rw [hF.fr.accessible]; exact hqa
    case dh => exact hqh
    case dw => omega
    case qk =>
      intro T hT ⟨junk, f, v, m, ex, ep, hs, hMF, hLF, hinv', hzr⟩ hrg
      subst hs
      have e400 : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
      have e3 := hl3; rw [bv_ofNat_toNat] at e3
      simp only [calleeStack, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, hF.sp, e400, h28', h0,
        bv_ofNat_toNat, e3] at hMF hLF hzr hinv'
      rw [Nat.mod_eq_of_lt (show 8 * a.ql.toNat < 2 ^ 64 by omega)] at hMF hLF hzr
      refine epiZ impl s _ ?zpc ?zsp ?z28 ?z18 ?zlr ?zfp (by omega) (by omega) hal ?zacc hE.1 hE.2.1 _
        fun s' ⟨e1, e2, e3, e4, e5⟩ => ⟨⟨e1, e2, e3, e4⟩, ?zpost⟩
      case zpc => rw [hT]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
      case zsp => exact hF.sp
      case z28 =>
        simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28', true_or, or_true, ite_true]
      case z18 =>
        simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18', true_or, or_true, ite_true]
      case zlr =>
        simp only [retStateX]
        rw [hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩)]; exact hF.lr
      case zfp =>
        simp only [retStateX]
        rw [hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩)]; exact hF.fp
      case zacc => simp only [retStateX]; rw [hMF.accessible]; exact hm0 ▸ hacc8
      case zpost =>
        have e5' : s'.mem = m := by rw [e5]; rfl
        rw [← e5'] at hMF hLF hinv' hzr
        refine post_clr hpre (by omega) hF.fr hMF hLF ?_ hinv' ?_ ?_
        · intro a' n ho; simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; omega
        · have : natVal s'.mem a.qp.toNat a.ql.toNat = 0 := FvModexp.Expmc.readLE_zeroed hzr
          rw [this, hU0]; simp
        · rw [hU0]; simp

end FvModexp.Arm64.DivRec
