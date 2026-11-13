import FvModexp.Proofs.Arm64.NatQ.MulCall
import FvModexp.Proofs.Arm64.NatQ.MulBMP
import FvModexp.Proofs.Arm64.NatQ.MulNorm
import FvModexp.Proofs.Arm64.Nat.DivmcCall
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.WinLemmas

/-!
# [Q-form copy of Arm64/Nat/MulBM.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), `2 ≤ n < 40`: `basicMul(z, x, y); return z.norm()` (natmul.go:38-41)

`bm`: the join (`0x1baf70`) → `CALL basicMul` (`0x1bb0e0`, threshold loaded); `bm2`: the call (`BasicMul.ens`, its
`CallEnv` from `Core.callee`), then `normA` and `post_of`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (stackBack_keep' stackBack_keepC stkOK_frame)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem bm2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb0e0) (hsp : S.sp = s.sp - 256#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 264#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = BitVec.ofNat 64 p) (r1 : S.regs 1 = BitVec.ofNat 64 (xl.toNat + yl.toNat))
    (r2 : S.regs 2 = BitVec.ofNat 64 c) (r3 : S.regs 3 = xp) (r4 : S.regs 4 = xl) (_r5 : S.regs 5 = xc)
    (r6 : S.regs 6 = yp) (r7 : S.regs 7 = yl) (_r8 : S.regs 8 = yc)
    (hF : MemFrame M S.mem (winA s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (m144 : S.mem.readLE (s.sp.toNat - 112) 8 = p) (m120 : S.mem.readLE (s.sp.toNat - 136) 8 = xl.toNat + yl.toNat)
    (m96 : S.mem.readLE (s.sp.toNat - 160) 8 = c)
    (mlr : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments BasicMul.names).link impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hBM := Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b1 L1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (noExit_restrict hap BasicMul.names) hc
  clear hc
  rw [show segAddr Extracted.program BasicMul.fn = 0x1bbd00 by decide] at hBM
  obtain ⟨hce, hmw, -⟩ := hJ.pre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩ := hce
  have hsp' : S.sp.toNat = s.sp.toNat - 256 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have tp : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 (xl.toNat + yl.toNat)).toNat = xl.toNat + yl.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  have e256 : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus_run [e2] until [0x1bbd00]
  refine ReachesRet.call_regions hBM rfl ⟨mul_ra157 hap, ?_⟩ fun s' hpc2 hq hrg => ?_
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r0, r1, r2, r3, r4, r6, r7]
    exact bm_pre hJ hpx hpy hy2 hyx e256 h28 hF hreg
  obtain ⟨⟨hsp2, h282, h292, h182⟩, hval, L2, b2, hext, hbb, hinv2, hF2, hLF2⟩ := hq
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r0, r3, r4, r6, r7, tp] at hval hF2 hLF2 hinv2
  rw [h28] at hinv2
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hpc2 hsp2 h282 h292 h182
  clear hpx hpy
  simp only [winA, e256] at hF2
  have hrd : ∀ a, s.sp.toNat - 264 ≤ a → a + 8 ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 184 ≤ a → a + 8 ≤ s.sp.toNat →
      s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2 h3
    refine hF2.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
  have q144 := (hrd _ (by omega) (Or.inr (by omega)) (by omega)).trans m144
  have q120 := (hrd _ (by omega) (Or.inr (by omega)) (by omega)).trans m120
  have q96 := (hrd _ (by omega) (Or.inr (by omega)) (by omega)).trans m96
  have qlr := (hrd _ (by omega) (Or.inl (by omega)) (by omega)).trans mlr
  have qfp := (hrd _ (by omega) (Or.inl (by omega)) (by omega)).trans mfp
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF.accessible]
  have hsacc : s'.mem.accessible (s.sp.toNat - 264) 264 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsacc' : s'.mem.accessible (s.sp.toNat - 264) 264 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  janus_run [q144, q120] until [hnormA]
  have hval' : natVal s'.mem p (xl.toNat + yl.toNat) =
      natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat := by
    obtain ⟨-, -, -, -, -, ⟨⟨-, -, -, -, -, hxw⟩, ⟨-, -, -, -, -, hyw⟩, -⟩, -⟩ := hJ.pre
    rw [hval, natVal_frame hF (winA_of_win' (hxw (by omega)).1), natVal_frame hF (winA_of_win' (hyw (by omega)).1),
      hJ.xv (by omega), hJ.yv (by omega)]
  have hstkS : StkOK S.mem R L1 st.toNat := stkOK_frame hJ.stk hF (by
    obtain ⟨-, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
    exact winA_of_win' hstw)
  have hpst := hJ.pst (by omega)
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hpst
  have hsbk := stackBack_keepC hstkS (ws := [(s.sp.toNat - 256 - 4224, s.sp.toNat - 256 - 8),
          (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 72)] ++ [(p, p + 8 * (xl.toNat + yl.toNat))])
        (by rw [← List.append_assoc]; exact hF2)
        (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by simp only [outside_append] at h; exact h.2)
        (by simp only [outside_append, outside_cons, outside_nil, and_true]; omega) hext
  refine normA impl s s'.mem p c (xl.toNat + yl.toNat) (natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat)
    _ (fun s3 n' hF3 q0 q1 q2 hn' hv' hnn => post_of hJ hF hval' hext (k := 0) (Or.inr ⟨by omega, hsbk.2⟩)
      (by unfold mulCQ; rw [Nat.max_eq_left hyx, Nat.min_eq_right hyx]; have := MCQ_basic (m := xl.toNat) hy2; omega)
      hinv2 hsbk.1
      (hF2.mono fun a n h => by
        simp only [stkWs, winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        have hk := Nat.le_trans (show 256 + 4224 ≤ 4608 by decide) hW
        exact ⟨⟨h.1.1, (winA_in (c := 256) (k := 4224) (ab := 72) hb0 hk (by decide) h.1.2.1).1, (winA_in (c := 256) (k := 4224) (ab := 72) hb0 hk (by decide) h.1.2.1).2⟩,
          by have := h.2.1; first | exact this | (rwa [Nat.two_mul] at this)⟩)
      (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      (hF3.mono fun a n h => by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
      q0 q1 q2 hn' (by rw [hv', hval']) hnn)
    hcap (by omega) (by omega) (by rw [hacc2]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qlr qfp q96 hal0 (by omega) (by omega) hsacc
    hl4 hl48 (xl.toNat + yl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hval'
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bm (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hsm : yl.toNat < 40) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  obtain ⟨h40, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, hsp, h28, h29, h18, mlr, mfp, m120, -, -, -, -, -, -, hreg,
    hpx, hpy, -, -⟩ := hA
  have hyl : yl.toNat < 2 ^ 13 := by omega
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -⟩, hmw, -⟩ := hpre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hsacc : S.mem.accessible (s.sp.toNat - 264) 264 true = true := by
    rw [hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := hJ.live (by omega); omega
  janus_run [h40, toInt_small yl (by omega), toInt_small (BitVec.ofNat 64 40) (by decide)] until [0x1bb0e0]
  refine bm2 impl hap R hmc hJ hpx hpy hy2 hyx _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [winA]; janus_frame) ?qreg ?q144 ?q120 ?q96 ?qlr ?qfp hl4 hl48
  case qreg => janus_simp; exact hreg
  case q144 => janus_simp
  case q120 => janus_simp; exact m120
  case q96 => janus_simp
  case qlr => janus_simp; exact mlr
  case qfp => janus_simp; exact mfp
  all_goals janus_simp

end FvModexp.Arm64.Q.NatMul
