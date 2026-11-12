import FvModexp.Proofs.Arm64.Nat.MulLoopLM
import FvModexp.Proofs.Arm64.Nat.MulKar

/-!
# `nat.mul` (arm64), chunk loop: the chunk product `t = t.mul(stk, x[i:i+cc], y)` (natmul.go:57)

`lcall2`: at the `CALL` `0x1bb260` (arguments loaded), the SCC induction hypothesis of member `.mul` (`μ_chunk`), the
return `0x1bb264` and `lm_of` ⟹ the continuation gets `LM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (StkPre)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- the call of the chunk product at `0x1bb260` and its return -/
theorem lcall2 (impl : List Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tc cc : Nat}
    (hμ : μl xl yl + 3 ≤ n0) (S : State)
    (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp (stLen M st) yl k) S.mem)
    (ht : TOK R L1 Lk M S.mem st tp tc) (hpx : Apart p (8 * c) xp (8 * xl)) (hpy : Apart p (8 * c) yp (8 * yl))
    (hilt : (k + 1) * yl < xl) (hcc : cc = min yl (xl - (k + 1) * yl))
    (hv : natVal S.mem p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl)
    (m128 : S.mem.readLE (s.sp.toNat - 128) 8 = (k + 1) * yl)
    (m136 : S.mem.readLE (s.sp.toNat - 120) 8 = (k + 1) * yl + yl)
    (hpc : S.pc = BitVec.ofNat 64 0x1bb260) (hsp : S.sp = s.sp - 256#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 264#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = BitVec.ofNat 64 tp) (r2 : S.regs 2 = BitVec.ofNat 64 tc) (r3 : S.regs 3 = BitVec.ofNat 64 st)
    (r4 : S.regs 4 = BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl))) (r5 : S.regs 5 = BitVec.ofNat 64 cc)
    (r6 : S.regs 6 = BitVec.ofNat 64 (xc - (k + 1) * yl)) (r7 : S.regs 7 = BitVec.ofNat 64 yp)
    (r8 : S.regs 8 = BitVec.ofNat 64 yl) (r9 : S.regs 9 = BitVec.ofNat 64 yc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' tp' tl' tc' : Nat) (S' : State),
      LM R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' k tp' tl' tc' S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  obtain ⟨hW, hWs, hal, -, -, -, -, hcap, -, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have h40 := h.h40
  have hsp' : S.sp.toNat = s.sp.toNat - 256 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcy : cc ≤ yl := by rw [hcc]; exact Nat.min_le_left _ _
  have hc0 : 0 < cc := by rw [hcc]; omega
  have hcx : (k + 1) * yl + cc ≤ xl := by
    have : cc ≤ xl - (k + 1) * yl := by rw [hcc]; exact Nat.min_le_right _ _
    omega
  have ht0 := ht.1
  have ht40 := ht.2.1
  have hst48 : st < 2 ^ 64 := by
    have := Memory.readLE_lt S.mem (s.sp.toNat - 72) 8; rw [h.s184] at this; omega
  have hxp48 : xp + 8 * xc ≤ 2 ^ 48 := (h.core.pre.2.2.2.2.2.1.1.2.2.2.2.1 (by omega)).2
  have hyp48 : yp + 8 * yc ≤ 2 ^ 48 := (h.core.pre.2.2.2.2.2.1.2.1.2.2.2.2.1 (by omega)).2
  have htp48 : tp + 8 * tc ≤ 2 ^ 48 := (ht.2.2.1 ht0).2.2.2
  have e0 : (BitVec.ofNat 64 tp).toNat = tp := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 tc).toNat = tc := by simp only [BitVec.toNat_ofNat]; omega
  have e3 : (BitVec.ofNat 64 st).toNat = st := by simp only [BitVec.toNat_ofNat]; omega
  have e4 : (BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl))).toNat = xp + 8 * ((k + 1) * yl) := by
    simp only [BitVec.toNat_ofNat]; omega
  have e5 : (BitVec.ofNat 64 cc).toNat = cc := by simp only [BitVec.toNat_ofNat]; omega
  have e6 : (BitVec.ofNat 64 (xc - (k + 1) * yl)).toNat = xc - (k + 1) * yl := by simp only [BitVec.toNat_ofNat]; omega
  have e7 : (BitVec.ofNat 64 yp).toNat = yp := by simp only [BitVec.toNat_ofNat]; omega
  have e8 : (BitVec.ofNat 64 yl).toNat = yl := by simp only [BitVec.toNat_ofNat]; omega
  have e9 : (BitVec.ofNat 64 yc).toNat = yc := by simp only [BitVec.toNat_ofNat]; omega
  have eL := (h.hdrM).2.1
  have hbk := h.bud
  rw [eL] at hbk
  have hlsp := lsp_call (ℓ := stLen s.mem st) h40 hilt h.core.pre.2.2.2.2.2.2.2.1 h.core.bud hbk
  have hsl := h.slen
  have hcost : mulC (stLen S.mem st) cc yl ≤ bk := by
    rw [hsl, eL]; exact Nat.le_trans (mulC_le_chunk hcy) hlsp
  have hyx : yl < xl := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left yl (by omega)) hilt
  have hμc : μl cc yl + 3 < n0 := Nat.lt_of_lt_of_le (μ_chunk hcy hyx) hμ
  have hBS : Summary (LibMul.program.link impl) 0x1bae70 _ _ := Summary.mono
    (ih ⟨bk, Lk, W - 256, BitVec.ofNat 64 tp, S.regs 1, BitVec.ofNat 64 tc, BitVec.ofNat 64 st,
      BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl)), BitVec.ofNat 64 cc, BitVec.ofNat 64 (xc - (k + 1) * yl),
      BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc⟩)
    (pre' := fun s1 => (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48 ∧
      s1.regs 0 = BitVec.ofNat 64 tp ∧ s1.regs 1 = S.regs 1 ∧ s1.regs 2 = BitVec.ofNat 64 tc ∧
      s1.regs 3 = BitVec.ofNat 64 st ∧ s1.regs 4 = BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl)) ∧
      s1.regs 5 = BitVec.ofNat 64 cc ∧ s1.regs 6 = BitVec.ofNat 64 (xc - (k + 1) * yl) ∧
      s1.regs 7 = BitVec.ofNat 64 yp ∧ s1.regs 8 = BitVec.ofNat 64 yl ∧ s1.regs 9 = BitVec.ofNat 64 yc ∧
      s1.sp = S.sp ∧ s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (post' := fun s1 s2 => Kept s1 s2 ∧
      IntAS.Box (∃ S1 : State, S1.mem = S.mem ∧ S1.sp = S.sp ∧ S1.regs 28 = S.regs 28 ∧
        MPost R bk Lk (W - 256) tp tc st (xp + 8 * ((k + 1) * yl)) cc (xc - (k + 1) * yl) yp yl yc S1 s2))
    (fun s1 ⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hs, hg, hm⟩ => by
      refine ⟨⟨⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, ?_⟩, ?_⟩
      · show MPre R bk Lk (W - 256) (BitVec.ofNat 64 tp).toNat (BitVec.ofNat 64 tc).toNat
          (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl))).toNat (BitVec.ofNat 64 cc).toNat
          (BitVec.ofNat 64 (xc - (k + 1) * yl)).toNat (BitVec.ofNat 64 yp).toNat (BitVec.ofNat 64 yl).toNat
          (BitVec.ofNat 64 yc).toNat s1
        rw [e0, e2, e3, e4, e5, e6, e7, e8, e9]
        exact h.mpreT ht (S1 := s1) (by rw [hs]; exact hsp') (by rw [hg, h28]) hm
          (i := (k + 1) * yl) (cc := cc) (Nat.le_mul_of_pos_left yl (by omega)) hc0 hcy hcx hcost
      · show μl (BitVec.ofNat 64 cc).toNat (BitVec.ofNat 64 yl).toNat + 3 < n0
        rw [e5, e8]; exact hμc)
    (fun s1 s2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, hg, hm⟩ ⟨hk, hq⟩ => by
      refine ⟨hk, ⟨⟨s1, hm, hs, hg, ?_⟩⟩⟩
      have := hq; rw [e0, e2, e3, e4, e5, e6, e7, e8, e9] at this; exact this)
  janus_run until [0x1bb264] calls [hBS]
  rename_i hpc2 hk1 hk2 hk3 hk4 hbox
  obtain ⟨⟨S1, hm1, hs1, hg1, hq⟩⟩ := hbox
  have q1 : s'.pc = BitVec.ofNat 64 0x1bb264 := by rw [hpc2]; janus_simp
  have q2 : s'.sp = s.sp - 256#64 := by rw [hk1]
  have q3 : s'.regs 28 = s.regs 28 := by rw [hk2]; simp only [setReg_apply]; exact h28
  have q4 : s'.regs 29 = s.sp - 264#64 := by rw [hk3]; simp only [setReg_apply]; exact h29
  have q5 : s'.regs 18 = s.regs 18 := by rw [hk4]; simp only [setReg_apply]; exact h18
  have hs1' : S1.sp.toNat = s.sp.toNat - 256 := by rw [hs1, ← hsp]; exact hsp'
  obtain ⟨Lk', bk', tp', tl', tc', hlm⟩ := lm_of h ht hpx hpy hilt hv m128 m136 hcc hs1' (by rw [hg1]) hm1 hq hrg1
    q1 q2 q3 q4 q5
  exact hK _ _ _ _ _ _ hlm

end FvModexp.Arm64.NatMul
