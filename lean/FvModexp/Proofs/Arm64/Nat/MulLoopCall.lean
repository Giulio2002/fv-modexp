import FvModexp.Proofs.Arm64.Nat.MulLoopLM
import FvModexp.Proofs.Arm64.Nat.MulKar
import FvModexp.Proofs.Common.BitArith

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

theorem toIntN {a : Nat} (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- the slice mask `i & ((i - c) >> 63)` for `i < c` -/
theorem maskN {i c : Nat} (h : i < c) (hc : c < 2 ^ 63) :
    (BitVec.ofNat 64 i &&& (BitVec.ofNat 64 i - BitVec.ofNat 64 c).sshiftRight 63) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have := BitArith.and_asr63 (BitVec.ofNat 64 i) (BitVec.ofNat 64 c) (by simp only [BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_ofNat]; omega)
  rw [this]; simp only [BitVec.toNat_ofNat]
  rw [if_pos (by rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- **one chunk product**: the head (`i < m`) → the call → `LM` -/
theorem lcall (impl : List Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tl tc : Nat}
    (hμ : μl xl yl + 3 ≤ n0) (S : State)
    (hH : LH R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S) (hilt : (k + 1) * yl < xl)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' tp' tl' tc' : Nat) (S' : State),
      LM R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' k tp' tl' tc' S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have h := hH.lb
  obtain ⟨hW, hWs, hal, -, -, -, -, hcap, -, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have h40 := h.h40
  have hpc := hH.pc; have hsp := hH.sp; have h28 := hH.g; have h29 := hH.fp; have h18 := hH.x18
  have r0 := hH.r0; have r1 := hH.r1; have r2 := hH.r2; have r3 := hH.r3
  have a296 := h.a296; have a304 := h.a304; have a312 := h.a312; have a320 := h.a320; have a328 := h.a328
  have a336 := h.a336; have s184 := h.s184
  have hyx : yl < xl := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left yl (by omega)) hilt
  obtain ⟨⟨-, ⟨-, -, ha0, hw0⟩, -⟩, -⟩ := h.core.pre
  have hsacc : S.mem.accessible (s.sp.toNat - 264) 352 true = true := by
    rw [h.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have i1 := toIntN (a := (k + 1) * yl) (by omega)
  have i2 := toIntN (a := xl) (by omega)
  have hm := maskN (i := (k + 1) * yl) (c := xc) (by omega) (by omega)
  have i3 := toIntN (a := (k + 1) * yl + yl) (by omega)
  have hadd : BitVec.ofNat 64 yl + BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 ((k + 1) * yl + yl) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  by_cases hlast : xl < (k + 1) * yl + yl
  · have hI : ((xl : Nat) : Int) < (((k + 1) * yl + yl : Nat) : Int) := by omega
    janus_run [a296, a304, a312, a320, a328, a336, s184, i1, i2, i3, hadd, hm, hI] until [0x1bb260]
    refine lcall2 impl R n0 ih hμ _ (h.local ?fr0 ?reg) (hH.tok.winKeep h ?frW) hH.px hH.py hilt (cc := xl - (k + 1) * yl) ?hcc
      ?hv ?m128 ?m136 ?pc ?sp ?g ?fp ?x18 ?r0 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 hK
    case fr0 => janus_frame
    case frW => simp only [winA]; janus_frame
    case reg => janus_simp
    case hcc => omega
    case hv =>
      rw [(h.winVal hH.tok (tl := 0) (Nat.zero_le _) (by simp only [winA]; janus_frame)).1, hH.val,
        Nat.min_eq_left (by omega)]
    case m128 => janus_simp
    case m136 => janus_simp
    case r0 => janus_simp
    case r2 => janus_simp
    all_goals try janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  · have hI : ¬ (((xl : Nat) : Int) < (((k + 1) * yl + yl : Nat) : Int)) := by omega
    janus_run [a296, a304, a312, a320, a328, a336, s184, i1, i2, i3, hadd, hm, hI] until [0x1bb260]
    refine lcall2 impl R n0 ih hμ _ (h.local ?fr0B ?regB) (hH.tok.winKeep h ?frWB) hH.px hH.py hilt (cc := yl) ?hccB
      ?hvB ?m128B ?m136B ?pcB ?spB ?gB ?fpB ?x18B ?r0B ?r2B ?r3B ?r4B ?r5B ?r6B ?r7B ?r8B ?r9B hK
    case fr0B => janus_frame
    case frWB => simp only [winA]; janus_frame
    case regB => janus_simp
    case hccB => omega
    case hvB =>
      rw [(h.winVal hH.tok (tl := 0) (Nat.zero_le _) (by simp only [winA]; janus_frame)).1, hH.val,
        Nat.min_eq_left (by omega)]
    case m128B => janus_simp
    case m136B => janus_simp
    case r0B => janus_simp
    case r2B => janus_simp
    all_goals try janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.NatMul
