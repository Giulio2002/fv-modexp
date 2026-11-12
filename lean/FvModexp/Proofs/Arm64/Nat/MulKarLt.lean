import FvModexp.Proofs.Arm64.Nat.MulKar
import FvModexp.Proofs.Arm64.Nat.MulLoopClr

/-!
# `nat.mul` (arm64), `40 ≤ n < m`: `karatsuba(stk, z[:2n], x[:n], y)` (natmul.go:51) → `KA` at `0x1bb054`

`karLt2`: the call at `0x1bb038` (the SCC induction hypothesis of member `.kar`, as `MulKar.karEq2`), the return and
`BLT` (`n < m`) → `KA`. `karLt`: the join → the call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (StkPre stackBack_keep')

theorem ws_kar {R : RtInv} {s S1 : State} {W p yl xl st : Nat} {M : Memory}
    (hs1 : S1.sp.toNat = s.sp.toNat - 256) (hW : 4608 ≤ W) (hWs : W ≤ s.sp.toNat) (hyx : yl < xl) :
    ∀ a n, Outside a n (R.rt ++ winA s W 88 ++ lws M st p (xl + yl)) →
      Outside a n (R.rt ++ winA S1 (W - 256) 72 ++ (p, p + 8 * (2 * yl)) :: stkWs M st) := by
  intro a n h
  rw [outside_append, outside_append] at h
  obtain ⟨⟨hr, hw⟩, hl⟩ := h
  simp only [winA, outside_cons, outside_nil, and_true] at hw
  simp only [lws, outside_cons] at hl
  obtain ⟨w1, w2⟩ := hw
  obtain ⟨hp, hs⟩ := hl
  rw [outside_append, outside_append]
  simp only [winA, outside_cons, outside_nil, and_true]
  rw [hs1]
  simp only [outside_nil, and_true] at hs
  exact ⟨⟨hr, by omega, by omega⟩, by omega, hs⟩

theorem lf_kar {M : Memory} {st p yl xl : Nat} (hyx : yl < xl) :
    ∀ a n, Outside a n (lws M st p (xl + yl)) → Outside a n ((p, p + 8 * (2 * yl)) :: stkWs M st) := by
  intro a n h
  simp only [lws, outside_cons] at h ⊢
  obtain ⟨hp, hs⟩ := h
  exact ⟨by omega, hs⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KA` from `karatsuba`'s post** (pure; `S` the call state, `S2` the return, `S'` at `0x1bb054`) -/
theorem kaOf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp (8 * xl)) (hpy : Apart p (8 * c) yp (8 * yl)) (h40 : 40 ≤ yl) (hyx : yl < xl)
    {S S1 S2 : State} (hF : MemFrame M S.mem (winA s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (hm1 : S1.mem = S.mem) (hs1 : S1.sp.toNat = s.sp.toNat - 256) (hg1 : S1.regs 28 = s.regs 28)
    (hq : KPost R b1 L1 (W - 256) st p (2 * yl) xp yl yp yl S1 S2) (hreg2 : S2.mem.regions = S.mem.regions)
    (er1 : S2.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (er2 : S2.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (er144 : S2.mem.readLE (s.sp.toNat - 112) 8 = p) (er120 : S2.mem.readLE (s.sp.toNat - 136) 8 = xl + yl)
    (er96 : S2.mem.readLE (s.sp.toNat - 160) 8 = c) (er94 : S2.mem.readLE (s.sp.toNat - 162) 1 = 0)
    (er304 : S2.mem.readLE (s.sp.toNat + 48) 8 = xl) (er328 : S2.mem.readLE (s.sp.toNat + 72) 8 = yl)
    (er136 : S2.mem.readLE (s.sp.toNat - 120) 8 = 2 * yl) (er184 : S2.mem.readLE (s.sp.toNat - 72) 8 = st)
    (er296 : S2.mem.readLE (s.sp.toNat + 40) 8 = xp) (er312 : S2.mem.readLE (s.sp.toNat + 56) 8 = xc)
    (er320 : S2.mem.readLE (s.sp.toNat + 64) 8 = yp) (er336 : S2.mem.readLE (s.sp.toNat + 80) 8 = yc) :
    ∃ (Lk : List (Nat × Nat)) (bk : Nat), ∀ S' : State, S'.mem = S2.mem → S'.pc = BitVec.ofNat 64 0x1bb054 →
      S'.sp = s.sp - 256#64 → S'.regs 28 = s.regs 28 → S'.regs 29 = s.sp - 264#64 → S'.regs 18 = s.regs 18 →
      S'.regs 10 = BitVec.ofNat 64 yl → KA R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S' := by
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -⟩, hmw, -⟩ := hJ.pre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  obtain ⟨hval, L2, b2, hext, hbud, hinv2, hsb, hMF, hLF⟩ := hq
  rw [hm1] at hval hsb hMF hLF hbud
  rw [hg1] at hinv2
  obtain ⟨-, -, -, -, -, ⟨⟨hxlc, -, hxl12, -, hxh, hxw⟩, ⟨hylc, -, hyl12, -, hyh, hyw⟩, -⟩, -⟩ := hJ.pre
  have hLs := hJ.lsep
  have hxo : Outside xp (8 * yl) (win s W 88) := (hxw (by omega)).1.of_sub (Nat.le_refl _) (by omega)
  have hxH : Held R L xp (8 * yl) := (hxh (by omega)).1.sub (Nat.le_refl _) (by omega)
  have hxv : natVal S.mem xp yl = natVal s.mem xp yl := by
    rw [natVal_frame hF (winA_of_win' hxo)]; unfold natVal; exact hJ.rd hxH hxo
  have hyv : natVal S.mem yp yl = natVal s.mem yp yl := by
    rw [natVal_frame hF (winA_of_win' (hyw (by omega)).1), hJ.yv (by omega)]
  have hval' : natVal S2.mem p (2 * yl) = natVal s.mem xp yl * natVal s.mem yp yl := by
    rw [hval, hxv, hyv]
  have eM := hJ.hdr 0 (by omega); have eM8 := hJ.hdr 8 (by omega); have eM16 := hJ.hdr 16 (by omega)
  simp only [Nat.add_zero] at eM
  have eMW : stW M st = stW S.mem st := by simp only [stW]; rw [eM]; exact eW.symm
  have eML : stLen M st = stLen S.mem st := by simp only [stLen]; rw [eM8]; exact eL.symm
  have eMC : stCap M st = stCap S.mem st := by simp only [stCap]; rw [eM16]; exact eC.symm
  have ews : stkWs S.mem st = stkWs M st := by simp only [stkWs]; rw [eMW, eML, eMC]
  rw [ews] at hMF hLF
  rw [← eML] at hbud
  have hsb0 : StackBackL R L1 L1 st M S.mem := by
    have hstw := hJ.pre.2.2.2.2.2.2.1.2.2.1
    exact stackBack_keep' hJ.stk (ws := winA s W 88) (hF.widen R.rt) (lf_win' _ hF hLs)
      (winA_of_win' hstw) (LiveExt.refl R L1)
  have hsb2 := sbl_trans hsb0 hsb (LiveExt.refl R L1) hext
  have hws := ws_kar (R := R) (M := M) (st := st) (p := p) hs1 hW hb0 hyx
  have hfr : MemFrame M S2.mem (R.rt ++ winA s W 88 ++ lws M st p (xl + yl)) :=
    hF.trans (hMF.mono hws) fun a n h => ⟨by simp only [outside_append] at h; exact h.1.2, h⟩
  have hlf : LiveFrame M S2.mem L1 (lws M st p (xl + yl)) :=
    LiveFrame.trans (lf_win' _ hF hLs) (FvModexp.LiveFrame.mono_ws hLF (lf_kar hyx)) fun _ _ h => h
  refine ⟨L2, b2, fun S' hm hpc hsp h28 h29 h18 h10 => ?_⟩
  rw [← hm] at hval' hsb2 hfr hlf hinv2 hreg2 er1 er2 er144 er120 er96 er94 er304 er328 er136 er184 er296 er312 er320 er336
  have hlq : LQ R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M L2 b2 (KC (stLen M st) yl) S'.mem :=
    { core := hJ, h40 := h40, hlt := hyx, ext := hext, bud := hbud, inv := hinv2,
      reg := hreg2.trans hreg, fr := hfr, lf := hlf, sok := hsb2.1.1, sb := hsb2,
      lr := er1, fp := er2, c96 := er96, n120 := er120, n136 := er136, p144 := er144, s184 := er184,
      a296 := er296, a304 := er304, a312 := er312, a320 := er320, a328 := er328, a336 := er336, px := hpx,
      py := hpy }
  exact ⟨hlq, hpc, hsp, h28, h29, h18, h10, er94, hval'⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- `n < m`, `n ≥ 40`: the call `karatsuba(stk, z[:2n], x[:n], y)` at `0x1bb038` and the branch to `0x1bb054` (`KA`) -/
theorem karLt2 (impl : List Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R n0 (.kar, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hnx : p + 8 * c ≠ xp.toNat + 8 * xc.toNat) (hny : p + 8 * c ≠ yp.toNat + 8 * yc.toNat)
    (h40 : 40 ≤ yl.toNat) (hyx : yl.toNat < xl.toNat) (hμ : 8 * yl.toNat + 2 < n0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb038) (hsp : S.sp = s.sp - 256#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 264#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = st) (r1 : S.regs 1 = BitVec.ofNat 64 p) (r2 : S.regs 2 = BitVec.ofNat 64 (2 * yl.toNat))
    (r3 : S.regs 3 = BitVec.ofNat 64 c) (r4 : S.regs 4 = xp) (r5 : S.regs 5 = yl) (r6 : S.regs 6 = xc)
    (r7 : S.regs 7 = yp) (r8 : S.regs 8 = yl) (r9 : S.regs 9 = yc)
    (hF : MemFrame M S.mem (winA s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (m144 : S.mem.readLE (s.sp.toNat - 112) 8 = p) (m120 : S.mem.readLE (s.sp.toNat - 136) 8 = xl.toNat + yl.toNat)
    (m96 : S.mem.readLE (s.sp.toNat - 160) 8 = c) (m94 : S.mem.readLE (s.sp.toNat - 162) 1 = 0)
    (m304 : S.mem.readLE (s.sp.toNat + 48) 8 = xl.toNat) (m328 : S.mem.readLE (s.sp.toNat + 72) 8 = yl.toNat)
    (m136 : S.mem.readLE (s.sp.toNat - 120) 8 = 2 * yl.toNat) (m184 : S.mem.readLE (s.sp.toNat - 72) 8 = st.toNat)
    (m296 : S.mem.readLE (s.sp.toNat + 40) 8 = xp.toNat) (m312 : S.mem.readLE (s.sp.toNat + 56) 8 = xc.toNat)
    (m320 : S.mem.readLE (s.sp.toNat + 64) 8 = yp.toNat) (m336 : S.mem.readLE (s.sp.toNat + 80) 8 = yc.toNat)
    (mlr : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (Lk : List (Nat × Nat)) (bk : Nat) (S' : State),
      KA R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M Lk bk S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩, hmw, -, -, -, -, hstk, -⟩ := hpre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hkw := kW_call h40 (Nat.le_of_lt hyx)
  have hkg := kW_ge yl.toNat
  have hsp' : S.sp.toNat = s.sp.toNat - 256 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hp64 : p < 2 ^ 64 := by omega
  have e1 : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 (2 * yl.toNat)).toNat = 2 * yl.toNat := by simp only [BitVec.toNat_ofNat]; omega
  have e3 : (BitVec.ofNat 64 c).toNat = c := by simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hpwin : Outside p (8 * (2 * yl.toNat)) (win s W 88) := hJ.pw.of_sub (Nat.le_refl _) (by omega)
  have hBS : Summary (LibMul.program.link impl) 0x1bbe70 _ _ := Summary.mono
    (ih ⟨b1, L1, W - 256, st, BitVec.ofNat 64 p, BitVec.ofNat 64 (2 * yl.toNat), BitVec.ofNat 64 c, xp, yl, xc,
      yp, yl, yc⟩)
    (pre' := fun s1 => (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48 ∧
      s1.regs 0 = st ∧ s1.regs 1 = BitVec.ofNat 64 p ∧ s1.regs 2 = BitVec.ofNat 64 (2 * yl.toNat) ∧
      s1.regs 3 = BitVec.ofNat 64 c ∧ s1.regs 4 = xp ∧ s1.regs 5 = yl ∧ s1.regs 6 = xc ∧ s1.regs 7 = yp ∧
      s1.regs 8 = yl ∧ s1.regs 9 = yc ∧ s1.sp = S.sp ∧ s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (post' := fun s1 s2 => Kept s1 s2 ∧ s2.mem.accessible (s.sp.toNat - 264) 352 true = true ∧
      s2.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat ∧ s2.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat ∧
      s2.mem.readLE (s.sp.toNat - 112) 8 = p ∧ s2.mem.readLE (s.sp.toNat - 136) 8 = xl.toNat + yl.toNat ∧
      s2.mem.readLE (s.sp.toNat - 160) 8 = c ∧ s2.mem.readLE (s.sp.toNat - 162) 1 = 0 ∧
      s2.mem.readLE (s.sp.toNat + 48) 8 = xl.toNat ∧ s2.mem.readLE (s.sp.toNat + 72) 8 = yl.toNat ∧
      s2.mem.readLE (s.sp.toNat - 120) 8 = 2 * yl.toNat ∧ s2.mem.readLE (s.sp.toNat - 72) 8 = st.toNat ∧
      s2.mem.readLE (s.sp.toNat + 40) 8 = xp.toNat ∧ s2.mem.readLE (s.sp.toNat + 56) 8 = xc.toNat ∧
      s2.mem.readLE (s.sp.toNat + 64) 8 = yp.toNat ∧ s2.mem.readLE (s.sp.toNat + 80) 8 = yc.toNat ∧
      IntAS.Box (∃ S1 : State, S1.mem = S.mem ∧ S1.sp = S.sp ∧ S1.regs 28 = S.regs 28 ∧
        KPost R b1 L1 (W - 256) st.toNat p (2 * yl.toNat) xp.toNat yl.toNat yp.toNat yl.toNat S1 s2))
    (fun s1 ⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hs, hg, hm⟩ => by
      refine ⟨⟨⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, ?_⟩, hμ⟩
      show KPre R b1 L1 (W - 256) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * yl.toNat)).toNat
        (BitVec.ofNat 64 c).toNat xp.toNat yl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s1
      rw [e1, e2, e3]
      exact kpre_of hJ hpx hpy hnx hny h40 (Nat.le_of_lt hyx) (by rw [hs]; exact hsp') (by rw [hg, h28])
        (by rw [hm]; exact hF) (by rw [hm]; exact hreg))
    (fun s1 s2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, hg, hm⟩ ⟨hk, hq⟩ => by
      have hq' : KPost R b1 L1 (W - 256) st.toNat p (2 * yl.toNat) xp.toNat yl.toNat yp.toNat yl.toNat s1 s2 := by
        have := hq; rw [e1, e2] at this; exact this
      have hMF : MemFrame s1.mem s2.mem (R.rt ++ winA s1 (W - 256) 72 ++ (p, p + 8 * (2 * yl.toNat)) ::
          stkWs s1.mem st.toNat) := by
        obtain ⟨_, _, _, _, _, _, _, h, -⟩ := hq'; exact h
      have hsp1 : s1.sp.toNat = s.sp.toNat - 256 := by rw [hs]; exact hsp'
      have hkp := kar_keeps (W1 := W - 256) (S1 := s1) (m2 := s2.mem) hJ.pre hsp1 (by omega) (by omega)
        (by rw [hm]; exact eW) (by rw [hm]; exact eL) (by rw [hm]; exact eC) hpwin hMF
      have k1 : ∀ a n, (s.sp.toNat - 264 ≤ a ∧ a + n ≤ s.sp.toNat - 248) ∨
          (s.sp.toNat - 184 ≤ a ∧ a + n ≤ s.sp.toNat + 88) → s2.mem.readLE a n = S.mem.readLE a n := by
        intro a n h; rw [hkp a n (by omega), hm]
      exact ⟨hk, by rw [hMF.accessible, hm, hF.accessible, hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega),
        by rw [k1 _ _ (by omega)]; exact mlr, by rw [k1 _ _ (by omega)]; exact mfp,
        by rw [k1 _ _ (by omega)]; exact m144, by rw [k1 _ _ (by omega)]; exact m120,
        by rw [k1 _ _ (by omega)]; exact m96, by rw [k1 _ _ (by omega)]; exact m94,
        by rw [k1 _ _ (by omega)]; exact m304, by rw [k1 _ _ (by omega)]; exact m328,
        by rw [k1 _ _ (by omega)]; exact m136, by rw [k1 _ _ (by omega)]; exact m184,
        by rw [k1 _ _ (by omega)]; exact m296, by rw [k1 _ _ (by omega)]; exact m312,
        by rw [k1 _ _ (by omega)]; exact m320, by rw [k1 _ _ (by omega)]; exact m336, ⟨⟨s1, hm, hs, hg, hq'⟩⟩⟩)
  janus_run until [0x1bb03c] calls [hBS]
  rename_i ea er1 er2 er144 er120 er96 er94 er304 er328 er136 er184 er296 er312 er320 er336 hbox
  obtain ⟨⟨S1, hm1, hs1, hg1, hq⟩⟩ := hbox
  have hreg2 : s'.mem.regions = S.mem.regions := by janus_assumption
  have hs1' : S1.sp.toNat = s.sp.toNat - 256 := by rw [hs1, ← hsp]; exact hsp'
  obtain ⟨Lk, bk, hka⟩ := kaOf hJ hpx hpy h40 hyx hF hreg hm1 hs1' (by rw [hg1]; try rw [h28]) hq hreg2 er1 er2 er144 er120
    er96 er94 er304 er328 er136 er184 er296 er312 er320 er336
  obtain ⟨-, -, -, -, -, ⟨⟨-, -, hxl12, -⟩, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hJ.pre
  janus_run [er304, er328, toInt_small xl (by omega), toInt_small yl (by omega)] until [0x1bb054]
  exact hK Lk bk _ (hka _ rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp))

end FvModexp.Arm64.NatMul
