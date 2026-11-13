import FvModexp.Proofs.Arm64.NatQ.MulKPre
import FvModexp.Proofs.Arm64.NatQ.MulNorm
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.WinLemmas

/-!
# [Q-form copy of Arm64/Nat/MulKar.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), `40 ≤ n = m`: `karatsuba(stk, z[:2n], x[:n], y); return z.norm()` (natmul.go:43-55)

`kar_keeps`: `karatsuba`'s frame keeps `nat.mul`'s frame outside its window. `karEq2`: the call (`0x1bb038`, the
SCC induction hypothesis of member `.kar`), then `normB` (no deferred call) and `post_of`. `karEq`: the join → the call.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (StkPre)

theorem rr_mono {p : Program} {ret : BitVec 64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h; exact ⟨k, s', hs, hr, hQ s' hq⟩

set_option maxRecDepth 20000 in
/-- a callee called at `SP - 256` with a frame `R.rt ++ winA S1 W1 72 ++ (p, p + n') :: stkWs` (`karatsuba`) keeps
`nat.mul`'s frame outside its window -/
theorem kar_keeps {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat}
    {s : State} {S1 : State} {m2 : Memory} {W1 p n' : Nat} (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s)
    (hsp : S1.sp.toNat = s.sp.toNat - 256) (hk : 256 + W1 ≤ W) (hW1 : 96 ≤ W1)
    (eW : stW S1.mem st = stW s.mem st) (eL : stLen S1.mem st = stLen s.mem st)
    (eC : stCap S1.mem st = stCap s.mem st) (hp : Outside p n' (win s W 88))
    (hMF : MemFrame S1.mem m2 (R.rt ++ winA S1 W1 72 ++ (p, p + n') :: stkWs S1.mem st)) :
    ∀ a n, (S1.sp.toNat - 8 ≤ a ∧ a + n ≤ S1.sp.toNat + 8) ∨ (S1.sp.toNat + 72 ≤ a ∧ a + n ≤ s.sp.toNat + 88) →
      m2.readLE a n = S1.mem.readLE a n := by
  obtain ⟨hce, -, -, -, -, -, hstk, -, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨-, -, hstw, -, -, -, hfw, -⟩ := hstk
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw hp
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  intro a n h
  refine hMF.readLE _ _ ?_
  simp only [stkWs, winA, outside_append, outside_cons, outside_nil, and_true]
  rw [eW, eL, eC]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- `m = n ≥ 40`: the call `karatsuba(stk, z[:2n], x, y)` at `0x1bb038`, the normalisation and the return -/
theorem karEq2 (impl : List Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.kar, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hnx : p + 8 * c ≠ xp.toNat + 8 * xc.toNat) (hny : p + 8 * c ≠ yp.toNat + 8 * yc.toNat)
    (h40 : 40 ≤ yl.toNat) (hmn : xl.toNat = yl.toNat) (hμ : 8 * yl.toNat + 2 < n0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb038) (hsp : S.sp = s.sp - 256#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 264#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = st) (r1 : S.regs 1 = BitVec.ofNat 64 p) (r2 : S.regs 2 = BitVec.ofNat 64 (2 * yl.toNat))
    (r3 : S.regs 3 = BitVec.ofNat 64 c) (r4 : S.regs 4 = xp) (r5 : S.regs 5 = yl) (r6 : S.regs 6 = xc)
    (r7 : S.regs 7 = yp) (r8 : S.regs 8 = yl) (r9 : S.regs 9 = yc)
    (hF : MemFrame M S.mem (winA s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (m144 : S.mem.readLE (s.sp.toNat - 112) 8 = p) (m120 : S.mem.readLE (s.sp.toNat - 136) 8 = xl.toNat + yl.toNat)
    (m96 : S.mem.readLE (s.sp.toNat - 160) 8 = c) (m94 : S.mem.readLE (s.sp.toNat - 162) 1 = 0)
    (m304 : S.mem.readLE (s.sp.toNat + 48) 8 = xl.toNat) (m328 : S.mem.readLE (s.sp.toNat + 72) 8 = yl.toNat)
    (mlr : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩, hmw, -, -, -, -, hstk, -⟩ := hpre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hkw := kW_call h40 (Nat.le_of_eq hmn.symm)
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
      IntAS.Box (∃ S1 : State, S1.mem = S.mem ∧ S1.sp = S.sp ∧ S1.regs 28 = S.regs 28 ∧
        KPost R b1 H L1 (W - 256) st.toNat p (2 * yl.toNat) xp.toNat yl.toNat yp.toNat yl.toNat S1 s2))
    (fun s1 ⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hs, hg, hm⟩ => by
      refine ⟨⟨⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, ?_⟩, hμ⟩
      show KPre R b1 H L1 (W - 256) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * yl.toNat)).toNat
        (BitVec.ofNat 64 c).toNat xp.toNat yl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s1
      rw [e1, e2, e3]
      exact kpre_of hJ hpx hpy hnx hny h40 (by omega) (by rw [hs]; exact hsp') (by rw [hg, h28])
        (by rw [hm]; exact hF) (by rw [hm]; exact hreg))
    (fun s1 s2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, hg, hm⟩ ⟨hk, hq⟩ => by
      have hq' : KPost R b1 H L1 (W - 256) st.toNat p (2 * yl.toNat) xp.toNat yl.toNat yp.toNat yl.toNat s1 s2 := by
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
        by rw [k1 _ _ (by omega)]; exact m304, by rw [k1 _ _ (by omega)]; exact m328, ⟨⟨s1, hm, hs, hg, hq'⟩⟩⟩)
  janus_run until [0x1bb03c] calls [hBS]
  rename_i ea er1 er2 er144 er120 er96 er94 er304 er328 hbox
  obtain ⟨⟨S1, hm1, hs1, hg1, hq⟩⟩ := hbox
  obtain ⟨hval, L2, b2, hext, hbud, hinv2, hsb, hMF, hLF⟩ := hq
  rw [hm1] at hval hsb hMF hLF hbud
  rw [hg1] at hinv2
  obtain ⟨-, -, -, -, -, ⟨⟨-, -, hxl12, -, -, hxw⟩, ⟨-, -, hyl12, -, -, hyw⟩, -⟩, -⟩ := hJ.pre
  janus_run [er144, er120, er94, er304, er328, toInt_small xl (by omega), toInt_small yl (by omega)] until [hnormB]
  have hsacc : s'.mem.accessible (s.sp.toNat - 264) 264 true = true := Memory.accessible_mono _ ea (by omega) (by omega)
  have hxv : natVal S.mem xp.toNat yl.toNat = natVal s.mem xp.toNat xl.toNat := by
    rw [← hmn, natVal_frame hF (winA_of_win' (hxw (by omega)).1), hJ.xv (by omega)]
  have hyv : natVal S.mem yp.toNat yl.toNat = natVal s.mem yp.toNat yl.toNat := by
    rw [natVal_frame hF (winA_of_win' (hyw (by omega)).1), hJ.yv (by omega)]
  have v2 : natVal s'.mem p (xl.toNat + yl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat := by
    rw [show xl.toNat + yl.toNat = 2 * yl.toNat by omega, hval, hxv, hyv]
  have hk : makeB (xl.toNat + yl.toNat) + KCQ yl.toNat ≤ mulCQ xl.toNat yl.toNat := by
    unfold mulCQ; rw [hmn, Nat.max_self, Nat.min_self]; exact MCQ_kar h40
  have hws : ∀ a n, Outside a n (R.rt ++ winA s W 88 ++ (p, p + 8 * (xl.toNat + yl.toNat)) :: stkWs S.mem st.toNat) →
      Outside a n (R.rt ++ winA S1 (W - 256) 72 ++ (p, p + 8 * (2 * yl.toNat)) :: stkWs S.mem st.toNat) := by
    intro a n h
    have hs1' : S1.sp.toNat = s.sp.toNat - 256 := by rw [hs1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    rw [hs1', show 2 * yl.toNat = xl.toNat + yl.toNat by omega]
    have hk := Nat.le_of_eq (Nat.add_sub_cancel' (Nat.le_trans (show 256 ≤ 4608 by decide) hW))
    exact ⟨⟨h.1.1, (winA_in (c := 256) (k := (W - 256)) (ab := 72) hb0 hk (by decide) h.1.2.1).1, (winA_in (c := 256) (k := (W - 256)) (ab := 72) hb0 hk (by decide) h.1.2.1).2⟩, h.2⟩
  have hLF' : LiveFrame S.mem s'.mem L1 ((p, p + 8 * (xl.toNat + yl.toNat)) :: stkWs S.mem st.toNat) := by
    rw [show xl.toNat + yl.toNat = 2 * yl.toNat by omega]; exact hLF
  refine normB impl s s'.mem p c (xl.toNat + yl.toNat) (natVal s'.mem p (xl.toNat + yl.toNat)) 0
    (fun s3 => Kept s s3 ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s3)
    (fun S' n' hB hn' hv hnn => by
      have F3 : MemFrame s'.mem S'.mem (winA s W 88) := hB.fr.mono fun a n h => by
        simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
      refine rr_mono (retB0 impl s S' s'.mem p c n' hB er1 er2 hal0 (by omega) (by omega) hsacc hl4 hl48
        (by omega) (by omega) (by omega)) fun s3 ⟨hk3, hm3, q0, q1, q2⟩ => ⟨hk3, ?_⟩
      exact post_of hJ hF v2 hext (Or.inl hbud) hk hinv2 hsb (hMF.mono hws) hLF'
        (by rw [hm3]; exact F3) q0 q1 q2 hn' (by rw [hv]) hnn)
    (by omega) (by omega) (by omega) ?_ er96 (by decide) hal0 (by omega) (by omega) hsacc (xl.toNat + yl.toNat) _
    (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · rw [hMF.accessible, hF.accessible]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `m = n ≥ 40`: the join → the call of `karatsuba` -/
theorem karEq (impl : List Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.kar, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (h40 : 40 ≤ yl.toNat) (hmn : xl.toNat = yl.toNat)
    (hμ : 8 * yl.toNat + 2 < n0) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  obtain ⟨h40', hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, hsp, h28, h29, h18, mlr, mfp, m120, -, m304, -, -, m328, -, hreg,
    hpx, hpy, hnx, hny⟩ := hA
  have hst0 : st ≠ 0#64 := by
    obtain ⟨-, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    intro e; apply h; rw [e]; rfl
  have hst0' : (st = 0#64) = False := by simp only [eq_iff_iff, iff_false]; exact hst0
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -⟩, hmw, -, -, -, ⟨-, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hpre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hsacc : S.mem.accessible (s.sp.toNat - 264) 264 true = true := by
    rw [hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := hJ.live (by omega); omega
  janus_run [h40', hst0', toInt_small yl (by omega), toInt_small (BitVec.ofNat 64 40) (by decide)] until [0x1bb038]
  refine karEq2 impl R n0 ih hJ hpx hpy hnx hny h40 hmn hμ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [winA]; janus_frame) ?qreg ?q144 ?q120 ?q96 ?q94 ?q304 ?q328 ?qlr ?qfp hl4 hl48
  case qreg => janus_simp; exact hreg
  case q120 => janus_simp; exact m120
  case q304 => janus_simp; exact m304
  case q328 => janus_simp; exact m328
  case qlr => janus_simp; exact mlr
  case qfp => janus_simp; exact mfp
  all_goals try janus_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.Q.NatMul
