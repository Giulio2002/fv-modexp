import FvModexp.Proofs.Arm64.NatQ.RemPost
import FvModexp.Proofs.Arm64.NatQ.RemPro
import FvModexp.Proofs.Arm64.NatQ.RemDivC
import FvModexp.Proofs.Arm64.NatQ.RemSnPre

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/RemEns.lean, TIGHT COSTS, asm s38)
# `nat.rem` (arm64): the composition — `full` (Summary on `LibRem`) and `ens : RemHypNA` (premise: `div` as `DHyp`)

entry → `pro` → `CALL (*stack).nat` (`natc`, pre `sn_pre`) → `sn_of` → `CALL nat.div` (`divc`, pre `dv_pre`) →
`atU` → `fin` (closure `stk.restore`, `RET`) → `post`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.Q.NatRem
open FvModexp.Arm64.NatRem
variable {H : Nat}

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

theorem rr_mono {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h
  exact ⟨k, s', hs, hr, hQ s' hq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {cd : Nat → Nat → Nat} (hD : DHyp impl R cd)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64) :
    Summary (LibRem.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = z ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = st ∧ s.regs 4 = u ∧ s.regs 5 = ul ∧ s.regs 6 = uc ∧ s.regs 7 = v ∧
        s.regs 8 = vl ∧ s.regs 9 = vc ∧
        Pre R b H cd L z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b H cd L z.toNat zc.toNat st.toNat u.toNat ul.toNat v.toNat vl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpre⟩
  have hpre0 := hpre
  obtain ⟨⟨⟨hce, -, -, -, -, -, -, hins, hsok0, hsw, -, -, -, -, -, -, -, -, -, -, -, -⟩, -⟩, hna, -⟩ := hpre0
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, -, -, hga, -, -, -⟩ := hce
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hsok0
  have hu9 := (hins u.toNat ul.toNat (by simp)).2.1
  have hv9 := (hins v.toNat vl.toNat (by simp)).2.1
  clear hins
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  refine pro impl s z zl zc st u ul uc v vl vc hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hg1 hg2 hg3 hal hb ha hw hga
    (Memory.accessible_read_of_write _ hstacc) hst48 hsw hv9 hu9 hna _ fun P hP => ?_
  refine natc impl hap R hgr hmc hwb H b L st.toNat (kq ul.toNat vl.toNat) st.isLt (by simp only [kq]; omega) P
    (s.regs 30) hP.pc hP.r0 hP.r1 (sn_pre hpre hP) _ fun T t1 t2 t3 t4 t5 t6 hQ => ?_
  obtain ⟨q0, q1, q2, hsl, L1, b1, hN⟩ := sn_of hpre hP t2 t3 t6 hQ
  have hTsp : T.sp = s.sp - 208#64 := t2.trans hP.sp
  have hT28 : T.regs 28 = s.regs 28 := t3.trans hP.r28
  have hlcT := hN.sok.2.2.2.2.2.1
  have hlT := hN.len
  have hrk := rnd_ge (kq ul.toNat vl.toNat)
  obtain ⟨-, -, -, hwT48⟩ := hN.sok.2.2.2.2.1 (by have := kq_pos ul.toNat vl.toNat; omega)
  refine divc impl hap R hD H b1 L1 s T z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat
    vc.toNat (stW T.mem st.toNat + 8 * stLen s.mem st.toNat) (kq ul.toNat vl.toNat) (s.regs 30)
    ⟨z.isLt, zl.isLt, zc.isLt, st.isLt, u.isLt, ul.isLt, uc.isLt, v.isLt, vl.isLt, vc.isLt, by omega,
      by simp only [kq]; omega⟩
    t1 hTsp hb hal ha (by rw [hN.mf.accessible]; exact hw) q0 q1 q2 hsl
    (fun X xm xsp x28 => dv_pre hpre hN X (xsp.trans hTsp) (x28.trans hT28) xm) _
    fun U X xm xsp x28 u1 u2 u3 u4 u5 u6 hDp => ?_
  obtain ⟨q, ql, qc, r, rl, rc, -, -, -, e3, e4, e5, L2, b2, -, hr, ⟨hx2, hbud2, hinv2⟩, hsb, hfr, hMF2, hLF2⟩ :=
    hDp
  have hXsp : X.sp.toNat = s.sp.toNat - 208 := by
    rw [xsp, hTsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  rw [xm] at hMF2 hLF2 hr hbud2 hsb
  rw [x28, hT28] at hinv2
  obtain ⟨hslU, hgU⟩ := atU hpre hN hXsp hMF2 hsl
  have hacU : ∀ a n w, U.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hMF2.accessible, hN.mf.accessible]
  have hcapU : stLen s.mem st.toNat ≤ stCap U.mem st.toNat := by
    have h1 := hsb.1.1.2.2.2.2.2.1; have h2 := hsb.1.2.1; omega
  have hrb : r < 2 ^ 64 ∧ rl < 2 ^ 64 ∧ rc < 2 ^ 64 := by
    obtain ⟨-, -, hrl, hrc, hlive, hloc⟩ := hr
    rcases hloc with ⟨rfl, -⟩ | ⟨hc1, -⟩
    · exact ⟨z.isLt, by omega, by omega⟩
    · obtain ⟨-, -, -, h48⟩ := hlive (by omega); exact ⟨by omega, by omega, by omega⟩
  refine rr_mono (fin impl s U z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat vc.toNat r rl rc
    u1 (u2.trans hTsp) (u3.trans hT28) (u4.trans (t4.trans hP.r29)) (u5.trans (t5.trans hP.r18)) e3 e4 e5 hslU
    hg1 (by rw [hacU]; exact hg2) (by rw [hgU]; exact hg3) hal hb ha (by rw [hacU]; exact hw) hga
    (by rw [hacU]; exact hstacc) hst48 hsw hcapU hrb.1 hrb.2.1 hrb.2.2 hl4 hl48) ?_
  intro s' ⟨hk, g0, g1, g2, hF3, hlen3⟩
  exact ⟨hk, post hpre hN xm hXsp (x28.trans hT28) hr hx2 hbud2 hinv2 hsb hfr hMF2 hLF2 s' hF3 hlen3 g0 g1 g2⟩

/-- **`nat.rem`** (arm64) given `div` (`DHyp`): `RemHypNA` (= `NHyp.RemHyp` + `0 < st`) on `LibRem` -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {cd : Nat → Nat → Nat} (hD : DHyp impl R cd) :
    NHyp.RemHypQ impl R LibRem.names 41712 112 need cd := by
  intro H b L z zl zc st u ul uc v vl vc
  rw [← LibRem.eq_only]
  janus_ensures_old [FvModexp.Arm64.NHyp.CPre, FvModexp.stkR, FvModexp.stLen, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.StackNat.wT, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, FvModexp.Arm64.NHyp.freeOf, FvModexp.Arm64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.StackNat.wbA, FvModexp.Arm64.RunIface.gA, FvModexp.stkRes, FvModexp.potK, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full (H := H) impl hap R hgr hmc hwb hD b L z zl zc st u ul uc v vl vc)
    hret h_pc h_lr ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.Q.NatRem
