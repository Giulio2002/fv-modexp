import FvModexp.Proofs.Amd64.NatQ.RemPost
import FvModexp.Proofs.Amd64.NatQ.RemPro

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): the composition — `full` (Summary on `LibRem`) and `ens : NHyp.RemHypQ`
(premise: `div` as `ExpHyp.DivHypLQ`; twin of Arm64/NatQ/RemEns.lean, divmc s59)

entry → `pro` → `CALL (*stack).nat` (`natc`, pre `sn_pre`, post `sn_of`) → stack-argument stores + `CALL nat.div`
(`divc`, pre `dv_pre` after `SN.frameX`) → `atU` → `fin` (closure `stk.restore`, `RET`) → `post`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

open FvModexp.Amd64.NHyp (RemPreQ CPostRQ)

variable {H : Nat}

theorem rr_mono {p : Amd64.Program} {ret : W64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h
  exact ⟨k, s', hs, hr, hQ s' hq⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {cd : Nat → Nat → Nat} (hD : ExpHyp.DivHypLQ impl R LibDiv.names 41512 112 cd)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc : BitVec 64) (v vl vc : Nat) :
    Summary (LibRem.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = z ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = st ∧ s.regs 6 = u ∧ s.regs 8 = ul ∧
        s.regs 9 = uc ∧
        RemPreQ R b H L 41720 112 z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v vl vc
          (need ul.toNat vl) (cd ul.toNat vl + stkR H s.mem st.toNat) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
          s'.xmm 15 = s.xmm 15) ∧
        CPostRQ R b L 41720 112 z.toNat zc.toNat st.toNat (natVal s.mem u.toNat ul.toNat % natVal s.mem v vl)
          (cd ul.toNat vl + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  have hpre0 := hpre
  obtain ⟨⟨hv1, hv2, hv3⟩, hce, -, -, -, -, -, -, hins, hsok0, hsw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hna, -, -⟩ := hpre0
  have hce0 := hce
  obtain ⟨-, ⟨hb, ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce0
  simp only [regSP] at hb ha hw
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hsok0
  have hu9 := (hins u.toNat ul.toNat (by simp)).2.1
  have hv9 := (hins v vl (by simp)).2.1
  clear hins
  have hswO := hsw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  refine pro impl R L s z zl zc st u ul uc vl hpc h0 h3 h1 h7 h6 h8 h9 hce hv2
    (Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hstacc) (by omega) (by omega))
    hst48 hsw hv9 hu9 hna _ fun P hP => ?_
  refine natc impl hap R hgr hmc hwb hpre hP hx15 hdf
    fun T t1 t2 t5 t14 tx tfs tdf treg q0 q1 q2 hsl L1 b1 hN => ?_
  have hLs1 : LiveSep L1 (win s 41720 112) := hN.ext.liveSep hLs (fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega))
  have hlT := hN.len
  have hlcT := hN.sok.2.2.2.2.2.1
  have hrk := rnd_ge (kq ul.toNat vl)
  have hkp := kq_pos ul.toNat vl
  obtain ⟨-, -, -, hwT48⟩ := hN.sok.2.2.2.2.1 (by omega)
  -- `SN` and the stack header across the stores before `CALL nat.div`
  have hNX : ∀ X : State, AtDiv s T X u.toNat ul.toNat uc.toNat v vl vc →
      SN R b H L st.toNat (kq ul.toNat vl) s X.mem L1 b1 ∧ stW X.mem st.toNat = stW T.mem st.toNat ∧
        (X.regs 4).toNat = (s.regs 4).toNat - 208 ∧
        Sl s z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat X.mem := by
    intro X hAt
    have hXsp : (X.regs 4).toNat = (s.regs 4).toNat - 208 := by
      rw [hAt.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    refine ⟨hN.frameX hAt.mf hAt.reg (by omega) hswO (hout.of_sub (by omega) (by omega)) hLs hLs1, hAt.mf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hXsp, hsl.frame hAt.mf (fun a n h1 h2 => by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)⟩
  refine divc impl hap R hD H b1 L1 s T z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v vl vc
    (stW T.mem st.toNat + 8 * stLen s.mem st.toNat) (kq ul.toNat vl)
    ⟨by omega, by simp only [kq]; omega, st.isLt, z.isLt, zl.isLt, zc.isLt⟩ t1 t2 (by rw [tx, hx15]; rfl) (by rw [tdf, hdf])
    q0 q1 q2 hsl (hsl.v1.trans hv1) (hsl.v2.trans hv2) (hsl.v3.trans hv3) hb ha
    (by rw [hN.mf.accessible]; exact hw) (fun X hAt => ?_) fun U X hAt u1 u2 u5 u14 ux ureg hDp => ?_
  · obtain ⟨hNx, eW, -, -⟩ := hNX X hAt
    rw [← eW]
    exact dv_pre hpre hNx hAt.sp (hAt.r14.trans t14) (hAt.fs.trans tfs) hAt.a1 hAt.a2 hAt.a3 hAt.a4 hAt.a5 hAt.a6
  obtain ⟨hNx, eW, hXsp, hslX⟩ := hNX X hAt
  obtain ⟨ufs, udf, -, -, -, r, rl, rc, -, -, -, e7, e6, e8, L2, b2, -, hr, ⟨hx2, hbud2, hinv2⟩, hsb, hfr, hMF2,
    hLF2⟩ := hDp
  rw [← eW] at hMF2 hLF2
  rw [hAt.r14, t14] at hinv2
  have hslU := atU hpre hNx hXsp hMF2 hslX
  have hacU : ∀ a n w, U.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hMF2.accessible, hNx.mf.accessible]
  have hcapU : stLen s.mem st.toNat ≤ stCap U.mem st.toNat := by
    have h1 := hsb.1.1.2.2.2.2.2.1; have h2 := hsb.1.2.1; have h3 := hNx.len; omega
  have hrb : r < 2 ^ 64 ∧ rl < 2 ^ 64 ∧ rc < 2 ^ 64 := by
    obtain ⟨-, -, hrl, hrc, hlive, hloc⟩ := hr
    rcases hloc with ⟨rfl, -⟩ | ⟨hc1, -⟩
    · exact ⟨z.isLt, by omega, by omega⟩
    · obtain ⟨-, -, -, h48⟩ := hlive (by omega); exact ⟨by omega, by omega, by omega⟩
  refine rr_mono (fin impl s U z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat r rl rc
    u1 u2 (u14.trans t14) (ufs.trans (hAt.fs.trans tfs)) (udf.trans hAt.df) e7 e6 e8 hslU hal hb ha
    (by rw [hacU]; exact hw) (by rw [hacU]; exact hstacc) hst48 hsw hcapU hrb.1 hrb.2.1 hrb.2.2 hra) ?_
  intro s' ⟨⟨k4, k5, k14, k15⟩, gfs, gdf, g0, g3, g1, hF3, hlen3⟩
  refine ⟨⟨k4, k5, k14, by rw [k15, ux, tx]⟩, post hpre hNx hXsp hr hx2 hbud2 hinv2 hsb hfr hMF2 hLF2 s' hF3 hlen3
    gfs ?_ g0 g3 g1⟩
  rw [gdf, udf, hAt.df, hdf]

/-- **`nat.rem`** (amd64, Q-form) given `div` (`ExpHyp.DivHypLQ`): `NHyp.RemHypQ` on `LibRem` -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {cd : Nat → Nat → Nat} (hD : ExpHyp.DivHypLQ impl R LibDiv.names 41512 112 cd) :
    NHyp.RemHypQ impl R LibRem.names 41720 112 need cd := by
  intro H b L z zl zc st u ul uc v vl vc
  rw [show NHyp.fnRem = fn from rfl, ← LibRem.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  exact Summary.returns (full (H := H) impl hap R hgr hmc hwb hD b L z zl zc st u ul uc v vl vc) hret
    (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
      h_a3, h_a4, h_a5, h_a6, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

end FvModexp.Amd64.Q.NatRem
