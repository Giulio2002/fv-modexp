import FvModexp.Proofs.Arm64.Nat.DivBigP
import FvModexp.Proofs.Arm64.Nat.DivBigF

/-!
# `nat.div` (arm64), `u ≥ v`: the `divLarge` call (premise `DivLarge.Hyp`), the results stored, return
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- after `divLarge` returned (`fn + 0x2d4`): results stored, the (unset) defer bit tested, return -/
theorem big3 (impl : List Segment) {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul v vl : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s)
    {X : State} (hsp : X.sp = s.sp - 240#64) (h28 : X.regs 28 = s.regs 28)
    (hF : MemFrame s.mem X.mem (winA s 41504 112))
    {q ql qc r rl rc : Nat} {L' : List (Nat × Nat)} {b'' : Nat} {T : State}
    (hq : ExpHyp.NatOF R L L' T.mem zp zc 1 q ql qc (natVal X.mem u ul / natVal X.mem v vl))
    (hr : ExpHyp.NatOF R L L' T.mem z2 z2c 1 r rl rc (natVal X.mem u ul % natVal X.mem v vl))
    (hrt : ExpHyp.RtPost R b (DivLarge.cost dc (stLen X.mem st) ul vl) L L' b'' X T)
    (hsb : StackBack R L L' st X.mem T.mem)
    (hfr : ¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap T.mem st →
      Apart r (8 * rc) (stW T.mem st) (8 * stCap T.mem st))
    (hmf : MemFrame X.mem T.mem (R.rt ++ winA X 41264 112 ++ (ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (hlf : LiveFrame X.mem T.mem L ((ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (T' : State) (hTe : T' = T)
    (hpcT : T.pc = BitVec.ofNat 64 retL) (hspT : T.sp = s.sp - 240#64) (h28T : T.regs 28 = s.regs 28)
    (h29T : T.regs 29 = s.sp - 248#64) (h18T : T.regs 18 = s.regs 18)
    (e0 : T.regs 0 = BitVec.ofNat 64 q) (e1 : T.regs 1 = BitVec.ofNat 64 ql) (e2 : T.regs 2 = BitVec.ofNat 64 qc)
    (e3 : T.regs 3 = BitVec.ofNat 64 r) (e4 : T.regs 4 = BitVec.ofNat 64 rl) (e5 : T.regs 5 = BitVec.ofNat 64 rc)
    (m1 : T.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (m2 : T.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat) (m3 : T.mem.readLE (s.sp.toNat - 122) 1 = 0)
    (hTacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T' (RQ R b dc L zp zc st z2 z2c u ul v vl s) := by
  subst hTe
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hp.ce
  have hB : Box (Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) := ⟨hpre⟩
  have hB2 := Box.mk (And.intro hq (And.intro hr (And.intro hrt (And.intro hsb (And.intro hfr (And.intro hmf hlf))))))
  clear hpre hp hmf hlf hq hr hrt hsb hfr
  janus_run [m1, m2, m3, e0, e1, e2, e3, e4, e5]
  obtain ⟨hpre⟩ := hB
  obtain ⟨hq, hr, hrt, hsb, hfr, hmf, hlf⟩ := hB2.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, bigFin hpre hsp h28 hF hq hr hrt hsb hfr hmf hlf _ (by janus_frame) ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals janus_simp
  all_goals exact ofNat_modL _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem big2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) (hsep : HdrSep s st)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivLarge.fn)) (hsp : X.sp = s.sp - 240#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 248#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 retL)
    (hr0 : X.regs 0 = BitVec.ofNat 64 zp) (hr1 : X.regs 1 = BitVec.ofNat 64 zl) (hr2 : X.regs 2 = BitVec.ofNat 64 zc)
    (hr3 : X.regs 3 = BitVec.ofNat 64 st) (hr4 : X.regs 4 = BitVec.ofNat 64 z2) (hr5 : X.regs 5 = BitVec.ofNat 64 z2l)
    (hr6 : X.regs 6 = BitVec.ofNat 64 z2c) (hr7 : X.regs 7 = BitVec.ofNat 64 u) (hr8 : X.regs 8 = BitVec.ofNat 64 ul)
    (hr9 : X.regs 9 = BitVec.ofNat 64 uc) (hr10 : X.regs 10 = BitVec.ofNat 64 v)
    (hr11 : X.regs 11 = BitVec.ofNat 64 vl) (hr12 : X.regs 12 = BitVec.ofNat 64 vc)
    (hF : MemFrame s.mem X.mem (winA s 41504 112)) (hreg : X.mem.regions = s.mem.regions)
    (mlr : X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (mfp : X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat) (mby : X.mem.readLE (s.sp.toNat - 122) 1 = 0)
    (hzp : zp < 2 ^ 64) (hz2 : z2 < 2 ^ 64) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X (RQ R b dc L zp zc st z2 z2c u ul v vl s) := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hp.ce
  have hspn : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hz40 := hp.zo.1; have hz240 := hp.z2o.1; have hul := hp.ul9; have hvl := hp.vl9
  have hu48 := hp.uo.2.2.1; have hv48 := hp.vo.2.2.1
  have hst48 := hp.sok.2.2.2.1
  have e : ∀ x, x < 2 ^ 64 → (BitVec.ofNat 64 x).toNat = x := fun x h => tN h
  have hsum := lsum impl hap R dc hL b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 z2) (BitVec.ofNat 64 z2l) (BitVec.ofNat 64 z2c) (BitVec.ofNat 64 u)
    (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) (BitVec.ofNat 64 v) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 vc)
  have e30 : (X.regs 30).toNat = retL := by rw [h30]; decide
  have ezp := e zp hzp; have ezc := e zc (by omega); have est := e st (by omega); have ez2 := e z2 hz2
  have ez2c := e z2c (by omega); have eu := e u (by omega); have eul := e ul (by omega); have ev := e v (by omega)
  have evl := e vl (by omega)
  have i1 : s.sp.toNat - 248 ≤ s.sp.toNat - 240 := by omega
  have i2 : s.sp.toNat - 240 + 8 ≤ s.sp.toNat - 232 := by omega
  have i3 : s.sp.toNat - 248 + 8 ≤ s.sp.toNat - 232 := by omega
  have i4 : s.sp.toNat - 122 + 1 ≤ s.sp.toNat - 121 := by omega
  refine ReachesRet.call_regions hsum hpc ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [e30]; exact raD impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]
    exact ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, trivial⟩
  case pre =>
    rw [ezp, ezc, est, ez2, ez2c, eu, eul, ev, evl]
    exact l_pre hpre hsep hge hv2 X hsp h28 hF hreg
  rw [ezp, ezc, est, ez2, ez2c, eu, eul, ev, evl] at hq
  obtain ⟨q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b'', hq', hr', hrt, hsb, hfr, hmf, hlf⟩ := hq
  have hk := slots_keep hpre hsp hF hmf
  have m1 : T.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat := by rw [hk _ _ (Or.inl ⟨i1, i2⟩)]; exact mlr
  have m2 : T.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat := by rw [hk _ _ (Or.inl ⟨Nat.le_refl _, i3⟩)]; exact mfp
  have m3 : T.mem.readLE (s.sp.toNat - 122) 1 = 0 := by rw [hk _ _ (Or.inr ⟨Nat.le_refl _, i4⟩)]; exact mby
  have hpcT : T.pc = BitVec.ofNat 64 retL := by rw [hT, h30]
  have hspT : T.sp = s.sp - 240#64 := by rw [f1, hsp]
  have h28T : T.regs 28 = s.regs 28 := by rw [f2, h28]
  have h29T : T.regs 29 = s.sp - 248#64 := by rw [f3, h29]
  have h18T : T.regs 18 = s.regs 18 := by rw [f4, h18]
  have hTacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by
    rw [hmf.accessible, hF.accessible]; exact hw
  exact big3 impl hpre hsp h28 hF hq' hr' hrt hsb hfr hmf hlf T rfl hpcT hspT h28T h29T h18T e0 e1 e2 e3 e4 e5 m1 m2 m3
    hTacc hl4 hl48

end FvModexp.Arm64.NatDiv
