import FvModexp.Proofs.Amd64.NatQ.DivCmp
import FvModexp.Proofs.Amd64.NatQ.DivLessRel
import FvModexp.Proofs.Amd64.NatQ.DivMBase

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u` (`(*Int).Mod`'s call), `len v ≥ 2`: `cmp`, and `u < v` (`r = u[:len u]`) — part A (top s40)

Twin of Arm64/NatQ/DivMLessA.lean: `two1M` / `two2M` / `lessRM` = the `PreG` forms `two1G` (DivZCmp) / `two2G`
(DivZTwo) / `lessRG` (DivZLess) on `PFM` (`IMod.DivPreM`'s conjuncts; `u` possibly empty with any pointer: `RdIn0`),
`lessRM` with `z2 = u` (`len u ≤ cap u`: `r = u[:len u]`, no allocation).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `nat.cmp`'s entry (`len v ≥ 2`), from `PFM` -/
theorem two1M (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = z2)
    (h8 : s.regs 8 = z2l) (h9 : s.regs 9 = z2c) (hv2 : 2 ≤ vl)
    (hpre : PFM R b dc L u ul uc v vl vc s)
    (Q : State → Prop)
    (k : ∀ X : State, AtK zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s X →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) s Q := by
  have hp := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have r1 := hp.su; have r2 := hp.sul; have r3 := hp.suc; have r4 := hp.sv; have r5 := hp.svl; have r6 := hp.svc
  have hvl : vl < 2 ^ 40 := hp.vo.1
  have hul : ul < 2 ^ 40 := hp.ui.1
  have hv0 : (BitVec.ofNat 64 vl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
  have hv1 : (BitVec.ofNat 64 vl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  clear hpre hp
  janus64_run [r1, r2, r3, r4, r5, r6, hv0, hv1] until [cmpE]
  refine k _
    { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, a0 := ?_, a3 := ?_, a1 := ?_,
      a7 := ?_, a6 := ?_, a8 := ?_, rc := ?_, mf := ?qF, reg := ?qR, bp := ?_, s1 := ?_, s2 := ?_, s3 := ?_,
      s4 := ?_, s5 := ?_, s6 := ?_, s7 := ?_, q0 := ?_ }
  case qF => unfold proW; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals first | exact hx15 | exact hdf | (janus64_simp; omega) | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem two2M (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (s : State)
    (hpre : PFM R b dc L u ul uc v vl vc s)
    (X : State) (hX : AtK zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s X)
    (Q : State → Prop)
    (k : ∀ S, AtC zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s S →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q := by
  have hp := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hul := hp.ui.1
  obtain ⟨hvl, hvacc, hv48, -, hvw⟩ := hp.vo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hF := hX.mf
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [hX.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have hu64 : u < 2 ^ 64 := by rw [← hp.su]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have t0 : (X.regs 0).toNat = u := by rw [hX.a0, BitVec.toNat_ofNat]; omega
  have t3 : (X.regs 3).toNat = ul := by rw [hX.a3, BitVec.toNat_ofNat]; omega
  have t7 : (X.regs 7).toNat = v := by rw [hX.a7, BitVec.toNat_ofNat]; omega
  have t6 : (X.regs 6).toNat = vl := by rw [hX.a6, BitVec.toNat_ofNat]; omega
  have hpre' : CmpSum.Pre X := by
    unfold CmpSum.Pre CmpSum.SliceOK
    rw [t0, t3, t7, t6, hspn, show (s.regs 4).toNat - 240 = (s.regs 4).toNat - 240 from rfl, hX.rc]
    refine ⟨by decide, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · by_cases h0 : ul = 0
      · exact Or.inl h0
      · obtain ⟨-, huacc, hu48, -, huw⟩ := hp.ui.2 (by omega)
        simp only [win, outside_cons, outside_nil, and_true] at huw
        exact Or.inr ⟨by rw [hF.accessible]; exact huacc, by unfold Apart; omega⟩
    · exact Or.inr ⟨by rw [hF.accessible]; exact hvacc, by unfold Apart; omega⟩
  refine ReachesRet.call_regions (csum impl hap) hX.pc hpre' fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v6, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  rw [hspn] at hf
  have hslot : ∀ a n, (a + n ≤ (s.regs 4).toNat - 248 ∨ (s.regs 4).toNat - 200 ≤ a) →
      m.readLE a n = X.mem.readLE a n := fun a n h =>
    hf.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hU : X.mem.readLE u (8 * ul) = s.mem.readLE u (8 * ul) := by
    by_cases h0 : ul = 0
    · simp only [h0, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]
    · obtain ⟨-, -, hu48, -, huw⟩ := hp.ui.2 (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at huw
      exact hrd _ _ (by omega)
  have hV : X.mem.readLE v (8 * vl) = s.mem.readLE v (8 * vl) := hrd _ _ (by omega)
  have hraS : X.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  refine k _
    { pc := by simp only [retAddrOf]; rw [hspn, hX.rc]
      sp := by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [hX.sp]; bv_omega
      r5 := by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hX.r5
      r14 := by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hX.r14
      fs := hX.fs
      x15 := hX.x15
      df := hX.df
      r0 := by
        simp only [setRegF_apply, ↓reduceIte]
        rw [t3, t6, t0, t7]
        show CmpSum.cmpRes _ _ (X.mem.readLE u (8 * ul)) (X.mem.readLE v (8 * vl)) = _
        rw [hU, hV]; rfl
      mf := hF.trans hf fun a n h => by simp only [win, proW, outside_cons, outside_nil, and_true] at h ⊢; omega
      reg := by rw [hrg, hX.reg]
      ra := by rw [hslot _ _ (by omega)]; exact hraS
      bp := by rw [hslot _ _ (by omega)]; exact hX.bp
      s1 := by rw [hslot _ _ (by omega)]; exact hX.s1
      s2 := by rw [hslot _ _ (by omega)]; exact hX.s2
      s3 := by rw [hslot _ _ (by omega)]; exact hX.s3
      s4 := by rw [hslot _ _ (by omega)]; exact hX.s4
      s5 := by rw [hslot _ _ (by omega)]; exact hX.s5
      s6 := by rw [hslot _ _ (by omega)]; exact hX.s6
      s7 := by rw [hslot _ _ (by omega)]; exact hX.s7
      s8 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.su
      s9 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.sul
      s10 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.suc
      s11 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.sv
      s12 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.svl
      s13 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.svc
      q0 := by rw [hslot _ _ (by omega)]; exact hX.q0 }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `len u ≤ cap u` (incl. `len u = 0`): `r = u[:len u]`, from `PFM` (`u = u`) -/
theorem lessRM (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2l u ul uc v vl vc : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v vl vc s) {S : State}
    (hS : AtC zp zl zc st u z2l uc u ul uc v vl vc s S) (hr0 : S.regs 0 = 18446744073709551615#64)
    (hz : ul ≤ uc) (Q : State → Prop)
    (k : ∀ S', AtS R b L zp zc u uc u ul s u uc L b S' →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hinv0 := hp.inv
  have hul := hp.ul9
  have hz40 := hp.uo.1
  obtain ⟨hinv1, hmf1, hlf1⟩ := winOnly hce hinv0 hS.mf
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hS.mf.accessible]; exact hw
  have m0 := hS.ra; have m1 := hS.bp; have m3 := hS.s1; have m4 := hS.s3; have m5 := hS.s5; have m6 := hS.s7
  have m7 := hS.s8; have m8 := hS.s9
  have hreg := hS.reg
  have hzp : zp < 2 ^ 64 := by rw [← hS.s1]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.s3]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  clear hpre hp hS hce hinv0
  janus64_run [hr0, m0, m1, m3, m4, m5, m6, m7, m8, BitVec.msb_eq_decide] until [joinS]
  refine k _
    { pc := rfl
      sp := ?_
      r5 := ?_
      r14 := ?_
      fs := ?_
      x15 := ?_
      df := ?_
      r0 := ?_
      r1 := ?_
      r3 := ?_
      r2 := ?_
      arr := Or.inl ⟨rfl, rfl, hz⟩
      ext := LiveExt.refl R L
      bud := Nat.sub_le _ _
      inv := RtInv.inv_frame' (ws := [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)]) (by janus_frame)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          left; exact hout.of_sub (by simp only; omega) (by simp only; omega)) hinv1
      mf := hmf1.trans (by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)])
        fun a n h => ⟨h, by simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
      lf := ⟨fun a n hin ho => by
        rw [(by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)]).readLE a n ?_]
        · exact hlf1.readLE a n hin ho
        · obtain ⟨r, hr, i1, i2⟩ := hin
          have := hLs r hr
          simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega⟩
      reg := ?_
      ra := ?_
      bp := ?_
      q0 := ?_
      q1 := ?_
      q2 := ?_
      s8 := ?_ }
  all_goals try (janus64_simp; done)
  all_goals first | exact hx15 | exact hdf | exact hfs | (janus64_simp; omega)

end FvModexp.Amd64.Q.NatDiv
