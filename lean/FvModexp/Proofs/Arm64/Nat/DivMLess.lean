import FvModexp.Proofs.Arm64.Nat.DivMDefs
import FvModexp.Proofs.Arm64.Nat.DivCmpB
import FvModexp.Proofs.Arm64.Nat.DivLess

set_option autoImplicit false

/-!
# `nat.div` (arm64), `z = nil`, `z2 = u` (`(*Int).Mod`'s call), `len v ≥ 2`: `cmp`, and `u < v` (`r = u.set(u)`)

`two1G`/`two2M`/`lessRM` = `two1`/`two2`/`lessR` (DivCmp/DivCmpB/DivLess) from the facts they use (`u` possibly empty
with any pointer: `RdIn0`). `lessSM`: with `z2 = u`, `z2.set(u)` reuses `u`'s array (`len u ≤ cap u`) and the copy is
skipped (`CMP`/`BEQ` on equal pointers), so `r = u[:len u]` = `U = U mod V`; `lessFinM` its postcondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `nat.cmp`'s entry (`len v ≥ 2`) -/
theorem two1G (impl : List Segment) (R : RtInv) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c up ul uc vp vl vc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = z2)
    (h5 : s.regs 5 = z2l) (h6 : s.regs 6 = z2c) (h7 : s.regs 7 = up) (h8 : s.regs 8 = ul) (h9 : s.regs 9 = uc)
    (h10 : s.regs 10 = vp) (h11 : s.regs 11 = vl) (h12 : s.regs 12 = vc) (hv2 : 2 ≤ vl.toNat)
    (hce : CallEnv R L s 41504 112)
    (Q : State → Prop)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 cmpE → X.sp = s.sp - 240#64 →
      X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 248#64 → X.regs 18 = s.regs 18 →
      X.regs 30 = BitVec.ofNat 64 retC → X.regs 0 = up → X.regs 1 = ul → X.regs 2 = uc → X.regs 3 = vp →
      X.regs 4 = vl → X.regs 5 = vc →
      MemFrame s.mem X.mem (proW s) → X.mem.regions = s.mem.regions →
      X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat → X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat →
      X.mem.readLE (s.sp.toNat + 8) 8 = zp.toNat → X.mem.readLE (s.sp.toNat + 16) 8 = zl.toNat →
      X.mem.readLE (s.sp.toNat + 24) 8 = zc.toNat → X.mem.readLE (s.sp.toNat + 32) 8 = st.toNat →
      X.mem.readLE (s.sp.toNat + 40) 8 = z2.toNat → X.mem.readLE (s.sp.toNat + 48) 8 = z2l.toNat →
      X.mem.readLE (s.sp.toNat + 56) 8 = z2c.toNat → X.mem.readLE (s.sp.toNat + 64) 8 = up.toNat →
      X.mem.readLE (s.sp.toNat + 72) 8 = ul.toNat → X.mem.readLE (s.sp.toNat + 80) 8 = uc.toNat →
      X.mem.readLE (s.sp.toNat + 88) 8 = vp.toNat → X.mem.readLE (s.sp.toNat + 96) 8 = vl.toNat →
      X.mem.readLE (s.sp.toNat + 104) 8 = vc.toNat →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hce
  have hv0 : (vl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hv2; simp at hv2
  have hv1 : (vl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hv2; simp at hv2
  janus_run [hv0, hv1] until [cmpE]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qR ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case qF => unfold proW; janus_frame
  case qR => simp only [Memory.regions_writeLE]
  all_goals try (janus_simp; done)
  all_goals (janus_simp; omega)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- at `nat.cmp`'s entry: the call, then `AtC` -/
theorem two2M (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {b : Nat} {dc : Nat → Nat → Nat → Nat} (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c up ul uc vp vl vc : BitVec 64) (s : State)
    (hp : PFM R b dc L up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 cmpE) (hsp : X.sp = s.sp - 240#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 248#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 retC) (hr0 : X.regs 0 = up) (hr1 : X.regs 1 = ul) (hr2 : X.regs 2 = uc)
    (hr3 : X.regs 3 = vp) (hr4 : X.regs 4 = vl) (hr5 : X.regs 5 = vc)
    (hF : MemFrame s.mem X.mem (proW s)) (hreg : X.mem.regions = s.mem.regions)
    (m1 : X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (m2 : X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat)
    (s1 : X.mem.readLE (s.sp.toNat + 8) 8 = zp.toNat) (s2 : X.mem.readLE (s.sp.toNat + 16) 8 = zl.toNat)
    (s3 : X.mem.readLE (s.sp.toNat + 24) 8 = zc.toNat) (s4 : X.mem.readLE (s.sp.toNat + 32) 8 = st.toNat)
    (s5 : X.mem.readLE (s.sp.toNat + 40) 8 = z2.toNat) (s6 : X.mem.readLE (s.sp.toNat + 48) 8 = z2l.toNat)
    (s7 : X.mem.readLE (s.sp.toNat + 56) 8 = z2c.toNat) (s8 : X.mem.readLE (s.sp.toNat + 64) 8 = up.toNat)
    (s9 : X.mem.readLE (s.sp.toNat + 72) 8 = ul.toNat) (s10 : X.mem.readLE (s.sp.toNat + 80) 8 = uc.toNat)
    (s11 : X.mem.readLE (s.sp.toNat + 88) 8 = vp.toNat) (s12 : X.mem.readLE (s.sp.toNat + 96) 8 = vl.toNat)
    (s13 : X.mem.readLE (s.sp.toNat + 104) 8 = vc.toNat) (Q : State → Prop)
    (k : ∀ S, AtC zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat uc.toNat
      vp.toNat vl.toNat vc.toNat s S → ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, hga, -, -, -⟩ := hp.ce
  unfold Apart at hga
  obtain ⟨-, hvacc, hv48, -, hvw⟩ := hp.vo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hui := hp.ui
  have hspn : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have hpre' : CmpSum.Pre X := by
    unfold CmpSum.Pre GuardOK StackOK CmpSum.SliceOK
    rw [h30, h28, hr0, hr1, hr3, hr4, hspn, hrd _ _ (by omega)]
    refine ⟨by decide, by decide, ⟨hg1, by rw [hF.accessible]; exact hg2, by omega⟩,
      ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_⟩
    · rw [hF.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · by_cases h0 : ul.toNat = 0
      · exact Or.inl h0
      · obtain ⟨-, huacc, hu48, -, huw⟩ := hui.2 (by omega)
        simp only [win, outside_cons, outside_nil, and_true] at huw
        exact Or.inr ⟨by rw [hF.accessible]; exact huacc, by unfold Apart; omega⟩
    · exact Or.inr ⟨by rw [hF.accessible]; exact hvacc, by unfold Apart; omega⟩
  refine ReachesRet.call_regions (csum impl hap) hpc hpre' fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  rw [hspn] at hf
  have hslot : ∀ a, (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 112) →
      m.readLE a 8 = X.mem.readLE a 8 := fun a h =>
    hf.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hU : X.mem.readLE up.toNat (8 * ul.toNat) = s.mem.readLE up.toNat (8 * ul.toNat) := by
    by_cases h0 : ul.toNat = 0
    · simp only [h0, Nat.mul_zero, Memory.readLE_zero]
    · obtain ⟨-, -, -, -, huw⟩ := hui.2 (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at huw
      exact hrd _ _ (by omega)
  have hV : X.mem.readLE vp.toNat (8 * vl.toNat) = s.mem.readLE vp.toNat (8 * vl.toNat) := hrd _ _ (by omega)
  refine k _
    { pc := by rw [h30]
      sp := by rw [← hsp]
      r28 := by simp [setReg]; exact h28
      r29 := by simp [setReg]; exact h29
      r18 := by simp [setReg]; exact h18
      r0 := by
        simp [setReg]
        rw [hr1, hr4, hr0, hr3]
        show CmpSum.cmpRes _ _ (X.mem.readLE up.toNat (8 * ul.toNat)) (X.mem.readLE vp.toNat (8 * vl.toNat)) = _
        rw [hU, hV]
      mf := hF.trans hf fun a n h => ⟨by simp only [winA, proW, outside_cons, outside_nil, and_true] at h ⊢; omega,
        by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
      reg := by rw [hrg, hreg]
      lr := by rw [hslot _ (Or.inl ⟨by omega, by omega⟩)]; exact m1
      fp := by rw [hslot _ (Or.inl ⟨by omega, by omega⟩)]; exact m2
      s1 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s1
      s2 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s2
      s3 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s3
      s4 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s4
      s5 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s5
      s6 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s6
      s7 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s7
      s8 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s8
      s9 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s9
      s10 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s10
      s11 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s11
      s12 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s12
      s13 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s13 }


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `len u ≤ cap z2`: `r = z2[:len u]` (= `lessR` from the facts it uses) -/
theorem lessRM (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hce : CallEnv R L s 41504 112) (hinv0 : R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
    (hul : ul ≤ 2 ^ 9) (hz40 : z2c < 2 ^ 40) {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (hr0 : S.regs 0 = 18446744073709551615#64)
    (hz : ul ≤ z2c) (Q : State → Prop)
    (k : ∀ S', AtS R b L zp zc z2 z2c u ul s z2 z2c L b S' → ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := id hce
  obtain ⟨hinv1, hmf1, hlf1⟩ := winOnly hce hinv0 hS.mf
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hS.mf.accessible]; exact hw
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.s1; have m4 := hS.s3; have m5 := hS.s5; have m6 := hS.s7
  have m7 := hS.s8; have m8 := hS.s9
  have hreg := hS.reg
  have hLs := hce.2.2.2.2.2.2.1
  have hzp : zp < 2 ^ 64 := by rw [← hS.s1]; exact Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.s3]; exact Memory.readLE_lt _ _ _
  clear hS hce hinv0
  janus_run [hr0, m1, m2, m3, m4, m5, m6, m7, m8] until [joinS]
  refine k _
    { pc := rfl
      sp := ?_
      r28 := ?_
      r29 := ?_
      r18 := ?_
      r0 := ?_
      r1 := ?_
      r2 := ?_
      r6 := ?_
      arr := Or.inl ⟨rfl, rfl, hz⟩
      ext := LiveExt.refl R L
      bud := Nat.sub_le _ _
      inv := RtInv.inv_frame' (ws := [(s.sp.toNat - 56, s.sp.toNat - 32)]) (by janus_frame) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        left; exact hout.of_sub (by simp only; omega) (by simp only; omega)) hinv1
      mf := hmf1.trans (by janus_frame : MemFrame S.mem _ [(s.sp.toNat - 56, s.sp.toNat - 32)]) fun a n h => ⟨h, by
        simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
      lf := ⟨fun a n hin ho => by
        rw [(by janus_frame : MemFrame S.mem _ [(s.sp.toNat - 56, s.sp.toNat - 32)]).readLE a n ?_]
        · exact hlf1.readLE a n hin ho
        · obtain ⟨r, hr, i1, i2⟩ := hin
          have := hLs r hr
          simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega⟩
      reg := ?_
      lr := ?_
      fp := ?_
      q0 := ?_
      q1 := ?_
      q2 := ?_
      s8 := ?_ }
  all_goals try (janus_simp; done)
  all_goals (janus_simp; omega)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the postcondition of the `u < v` path with `z2 = u` (`r = u[:len u]`, nothing copied) -/
theorem lessFinM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s) {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L 0 0 u uc u ul s u uc L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (s' : State) {q ql qc : Nat}
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 1 = BitVec.ofNat 64 ql) (h2 : s'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 3 = BitVec.ofNat 64 u) (h4 : s'.regs 4 = BitVec.ofNat 64 ul) (h5 : s'.regs 5 = BitVec.ofNat 64 uc)
    (hM : MemFrame S.mem s'.mem [(s.sp.toNat - 80, s.sp.toNat - 56)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)) :
    PostM R b dc L u ul uc v vl s s' := by
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hp.ce
  have hLs1 : ∀ r ∈ L', r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ r.1 := by
    obtain ⟨ns, e, hn, -⟩ := hS.ext
    intro r hr; rw [e] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := outside_of_inRanges hout (hn r hr).1; omega
  -- `u`'s words at `s'.mem` are the entry's
  have hku : ∀ a n, u ≤ a → a + n ≤ u + 8 * ul → 0 < n → s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2 hn
    obtain ⟨-, -, -, huh, huw⟩ := hp.ui.2 (by omega)
    simp only [win, outside_cons, outside_nil, and_true] at huw
    rw [hM.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rcases huh.sub h1 h2 with hin | ho
    · exact hS.lf.readLE a n hin trivial
    · exact hS.mf.readLE a n (by
        simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨ho, by omega, by omega⟩)
  have hval : natVal s'.mem u ul = natVal s.mem u ul := by
    by_cases h0 : ul = 0
    · simp [natVal, h0]
    · exact hku _ _ (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hbud := hS.bud
  have hc := hp.cost
  have hacc : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hM.accessible, hS.mf.accessible]
  refine ⟨q, ql, qc, u, ul, uc, h0, h1, h2, h3, h4, h5, L', b', ⟨?_, ?_, hp.ulc, hp.uo.1, ?_, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨hS.ext, ?_, hinv⟩, hS.mf.trans hM fun a n h => ⟨?_, ?_⟩, ⟨fun a n hin ho => ?_⟩⟩
  · rw [hval, Nat.mod_eq_of_lt hU]
  · by_cases h0 : ul = 0
    · exact Or.inl h0
    · rcases hp.un with h | h
      · exact absurd h h0
      · exact Or.inr (by rw [hku _ _ (by omega) (by omega) (by omega)]; exact h)
  · intro hcu
    obtain ⟨a1, a2, a3, a4⟩ := hp.uo.2.1 hcu
    exact ⟨a1, hS.ext.held a2, by rw [hacc]; exact a3, a4⟩
  · simp only [costM, cost] at hc ⊢; omega
  · simp only [outside_append] at h ⊢; exact h.1
  · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  · obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs1 r (hS.ext.mem_old hr)
    rw [hM.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hS.lf.readLE a n ⟨r, hr, i1, i2⟩ trivial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u < v`, `z2 = u`: `copy(u[:len u], u)` is skipped (same pointer), `r = u[:len u]` stored, return -/
theorem lessSM (impl : List Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s) {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L 0 0 u uc u ul s u uc L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hp.ce
  unfold Apart at hga
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr6 := hS.r6
  have hacc := hS.mf.accessible
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hacc]; exact hw
  have hinvS := hS.inv
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.q0; have m4 := hS.q1; have m5 := hS.q2; have m6 := hS.s8
  have hB : Box (PFM R b dc L u ul uc v vl s ∧ AtS R b L 0 0 u uc u ul s u uc L' b' S) := ⟨⟨hp, hS⟩⟩
  have hpu' : (BitVec.ofNat 64 u = BitVec.ofNat 64 u) = True := eq_self _
  clear hp hS
  janus_run [m1, m2, m3, m4, m5, m6, hpu']
  obtain ⟨hp, hS⟩ := hB.h
  have hW2 : MemFrame S.mem (((S.mem.writeLE (s.sp.toNat - 80) 8 u).writeLE (s.sp.toNat - 72) 8 ul).writeLE
      (s.sp.toNat - 64) 8 uc) [(s.sp.toNat - 80, s.sp.toNat - 56)] := by janus_frame
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lessFinM (q := 0) (ql := 0) (qc := 0) hp hS hU _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hI⟩
  case hM => first | exact hW2 | janus_frame
  case hI =>
    refine RtInv.inv_frame' hW2 (fun r hr => ?_) hinvS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  all_goals janus_simp
  all_goals exact ofNat_modL _

end FvModexp.Arm64.NatDiv
