import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivRel

/-!
# `nat.div` (arm64), `u < v` (`len v ≥ 2`): `q = z[:0]`, `r = z2.make(len u)` (reuse or `makeslice`) → `AtS`
(natdiv.go:532-534, nat.go:58-68)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

/-- window-only frames keep the invariant and the live objects -/
theorem winOnly {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} (hce : CallEnv R L s 41504 112)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) {M : Memory} (hF : MemFrame s.mem M (winA s 41504 112)) :
    R.inv b L (s.regs 28).toNat (view R.rt L M) ∧ MemFrame s.mem M (R.rt ++ winA s 41504 112) ∧
      LiveFrame s.mem M L [] := by
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  refine ⟨inv_frame_winA hF hout hb' (by omega) hinv, hF.mono fun a n h => by
    simp only [outside_append] at h; exact h.2, ⟨fun a n hin _ => hF.readLE a n ?_⟩⟩
  obtain ⟨r, hr, i1, i2⟩ := hin
  have := hLs r hr
  simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `len u ≤ cap z2`: `r = z2[:len u]` -/
theorem lessR (impl : List Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (hr0 : S.regs 0 = 18446744073709551615#64)
    (hz : ul ≤ z2c) (Q : State → Prop)
    (k : ∀ S', AtS R b L zp zc z2 z2c u ul s z2 z2c L b S' → ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hp.ce
  have hinv0 := hp.inv
  have hul := hp.ul9
  have hz40 := hp.z2o.1
  obtain ⟨hinv1, hmf1, hlf1⟩ := winOnly hce hinv0 hS.mf
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hS.mf.accessible]; exact hw
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.s1; have m4 := hS.s3; have m5 := hS.s5; have m6 := hS.s7
  have m7 := hS.s8; have m8 := hS.s9
  have hreg := hS.reg
  have hLs := hce.2.2.2.2.2.2.1
  have hzp : zp < 2 ^ 64 := by rw [← hS.s1]; exact Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.s3]; exact Memory.readLE_lt _ _ _
  clear hpre hp hS hce hinv0
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
set_option maxHeartbeats 64000000 in
/-- `cap z2 < len u`: `makeslice(Word, len u, makeCap (len u))` → `AtS` (`ul = 1`: `(1, 1)`, else `(ul, ul + 4)`) -/
theorem lessA (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (hr0 : S.regs 0 = 18446744073709551615#64)
    (hz : z2c < ul) (Q : State → Prop)
    (k : ∀ S' p c L' b', AtS R b L zp zc z2 z2c u ul s p c L' b' S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := hp.ce
  unfold Apart at hga
  have hinv0 := hp.inv
  have hul := hp.ul9
  have hz40 := hp.z2o.1
  have hsv := hp.sv
  have hcost := hp.cost
  obtain ⟨hinv1, hmf1, hlf1⟩ := winOnly hce hinv0 hS.mf
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hacc := hS.mf.accessible
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hS.mf.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 41504) (41504 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt
  have hWr : ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → S.mem.readLE a n = s.mem.readLE a n := fun a n h1 h2 =>
    hS.mf.readLE a n (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hmc : makeCost ul ≤ b := by simp only [cost] at hcost; omega
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, ul, makeCap ul] := hsv.1 _ _ _ (by unfold makeCap; split <;> omega)
  have hbl := blockSize_le_allocCost (8 * makeCap ul) true
  have hbs : blockSize (8 * makeCap ul) true ≤ b := by unfold makeCost at hmc; omega
  have hLs1 : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ r.1 := fun r hr => by
    have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.s1; have m4 := hS.s3; have m5 := hS.s5; have m6 := hS.s7
  have m7 := hS.s8; have m8 := hS.s9
  have hreg := hS.reg
  have hzp : zp < 2 ^ 64 := by rw [← hS.s1]; exact Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.s3]; exact Memory.readLE_lt _ _ _
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : S.mem.readLE 2641088 8 = s.mem.readLE 2641088 8 := hWr _ _ (by omega) (by omega)
  have hT2 : S.mem.readLE 2641096 8 = s.mem.readLE 2641096 8 := hWr _ _ (by omega) (by omega)
  have hTa : S.mem.accessible 2641088 16 false = s.mem.accessible 2641088 16 false := hacc _ _ _
  clear hpre hp hS hce hinv0 hWr
  by_cases h1 : ul = 1
  · subst h1
    have hc1 : makeCap 1 = 1 := rfl
    rw [hc1] at hok1 hbs hbl
    set_option janus.callRegions true in
    janus_run [hr0, m1, m2, m3, m4, m5, m6, m7, m8, hT1, hT2, hTa, hgS] until [joinS] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc' h8 _ _ _ hrb hinv' hapw _
    have hpo := FvModexp.Arm64.NatAdd.outside_of_inRanges hout hIn
    have hmo : ∀ a n, (s.sp.toNat - 248 ≤ a ∧ a + n ≤ s.sp.toNat - 232) ∨ (s.sp.toNat - 56 ≤ a ∧ a + n ≤ s.sp.toNat - 32) ∨
        (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 112) → Outside a n (R.rt ++ [(s.sp.toNat - 240 - 4096, s.sp.toNat - 240 - 8),
          (s.sp.toNat - 240 + 8, s.sp.toNat - 240 + 8 + 24)]) := fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    refine k _ ptr.toNat 1 (L ++ [(ptr.toNat, ptr.toNat + 8)]) (b - 8)
      { pc := rfl
        sp := ?_
        r28 := ?_
        r29 := ?_
        r18 := ?_
        r0 := ?_
        r1 := ?_
        r2 := ?_
        r6 := ?_
        arr := Or.inr ⟨hz, Nat.le_refl _, by omega, h8, by omega, by simpa using hIn, by simpa using hAp,
          ⟨(ptr.toNat, ptr.toNat + 8), by simp, by simp only; omega, by simp only; omega⟩, ?acc⟩
        ext := LiveExt.single (by simpa using hIn) (by simpa using hAp)
        bud := by have : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
                  omega
        inv := by simpa using hinv'
        mf := hmf1.trans ((by janus_frame : MemFrame S.mem _ [(s.sp.toNat - 56, s.sp.toNat - 32)]).trans hMF
          (rs'' := R.rt ++ winA s 41504 112) fun a n h => ?mf2) fun a n h => ⟨h, h⟩
        lf := ⟨fun a n hin ho => ?lf⟩
        reg := ?_
        lr := ?_
        fp := ?_
        q0 := ?_
        q1 := ?_
        q2 := ?_
        s8 := ?_ }
    case acc =>
      rw [hMF.accessible]; simp only [Memory.accessible_writeLE]; rw [hacc]; exact hacc'
    case mf2 =>
      simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨by omega, h.1, by omega, by omega⟩
    case lf =>
      obtain ⟨r, hr, i1, i2⟩ := hin
      have := hLs1 r hr
      rw [hLF.readLE a n ⟨r, hr, i1, i2⟩ trivial,
        (by janus_frame : MemFrame S.mem _ [(s.sp.toNat - 56, s.sp.toNat - 32)]).readLE a n
          (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hlf1.readLE a n ⟨r, hr, i1, i2⟩ ho
    all_goals try (janus_simp; done)
    all_goals try (simp only at hrg1 ⊢; rw [hrg1]; exact hreg)
    all_goals try (rw [hMF.readLE _ _ (hmo _ _ (by omega))]
                   simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
                     m1, m2, m7]
                   done)
  · have hcN : makeCap ul = ul + 4 := by unfold makeCap; rw [if_neg h1]
    rw [hcN] at hok1 hbs hbl
    have h1' : (BitVec.ofNat 64 ul = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    set_option janus.callRegions true in
    janus_run [hr0, m1, m2, m3, m4, m5, m6, m7, m8, hT1, hT2, hTa, hgS, h1'] until [joinS] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc' h8 _ _ hsz hrb hinv' hapw _
    have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
    have hmc' : makeCost ul = allocCost (8 * (ul + 4)) := by unfold makeCost; rw [hcN]
    have hbl' := blockSize_le_allocCost (8 * (ul + 4)) true
    have hmo : ∀ a n, (s.sp.toNat - 248 ≤ a ∧ a + n ≤ s.sp.toNat - 232) ∨ (s.sp.toNat - 120 ≤ a ∧ a + n ≤ s.sp.toNat - 32) ∨
        (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 112) → Outside a n (R.rt ++ [(s.sp.toNat - 240 - 4096, s.sp.toNat - 240 - 8),
          (s.sp.toNat - 240 + 8, s.sp.toNat - 240 + 8 + 24)]) := fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    refine k _ ptr.toNat (ul + 4) (L ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (ul + 4)) true)])
      (b - blockSize (8 * (ul + 4)) true)
      { pc := rfl
        sp := ?_
        r28 := ?_
        r29 := ?_
        r18 := ?_
        r0 := ?_
        r1 := ?_
        r2 := ?_
        r6 := ?_
        arr := Or.inr ⟨hz, by omega, Nat.le_refl _, h8', by omega, hIn.sub (Nat.le_refl _) (by omega),
          fun r hr => (hAp r hr).mono hsz (Nat.le_refl _),
          ⟨(ptr.toNat, ptr.toNat + blockSize (8 * (ul + 4)) true), by simp, by simp only; omega, by simp only; omega⟩,
          ?acc⟩
        ext := LiveExt.single (by simpa using hIn) (by simpa using hAp)
        bud := by omega
        inv := hinv'
        mf := hmf1.trans ((by janus_frame : MemFrame S.mem _ [(s.sp.toNat - 120, s.sp.toNat - 32)]).trans hMF
          (rs'' := R.rt ++ winA s 41504 112) fun a n h => ?mf2) fun a n h => ⟨h, h⟩
        lf := ⟨fun a n hin ho => ?lf⟩
        reg := ?_
        lr := ?_
        fp := ?_
        q0 := ?_
        q1 := ?_
        q2 := ?_
        s8 := ?_ }
    case acc =>
      rw [hMF.accessible]; simp only [Memory.accessible_writeLE]; rw [hacc]
      exact Memory.accessible_mono _ hacc' (Nat.le_refl _) (by omega)
    case mf2 =>
      simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨by omega, h.1, by omega, by omega⟩
    case lf =>
      obtain ⟨r, hr, i1, i2⟩ := hin
      have := hLs1 r hr
      rw [hLF.readLE a n ⟨r, hr, i1, i2⟩ trivial,
        (by janus_frame : MemFrame S.mem _ [(s.sp.toNat - 120, s.sp.toNat - 32)]).readLE a n
          (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hlf1.readLE a n ⟨r, hr, i1, i2⟩ ho
    all_goals try (janus_simp; done)
    all_goals try (simp only at hrg1 ⊢; rw [hrg1]; exact hreg)
    all_goals try (rw [hMF.readLE _ _ (hmo _ _ (by omega))]
                   simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
                     m1, m2, m7]
                   done)

end FvModexp.Arm64.NatDiv
