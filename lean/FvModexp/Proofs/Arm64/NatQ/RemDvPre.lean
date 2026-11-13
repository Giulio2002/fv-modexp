import FvModexp.Proofs.Arm64.NatQ.RemSN

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/RemDvPre.lean, TIGHT COSTS, asm s38)
# `nat.rem` (arm64): `div`'s precondition at `CALL nat.div` (pure)

`q = (tq, k, k)` with `tq = stW M + 8·len` (the scratch from `stk.nat(k)`), `z2 := z`, `u`, `v`, stack `st` (now of
length `len + rnd k`), live set `L1`, budget `b1` (`SN`). The region `F = [tq, stW M + 8·cap M)` (`q` and the new free
part) is the old free part (stack kept) or inside the fresh array (in `R.rt`, apart from `L`): `SN.regH` / `SN.regO`
give its apartness from every held range apart from the old free part, and from the window / guard word / `gA`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.NatRem
open FvModexp.Arm64.NatRem
variable {H : Nat}

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

theorem rnd_ge (k : Nat) : k ≤ StackNat.rnd k ∧ StackNat.rnd k ≤ k + 3 := by
  simp only [StackNat.rnd]; omega

theorem kq_pos (ul vl : Nat) : 0 < kq ul vl := by simp only [kq]; omega

theorem kq_le (ul vl : Nat) : kq ul vl ≤ ul + 1 := by simp only [kq]; omega

set_option maxRecDepth 100000 in
/-- `div`'s window bounds in terms of `rem`'s (omega is very slow on `x - 41504` with `x = y - 208`: rewrite first) -/
theorem spW {X s : State} (hspn : X.sp.toNat = s.sp.toNat - 208) (hb : 41712 ≤ s.sp.toNat) :
    X.sp.toNat - 41504 = s.sp.toNat - 41712 ∧ X.sp.toNat - 8 = s.sp.toNat - 216 ∧
      X.sp.toNat + 8 = s.sp.toNat - 200 ∧ X.sp.toNat + 112 = s.sp.toNat - 96 := by
  omega

set_option maxRecDepth 20000 in
theorem winX {X s : State} (hspn : X.sp.toNat = s.sp.toNat - 208) (hb : 41712 ≤ s.sp.toNat) {a n : Nat}
    (h : Outside a n (win s 41712 112)) : Outside a n (win X 41504 112) := by
  obtain ⟨e1, -, -, e4⟩ := spW hspn hb
  simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [e1, e4]; omega

set_option maxRecDepth 20000 in
theorem sp208 {X s : State} (h : X.sp = s.sp - 208#64) (hb : 41712 ≤ s.sp.toNat) : X.sp.toNat = s.sp.toNat - 208 := by
  rw [h, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl

/-- a held range apart from the old free part is apart from the region `F` -/
theorem SN.regH {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st k : Nat} {s : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hN : SN R b H L st k s M L1 b1) {a n : Nat} (hH : Held R L a n)
    (hA : Apart a n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) :
    Apart a n (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) := by
  have hlc := hN.sok.2.2.2.2.2.1
  have hl := hN.len
  by_cases hg : stLen s.mem st + StackNat.rnd k ≤ stCap s.mem st
  · rw [(hN.kept hg).1, (hN.kept hg).2]; exact hA
  · obtain ⟨hin, hap⟩ := hN.fresh (by omega)
    have h2 : Apart a n (stW M st) (8 * stCap M st) := by
      rcases hH with h | h
      · obtain ⟨r, hr, h1, h2⟩ := h
        have := hap r hr; unfold Apart at this ⊢; omega
      · exact InRanges.apart hin h
    unfold Apart at h2 ⊢; omega

/-- the region `F` is outside the window and apart from the guard word and `gA` -/
theorem SN.regO {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl : Nat} {s : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b H cd L zp zl zc st up ul uc vp vl s) (hN : SN R b H L st (kq ul vl) s M L1 b1) :
    Outside (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) (win s 41712 112) ∧
      Apart (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) ((s.regs 28).toNat + 16) 8 ∧
      Apart (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) RunIface.gA 32 := by
  obtain ⟨⟨⟨hce, -, hgl, -, -, -, -, -, -, -, -, harr, -, -, -, -, -, -, -, hfg, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, -, -, hout, -, hgr, -, -⟩ := hce
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, -, -, -, -⟩ := hgl
  have hlc := hN.sok.2.2.2.2.2.1
  have hl := hN.len
  have hr := rnd_ge (kq ul vl)
  have hk := kq_pos ul vl
  by_cases hg : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap s.mem st
  · rw [(hN.kept hg).1, (hN.kept hg).2]
    obtain ⟨h1, h2⟩ := harr (by omega)
    simp only [win, outside_cons, outside_nil, and_true] at h1 ⊢
    refine ⟨by omega, by unfold Apart at h2 ⊢; omega, hfg⟩
  · obtain ⟨hin, -⟩ := hN.fresh (by omega)
    have a1 := InRanges.apart hin hout
    have a2 := InRanges.apart hin hgr
    have a3 := InRanges.apart hin hgArt
    unfold Apart at a1 a2 a3
    simp only [win, outside_cons, outside_nil, and_true]
    unfold Apart
    omega

/-- the scratch `q` and the new free part lie in the region `F` (`len' = len + rnd k ≤ cap'`), `q` before the free part -/
theorem sub_F {ln lM C k W a n : Nat} (hl : lM = ln + StackNat.rnd k) (hlc : lM ≤ C)
    (h : Apart a n (W + 8 * ln) (8 * (C - ln))) :
    Apart a n (W + 8 * ln) (8 * k) ∧ Apart a n (W + 8 * lM) (8 * (C - lM)) := by
  have := rnd_ge k
  unfold Apart at h ⊢; omega

theorem sub_F' {ln lM C k W a n : Nat} (hl : lM = ln + StackNat.rnd k) (hlc : lM ≤ C)
    (h : Apart (W + 8 * ln) (8 * (C - ln)) a n) :
    Apart (W + 8 * ln) (8 * k) a n ∧ Apart (W + 8 * lM) (8 * (C - lM)) a n := by
  have := rnd_ge k
  unfold Apart at h ⊢; omega

theorem q_free {ln lM C k W : Nat} (hl : lM = ln + StackNat.rnd k) :
    Apart (W + 8 * ln) (8 * k) (W + 8 * lM) (8 * (C - lM)) := by
  have := rnd_ge k
  unfold Apart; omega

theorem len_ok {ln ul k : Nat} (hneed : ln + need ul 0 ≤ 2 ^ 16) (hk1 : k ≤ ul + 1) :
    ln + StackNat.rnd k + 16 * ul + 64 ≤ 2 ^ 16 := by
  have := rnd_ge k; simp only [need] at hneed; omega

theorem lenH_ok {ln ul k H : Nat} (hneed : ln + need ul 0 ≤ H) (hk1 : k ≤ ul + 1) :
    ln + StackNat.rnd k + 16 * ul + 64 ≤ H := by
  have := rnd_ge k; simp only [need] at hneed; omega

theorem cost_ok {b b1 c R0 R1 : Nat} (hc : c + R0 ≤ b) (hb : b - R0 + R1 ≤ b1) : c + R1 ≤ b1 := by omega

/-- the threshold globals and the write-barrier flag survive a frame they are outside of (local copy of asm's
`NatDiv.globals_win`, Arm64/Nat/DivBigP.lean) -/
theorem globals_win {R : RtInv} {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' ws) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (hg.of_sub (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

/-- a range apart from the header and the old free part is outside `stkWs` -/
theorem out_stkWs {m : Memory} {st a n : Nat} (hlc : stLen m st ≤ stCap m st) (h1 : Apart a n st 24)
    (h2 : Apart a n (stW m st + 8 * stLen m st) (8 * (stCap m st - stLen m st))) : Outside a n (stkWs m st) := by
  simp only [stkWs, outside_cons, outside_nil, and_true]; unfold Apart at h1 h2; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`div`'s precondition** at the call state `X` (`SP = entry SP - 208`, memory `M` after `stk.nat`) -/
theorem dv_pre {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl : Nat} {s : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b H cd L zp zl zc st up ul uc vp vl s) (hN : SN R b H L st (kq ul vl) s M L1 b1)
    (X : State) (hsp : X.sp = s.sp - 208#64) (h28 : X.regs 28 = s.regs 28) (hm : X.mem = M) :
    ExpHyp.DivPreQ R b1 H (cd ul vl + stkR H X.mem st) L1 41504 112 (stW M st + 8 * stLen s.mem st) (kq ul vl)
      (kq ul vl) st zp zl zc up ul vp vl X := by
  have hO := hN.regO hpre
  subst hm
  obtain ⟨⟨⟨hce, hsv, hgl, -, -, hzlc, hzo, hins, hsok0, hsw, hsg, harr, hc0, hneed, -, hwbs, hfree, hzst, hsgA,
    hfgA, hcst, -⟩, hvl0⟩, -, hst0, hlv⟩ := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  have hspn : X.sp.toNat = s.sp.toNat - 208 := sp208 hsp hb'
  obtain ⟨hW1, -, -, hW4⟩ := spW hspn hb'
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := hN.mf.accessible
  have hwinX : ∀ a n, Outside a n (win s 41712 112) → Outside a n (win X 41504 112) := fun a n h =>
    winX hspn hb' h
  obtain ⟨-, hsth, hstacc, -, hnl0, hlc0, -⟩ := hsok0
  have hMF : MemFrame s.mem X.mem (R.rt ++ (winA s 41712 112 ++ stkWs s.mem st)) := by
    simpa only [List.append_assoc] using hN.mf
  have hLF : LiveFrame s.mem X.mem L (winA s 41712 112 ++ stkWs s.mem st) :=
    ⟨fun a n hin ho => hN.lf.readLE a n hin (by rw [outside_append] at ho; exact ho.2)⟩
  have hrdH : ∀ a n, Held R L a n → Outside a n (win s 41712 112) → Outside a n (stkWs s.mem st) →
      X.mem.readLE a n = s.mem.readLE a n := fun a n hh h1 h2 => hh.readLE hMF hLF (by
    rw [outside_append]; refine ⟨?_, h2⟩
    simp only [win, winA, outside_cons, outside_nil, and_true] at h1 ⊢; omega)
  obtain ⟨⟨hu40, huacc, hu48, huh, huw⟩, hu9, hun, hust, hufr, hzu⟩ := hins up ul (by simp)
  obtain ⟨⟨hv40, hvacc, hv48, hvh, hvw⟩, hv9, hvn, hvst, hvfr, hzv⟩ := hins vp vl (by simp)
  clear hins
  have hsok := hN.sok
  obtain ⟨-, -, -, -, hnl, hlc, -⟩ := hsok
  have hl := hN.len
  have hr := rnd_ge (kq ul vl)
  have hk := kq_pos ul vl
  have hk1 := kq_le ul vl
  have hC : 0 < stCap X.mem st := by omega
  have hlc' : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap X.mem st := hl ▸ hlc
  obtain ⟨hw8, hwh, hwacc, hw48⟩ := hnl hC
  -- the guard word is outside the frame
  have hgO : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ (winA s 41712 112 ++ stkWs s.mem st)) := by
    rw [outside_append, outside_append]
    refine ⟨hgr, by simp only [winA, outside_cons, outside_nil, and_true]; unfold Apart at hga; omega,
      out_stkWs hlc0 hsg.symm ?_⟩
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with hc | hc
    · rw [hc0 hc, hc]; unfold Apart; omega
    · have := (harr hc).2; unfold Apart at this ⊢; omega
  unfold ExpHyp.DivPreQ
  rw [hl]
  refine ⟨?ce, hsv, ?gl, Nat.le_refl _, hzlc, ?qo, ?zo, ?ui, ?vi, hu9, hvl0, hv9, ?un, ?vn, hN.sok, ?stw, ?sarr,
    ?len, ?c0, hust, ?uF, hvst, ?vF, by omega, ⟨by rw [h28]; exact hsg, hwbs, ?stF⟩, ?qg, fun hc => (hzst hc).2.2,
    hsgA, ?fgA, ?qz, ?pw, ?cost, by rw [h28]; exact hN.inv⟩
  case ce =>
    refine ⟨⟨by rw [h28]; exact hg1, by rw [h28, hacc]; exact hg2, ?_⟩, ⟨by rw [hspn]; omega, by rw [hspn]; omega,
      by rw [hspn]; omega, by rw [hacc, hW1]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩, ?_,
      by rw [hW1]; exact hout.of_sub (by omega) (by omega), by rw [h28, hW1]; unfold Apart at hga ⊢; omega,
      by rw [h28]; exact hgr, ?_, hro⟩
    · rw [h28, hMF.readLE _ _ hgO, hspn]; omega
    · refine dataLoaded_frame (rt := R.rt) (ws := winA s 41712 112 ++ stkWs s.mem st) hdl hN.reg hro hMF ?_
      intro r hr hlt
      simp only [winA, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
      · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
      · simpa using hstacc
      · simp only at hlt ⊢
        obtain ⟨-, -, harr0, -⟩ := hnl0 (by omega)
        exact Memory.accessible_mono _ harr0 (by omega) (by omega)
    · refine hN.ext.liveSep (fun r hr => ?_) (fun r hr => ?_)
      · have := hLs r hr
        simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hW1, hW4]; omega
      · simp only [win, List.mem_singleton] at hr; subst hr; simp only
        rw [hW1, hW4]; exact hout.of_sub (by omega) (by omega)
  case gl =>
    refine globals_win hgl hN.mf ?_ hwinX
    obtain ⟨-, -, -, -, -, -, -, -, hgArt, hgAw, -, -, -⟩ := hgl
    rw [outside_append, outside_append]
    refine ⟨⟨hgArt, ?_⟩, out_stkWs hlc0 hsgA.symm hfgA.symm⟩
    simp only [win, winA, outside_cons, outside_nil, and_true] at hgAw ⊢; omega
  case qo =>
    refine ⟨by omega, fun _ => ⟨by omega, hwh.sub (by omega) (by omega),
      Memory.accessible_mono _ hwacc (by omega) (by omega), by omega⟩, fun _ => ⟨?_, ?_⟩⟩
    · exact hwinX _ _ (hO.1.of_sub (by omega) (by omega))
    · rw [h28]; exact (sub_F' rfl hlc' hO.2.1).1
  case zo =>
    obtain ⟨h1, h2, h3⟩ := hzo
    refine ⟨h1, fun hc => ?_, fun hc => ⟨hwinX _ _ (h3 hc).1, by rw [h28]; exact (h3 hc).2⟩⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 hc; exact ⟨a1, hN.ext.held a2, by rw [hacc]; exact a3, a4⟩
  case ui => exact ⟨hu40, by rw [hacc]; exact huacc, hu48, hN.ext.held huh, hwinX _ _ huw⟩
  case vi => exact ⟨hv40, by rw [hacc]; exact hvacc, hv48, hN.ext.held hvh, hwinX _ _ hvw⟩
  case un =>
    rcases hun with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos ul with h0 | h0
      · exact Or.inl h0
      refine Or.inr ?_
      have ho := out_stkWs hlc0 hust hufr
      rw [hrdH _ _ (huh.sub (by omega) (by omega)) (huw.of_sub (by omega) (by omega))
        (ho.of_sub (by omega) (by omega))]; exact h
  case vn =>
    rcases hvn with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos vl with h0 | h0
      · exact Or.inl h0
      refine Or.inr ?_
      have ho := out_stkWs hlc0 hvst hvfr
      rw [hrdH _ _ (hvh.sub (by omega) (by omega)) (hvw.of_sub (by omega) (by omega))
        (ho.of_sub (by omega) (by omega))]; exact h
  case stw => exact hwinX _ _ hsw
  case sarr =>
    intro _
    refine ⟨?_, ?_⟩
    · have := hO.1
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢
      rw [hW1, hW4]
      rcases Nat.lt_or_ge (stCap X.mem st) (stLen s.mem st + StackNat.rnd (kq ul vl)) with h | h
      · omega
      · by_cases hg : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap s.mem st
        · rw [(hN.kept hg).1, (hN.kept hg).2]
          have := (harr (by omega)).1
          simp only [win, outside_cons, outside_nil, and_true] at this; omega
        · obtain ⟨hin, -⟩ := hN.fresh (by omega)
          have := InRanges.apart hin hout; unfold Apart at this; omega
    · rw [h28]
      by_cases hg : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap s.mem st
      · rw [(hN.kept hg).1, (hN.kept hg).2]; exact (harr (by omega)).2
      · obtain ⟨hin, -⟩ := hN.fresh (by omega)
        exact (InRanges.apart hin hgr).symm
  case len => exact len_ok hneed hk1
  case c0 => exact fun h => absurd h (Nat.pos_iff_ne_zero.mp hC)
  case uF => exact (sub_F rfl hlc' (hN.regH huh hufr)).2
  case vF => exact (sub_F rfl hlc' (hN.regH hvh hvfr)).2
  case stF => exact (sub_F rfl hlc' (hN.regH hsth hfree)).2
  case qg => exact fun _ => (sub_F' rfl hlc' hO.2.2).1
  case fgA => exact (sub_F' rfl hlc' hO.2.2).2
  case qz =>
    intro _ hc
    exact (sub_F rfl hlc' (hN.regH ((hzo.2.1 hc).2.1) (hzst hc).2.1)).1.symm
  case pw =>
    intro p c hpc hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hpc
    rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(sub_F rfl hlc' (hN.regH huh hufr)).1.symm, (sub_F rfl hlc' (hN.regH hvh hvfr)).1.symm,
        (sub_F rfl hlc' (hN.regH hsth hfree)).1.symm, q_free rfl⟩
    · exact ⟨hzu hc, hzv hc, (hzst hc).1, (sub_F rfl hlc' (hN.regH ((hzo.2.1 hc).2.1) (hzst hc).2.1)).2⟩
  case cost =>
    refine ⟨by exact lenH_ok (by simp only [need] at hlv ⊢; omega) (by simp only [kq]; omega), ?_⟩
    exact cost_ok hcst hN.bud

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the operands keep their values through `stk.nat` -/
theorem uv_val {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl : Nat} {s : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b H cd L zp zl zc st up ul uc vp vl s) (hN : SN R b H L st (kq ul vl) s M L1 b1) :
    natVal M up ul = natVal s.mem up ul ∧ natVal M vp vl = natVal s.mem vp vl := by
  obtain ⟨⟨⟨-, -, -, -, -, -, -, hins, hsok0, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, -, -, -, -, hlc0, -⟩ := hsok0
  have hMF : MemFrame s.mem M (R.rt ++ (winA s 41712 112 ++ stkWs s.mem st)) := by
    simpa only [List.append_assoc] using hN.mf
  have hLF : LiveFrame s.mem M L (winA s 41712 112 ++ stkWs s.mem st) :=
    ⟨fun a n hin ho => hN.lf.readLE a n hin (by rw [outside_append] at ho; exact ho.2)⟩
  have key : ∀ p n, (p, n) ∈ [(up, ul), (vp, vl)] → natVal M p n = natVal s.mem p n := by
    intro p n hp
    obtain ⟨⟨-, -, -, hh, hw⟩, -, -, hst, hfr, -⟩ := hins p n hp
    refine hh.readLE hMF hLF ?_
    rw [outside_append]; refine ⟨?_, out_stkWs hlc0 hst hfr⟩
    simp only [win, winA, outside_cons, outside_nil, and_true] at hw ⊢; omega
  exact ⟨key _ _ (by simp), key _ _ (by simp)⟩

end FvModexp.Arm64.Q.NatRem
