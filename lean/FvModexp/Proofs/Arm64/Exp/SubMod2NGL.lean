import FvModexp.Proofs.Arm64.Exp.SubMod2NG

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: runtime-fact and call-precondition lemmas over `PreG` (agent infra)

`PreG` keeps `Pre`'s conjunct positions, so `rtG_stack` / `rtG_stk` / `dlG_of` are `Pre`'s proofs; the rest take the
facts of the destination array (`z`'s own or the current fresh one) explicitly, and the budget relative to a base `bb`
(`b`, or `b - g · gA n` after `g` growths of the `append` loop).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
theorem rtG_stack {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {M : Memory} (k : Nat) (hF : MemFrame s.mem M (winA s K A))
    (hreg : M.regions = s.mem.regions) : Rt R b L s zp zc n k M L b := by
  obtain ⟨⟨-, ⟨-, -, -, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzl, -, -, -, -, -, -, -, -, -,
    -, hinv, -⟩ := hpre
  refine ⟨hreg, hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    Expmc.liveFrame_of_frame hF fun a k hin _ => inRanges_outside_win hLs hin, LiveExt.refl R L, Nat.sub_le _ _,
    Expmc.inv_frame hF (fun r hr => Or.inr ?_) ?_, fun hc => ?_⟩
  · simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only [K]; omega) (by simp only [K, A]; omega)
  · exact hinv
  · obtain ⟨h1, h2, h3, h4⟩ := hzl hc
    exact ⟨h1, h2, by rw [hF.accessible]; exact h3, h4⟩

set_option maxRecDepth 20000 in
theorem rtG_stk {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M M' : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (h : Rt R bb L s zp zc n k M L1 b1) (hF : MemFrame M M' (winA s K A)) (hreg : M'.regions = M.regions) :
    Rt R bb L s zp zc n k M' L1 b1 := by
  obtain ⟨⟨-, ⟨-, -, -, -⟩, -, hout, -, -, hLs, -⟩, -⟩ := hpre
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  have hwr : ∀ r ∈ winA s K A, Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only [K]; omega) (by simp only [K, A]; omega)
  have hLs1 := LiveExt.liveSep a4 hLs (fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    simp only [K, A] at hout ⊢; exact hout.of_sub (by omega) (by omega))
  refine ⟨hreg.trans a1, a2.trans hF fun x m hx => ?_, a3.trans (Expmc.liveFrame_of_frame hF fun x m hin _ => ?_)
    fun x m h => a4.inRanges_old h, a4, a5, Expmc.inv_frame hF (fun r hr => Or.inr (hwr r hr)) a6, fun hc => ?_⟩
  · refine ⟨hx, ?_⟩; simp only [outside_append] at hx; exact hx.1.2
  · exact inRanges_outside_win hLs1 hin
  · obtain ⟨c1, c2, c3, c4⟩ := a7 hc
    exact ⟨c1, c2, by rw [hF.accessible]; exact c3, c4⟩

set_option maxRecDepth 20000 in
theorem cenvG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R bb L s zp zc n k M L1 b1) (hd : Extracted.program.DataLoaded M) :
    CallW.CEnv R L1 (s.regs 28).toNat (s.sp.toNat - 144) 4464 88 M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, hro⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hzg, -⟩ := hpre
  obtain ⟨hreg, hF, -, hLE, -⟩ := hrt
  simp only [K, A] at *
  have hgv : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hF.readLE _ _ ?_
    simp only [winA, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hga hzg
    exact ⟨⟨hgr, by omega, by omega⟩, by omega⟩
  refine ⟨by omega, by omega, by omega, ?_, hg1, by rw [hF.accessible]; exact hg2, by rw [hgv]; omega,
    hout.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgr, ?_, hd, hro⟩
  · rw [hF.accessible]; exact Memory.accessible_sub _ hw (Or.inr rfl) (by omega) (by omega)
  · refine LiveExt.liveSep hLE (liveSep_sub (lo := s.sp.toNat - 4608) (hi := s.sp.toNat + 88) ?_ (by omega) (by omega))
      (fun r hr => ?_)
    · exact hLs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only
      exact hout.of_sub (by omega) (by omega)

theorem dlG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R bb L s zp zc n k M L1 b1) : Extracted.program.DataLoaded M := by
  obtain ⟨⟨⟨-, -, -⟩, ⟨-, -, -, hw⟩, hd, -, -, -, -, hro⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzl, -⟩ := hpre
  obtain ⟨hreg, hF, -⟩ := hrt
  refine dataLoaded_frame hd hreg hro (by simpa only [List.append_assoc] using hF) fun r hr hlt => ?_
  simp only [winA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Memory.accessible_sub _ hw (Or.inr rfl) (by simp only at hlt ⊢; omega) (by simp only at hlt ⊢; omega)
  · exact Memory.accessible_sub _ hw (Or.inr rfl) (by simp only at hlt ⊢; omega) (by simp only at hlt ⊢; omega)
  · simp only at hlt ⊢
    have := (hzl (by omega)).2.2.1
    rwa [show zp + 8 * zc - zp = 8 * zc by omega]

/-! ## Fresh arrays and the frame -/

/-- a runtime range is outside the function's whole window -/
theorem fresh_win {R : RtInv} {s : State} {p k : Nat} (hout : Outside (s.sp.toNat - 4608) (4608 + 88) R.rt)
    (hin : InRanges p k R.rt) : p + k ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p := by
  have := hin.apart hout; unfold Apart at this; omega

/-- a fresh range apart from the entry live set is outside every range of it -/
theorem fresh_live {L : List (Nat × Nat)} {p k a m : Nat} (hAp : ApartAll p k L) (hin : InRanges a m L) :
    a + m ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := hAp r hr; unfold Apart at this; omega

/-- after a callee at `SP - 144` that writes its window and the range `zr`: `z`'s array, an empty range, or a fresh
runtime array apart from the entry live set (the current array of the `x < y` tail) -/
theorem rt_callG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M0 M1 : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 c stk above : Nat} {zr : Nat × Nat}
    (hrt : Rt R b L s zp zc n k M0 L1 b1) (hal : 4608 ≤ s.sp.toNat) (hk : stk ≤ 4464) (ha : above ≤ 136)
    (hzr : zr = (zp, zp + 8 * zc) ∨ zr.2 = 0 ∨
      (zr.1 ≤ zr.2 ∧ InRanges zr.1 (zr.2 - zr.1) R.rt ∧ ApartAll zr.1 (zr.2 - zr.1) L))
    (hreg : M1.regions = M0.regions)
    (hF : MemFrame M0 M1 (R.rt ++ [(s.sp.toNat - 144 - stk, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + above)] ++ [zr]))
    (hLF : LiveFrame M0 M1 L1 [zr]) (hLE : LiveExt R L1 L2) (hb : b1 - c ≤ b2) (hc : c ≤ wCost n)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M1)) (hlive : NatLive M1 R L2 zp zc) :
    Rt R b L s zp zc n (k + 1) M1 L2 b2 := by
  rcases hzr with h | h
  · exact rt_call hrt hal hk ha (Or.inl h) hreg hF hLF hLE hb hc hinv hlive
  rcases h with h | ⟨hle, hin, hAp⟩
  · exact rt_call hrt hal hk ha (Or.inr h) hreg hF hLF hLE hb hc hinv hlive
  obtain ⟨hreg0, hF0, hLF0, hLE0, hb0, -, -⟩ := hrt
  obtain ⟨z1, z2⟩ := zr
  simp only at hle hin hAp
  refine ⟨hreg.trans hreg0, hF0.trans hF fun a m h => ?_, ⟨fun a m hin' hout => ?_⟩, hLE0.trans hLE, ?_, hinv, hlive⟩
  · simp only [outside_append] at h ⊢
    refine ⟨h, ⟨h.1.1, cw_sub hal hk ha h.1.2⟩, ?_⟩
    have := hin.apart h.1.1
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at this; omega
  · rw [hLF.readLE a m (hLE0.inRanges_old hin') (by
      have := fresh_live hAp hin'
      simp only [outside_cons, outside_nil, and_true]; omega), hLF0.readLE a m hin' hout]
  · rw [Nat.add_mul, Nat.one_mul]; omega

/-- the frame words survive a callee at `SP - 144` writing `zr` (outside the function's window, or empty) -/
theorem fw_callG {R : RtInv} {s : State} {M M' : Memory} {zp zl zc yp n stk above : Nat} {zr : Nat × Nat}
    (hs : 4608 ≤ s.sp.toNat) (hout : Outside (s.sp.toNat - 4608) (4608 + 88) R.rt)
    (hzr : zr.2 = 0 ∨ zr.2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zr.1)
    (hk : stk ≤ 4464) (ha : above ≤ 88) (h : Fw s M zp zl zc yp n)
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 144 - stk, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + above)] ++ [zr])) : Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  obtain ⟨z1, z2⟩ := zr
  simp only at hzr
  have r : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 88 → (a + 8 ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 56 ≤ a) →
      M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
  exact ⟨(r _ (by omega) (by omega) (by omega)).trans f1, (r _ (by omega) (by omega) (by omega)).trans f2,
    (r _ (by omega) (by omega) (by omega)).trans f3, (r _ (by omega) (by omega) (by omega)).trans f4,
    (r _ (by omega) (by omega) (by omega)).trans f5, (r _ (by omega) (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega) (by omega)).trans f7⟩

set_option maxRecDepth 20000 in
/-- a store into the current array `(p, c)` keeps the runtime facts -/
theorem rt_cstore {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p c : Nat} (h : Rt R b L s zp zc n k M L1 b1) (hcur : CurA R L zp zc p c)
    (hlv : NatLive M R L1 p c) {a v : Nat} (h1 : p ≤ a) (h2 : a + 8 ≤ p + 8 * c) :
    Rt R b L s zp zc n k (M.writeLE a 8 v) L1 b1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨-, hph, -, -⟩ := hlv (by omega)
  have hF : MemFrame s.mem (M.writeLE a 8 v) (R.rt ++ winA s K A ++ [(zp, zp + 8 * zc)]) := by
    rcases hcur with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · exact a2.writeLE v (List.mem_append_right _ (List.mem_singleton_self _)) h1 (by simp only; omega)
    · obtain ⟨r, hr, r1, r2⟩ := hin
      exact a2.writeLE v (List.mem_append_left _ (List.mem_append_left _ hr)) (by omega) (by omega)
  have hLF : LiveFrame s.mem (M.writeLE a 8 v) L [(zp, zp + 8 * zc)] := by
    rcases hcur with ⟨rfl, rfl⟩ | ⟨-, hAp⟩
    · exact FvModexp.LiveFrame.writeLE_ws a3 v ⟨(p, p + 8 * c), List.mem_singleton_self _, h1, by omega⟩
    · refine a3.writeLE v (Janus.Contracts.outside_of_forall fun r hr => ?_)
      have := hAp r hr; unfold Apart at this; omega
  refine ⟨by rw [Memory.regions_writeLE]; exact a1, hF, hLF, a4, a5, inv_store_held a6 (hph.sub h1 (by omega)),
    fun hc => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := a7 hc
  exact ⟨c1, c2, by rw [Memory.accessible_writeLE]; exact c3, c4⟩

theorem natLive_store {m : Memory} {R : RtInv} {L : List (Nat × Nat)} {p c : Nat} (h : NatLive m R L p c)
    (a k v : Nat) : NatLive (m.writeLE a k v) R L p c := fun hc => by
  obtain ⟨c1, c2, c3, c4⟩ := h hc
  exact ⟨c1, c2, by rw [Memory.accessible_writeLE]; exact c3, c4⟩

/-- the current array's window / guard facts -/
theorem curA_win {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {p c : Nat} (hcur : CurA R L zp zc p c) :
    (p + 8 * c ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p) ∧ Apart p (8 * c) ((s.regs 28).toNat + 16) 8 ∧
      Apart p (8 * c) natOneA 24 ∧ Apart p (8 * c) op 8 := by
  obtain ⟨⟨-, -, -, hout, -, hgrt, -, -⟩, -, -, ⟨-, -, -, -, -, ort, -, -, -, oph, -⟩, hz1, hz2, -, -, -, -, -, -, -, -, -, -,
    hzw, hzg, -⟩ := hpre
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout
  rcases hcur with ⟨rfl, rfl⟩ | ⟨hin, hAp⟩
  · exact ⟨by omega, hzg, hz1, hz2⟩
  · exact ⟨fresh_win hout hin, (hin.apart hgrt).symm, (hin.apart ort).symm, (apart_fresh oph hAp hin).symm⟩

end FvModexp.Arm64.SubMod2N
