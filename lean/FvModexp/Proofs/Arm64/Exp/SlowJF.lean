import FvModexp.Proofs.Arm64.Exp.SlowJ

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the function's own slot stores keep `JC` and `BB` (agent expmc)

`JC.frameW` / `BB.frameW`: a memory `M'` differing from `M` only in ranges `ws` inside the slot area
`[sp + 120, sp + 424)` (the loop's spills; the argument spills and the saved FP/LR are outside it) keeps the context,
the stable slots and the four buffers (their arrays are apart from the window).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- a slot-area range list -/
@[reducible] def InSlots (sp : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, sp + 120 ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 424

theorem out_slots {sp : Nat} {ws : List (Nat × Nat)} (h : InSlots sp ws) {a k : Nat}
    (ho : a + k ≤ sp + 120 ∨ sp + 424 ≤ a) : Outside a k ws := by
  induction ws with
  | nil => exact trivial
  | cons r rs ih =>
    obtain ⟨lo, hi⟩ := r
    have := h (lo, hi) List.mem_cons_self
    exact ⟨by simp only at this; omega, ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
theorem WC.frameW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {ws : List (Nat × Nat)}
    (hws : InSlots sp ws) (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hin : ∀ a k, (a + k ≤ sp - K ∨ sp + 424 ≤ a) → Outside a k ws := fun a k ho => out_slots hws (by omega)
  refine h.frame hF hrg (fun a k ho => hin a k ?_) (fun a k hL _ => hin a k ?_) (out_slots hws (by omega))
    (fun r hr => Or.inr ?_)
  · rw [outside_append, outside_append] at ho
    simp only [WN, outside_cons, outside_nil, and_true] at ho; omega
  · obtain ⟨r, hr, h1, h2⟩ := hL
    have h3 := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at h3
    omega
  · obtain ⟨t1, t3, t2⟩ := hws r hr
    refine hout.of_sub ?_ ?_
    · omega
    · omega

/-- a destination (any capacity) keeps its facts through slot stores -/
theorem DL.frameW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 : List (Nat × Nat)} {ws : List (Nat × Nat)} (hws : InSlots sp ws) (hF : MemFrame M M' ws)
    {p c : Nat} (hd : DL R L st zp zc M L1 p c) : DL R L st zp zc M' L1 p c := by
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hhd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    hF.readLE _ _ (out_slots hws (by omega))
  have e0 : stW M' st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen M' st = stLen M st := hhd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hhd 16 (by omega)
  obtain ⟨c40, hlv, hloc, hob, h0⟩ := hd
  refine ⟨c40, fun hc => ?_, hloc, fun hc => ?_, h0⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hlv hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · obtain ⟨o1, o2, o3⟩ := hob hc
    refine ⟨o1, ?_, ?_⟩
    · show Apart p (8 * c) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
      rw [e0, e1, e2]; exact o2
    · show InRanges (stW M' st) (8 * stCap M' st) R.rt → ApartAll (stW M' st) (8 * stCap M' st) L →
        Apart p (8 * c) (stW M' st) (8 * stCap M' st)
      rw [e0, e2]; exact o3

/-- a live local keeps its facts and value through slot stores -/
theorem LN.frameW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 : List (Nat × Nat)} {ws : List (Nat × Nat)} (hws : InSlots sp ws) (hF : MemFrame M M' ws)
    {p l c v : Nat} (hq : LN R L st zp zc M L1 p l c v) : LN R L st zp zc M' L1 p l c v := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hb : 0 < c → ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k := by
    intro hc a k h1 h2
    have := (Loc.ap hP hq.1.2.2.1 hc).1
    unfold Apart at this
    exact hF.readLE _ _ (out_slots hws (by omega))
  obtain ⟨hd, hlc, hv, hn⟩ := hq
  refine ⟨DL.frameW hP hws hF hd, hlc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with c0 | c0
    · have : l = 0 := by omega
      subst this
      rw [← hv]; exact Memory.readLE_congr fun i hi => absurd hi (by omega)
    · rw [← hv]; exact hb c0 _ _ (Nat.le_refl _) (by omega)
  · rcases hn with h0 | hne
    · exact Or.inl h0
    · rcases Nat.eq_zero_or_pos c with c0 | c0
      · exact Or.inl (by omega)
      · right; rw [hb c0 _ _ (by omega) (by omega)]; exact hne

theorem BB.frameW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 : List (Nat × Nat)} {ws : List (Nat × Nat)} (hws : InSlots sp ws) (hF : MemFrame M M' ws)
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat} (hB : BB R L st zp zc M L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc) :
    BB R L st zp zc M' L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc :=
  ⟨LN.frameW hP hws hF hB.bz, DL.frameW hP hws hF hB.bzz, hB.lzz, DL.frameW hP hws hF hB.br, hB.lr,
    DL.frameW hP hws hF hB.bq, hB.lq, hB.p1, hB.p2, hB.p3, hB.p4, hB.p5, hB.p6⟩

theorem JC.frameW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {S : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S M L1 b1)
    {S' : State} {ws : List (Nat × Nat)} (hws : InSlots sp ws) (hF : MemFrame M S'.mem ws)
    (hrg : S'.mem.regions = M.regions) (esp : S'.sp = BitVec.ofNat 64 sp) (e28 : S'.regs 28 = BitVec.ofNat 64 g)
    (e29 : S'.regs 29 = BitVec.ofNat 64 (sp - 8)) (e18 : S'.regs 18 = r18) :
    JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' S'.mem L1 b1 := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  exact ⟨WC.frameW hP hj.wc hws hF hrg, rfl, esp, e28, e29, e18,
    hj.sf.keep fun a k ha => hF.readLE _ _ (out_slots hws (by omega))⟩

end

end FvModexp.Arm64.ExpSlow
