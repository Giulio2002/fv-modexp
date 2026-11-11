import FvModexp.Proofs.Arm64.Nat.TruncDefs

/-!
# `nat.trunc` (arm64): `Mid` on the reuse and on the `makeslice` path of `z.make(k)`

Both the main path (`k = w`) and the `set` path (`k = len x`) start with an inlined `z.make(k)`; the lemmas take the
memory `M0` after the frame push and the spills (changed only in the window) and, on the allocation path, the
`makeslice` post at `SP' = SP - 112`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.Trunc

/-- **`Mid` on the reuse path** (`k ≤ zc`, `0 < zc`): `p = zp`, `c = zc`, nothing allocated. -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n k : Nat} {s : State}
    {M : Memory} (hpre : Pre R b L zp zl zc x xl n s) (hkx : k ≤ xl) (hz : k ≤ zc) (hz0 : 0 < zc)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hF : MemFrame s.mem M (winA s 4208 64))
    (r1 : M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat) (r2 : M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (rn : k = wOf n → M.readLE (s.sp.toNat + 56) 8 = n) :
    Mid R b L zp zc x xl n s k zp zc L b M := by
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, hsv, _, ⟨hz40, hzl, hzw⟩,
    ⟨hx40, hxacc, hx48, hxh, hxw⟩, hx16, _, hzx, _, hinv⟩, _, _⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hz0
  obtain ⟨hzw', hzg⟩ := hzw hz0
  have hxw' := hxw
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw'
  unfold Apart at hga
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4208 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl16 := hx16, kx := hkx, lr := r1, fp := r2, sn := rn,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)), c0 := hz0, cap := hz, c40 := hz40, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pheld := hzh,
    px := fun hk0 => hzx.imp id (fun h => h hz0 (by omega)),
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := hxw,
    xr := fun a k h1 h2 => hF.readLE _ _ (hFo _ _ (by omega)),
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_frame_winA hF hout hb' (by omega) hinv, lsep := hLs,
    ru := fun _ => ⟨rfl, rfl⟩, ror := Or.inl ⟨rfl, rfl⟩,
    mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := winA s 4208 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega),
    sv := hsv }

/-- **`Mid` on an allocation path** (`zc < k`): `makeslice(Word, k, c)` at `SP' = SP - 112` returned
`[ptr, ptr + round)`; `M0` = the entry memory changed only in the window, `m` the memory after the call. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n k : Nat}
    {s : State} {M0 m : Memory} {ptr round c : Nat} (hpre : Pre R b L zp zl zc x xl n s) (hkx : k ≤ xl)
    (hz : zc < k) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hF : MemFrame s.mem M0 (winA s 4208 64))
    (r1 : M0.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat) (r2 : M0.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (rn : k = wOf n → M0.readLE (s.sp.toNat + 56) 8 = n)
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
      (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : k ≤ c) (hc2 : c ≤ k + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost k) :
    Mid R b L zp zc x xl n s k ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, hsv, _, _,
    ⟨hx40, hxacc, hx48, hxh, hxw⟩, hx16, _, _, _, hinv0⟩, _, _⟩ := hpre
  have hxw' := hxw
  simp only [win, outside_cons, outside_nil, and_true] at hxw'
  unfold Apart at hga
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hgM : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
      (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    rw [outside_append]; refine ⟨hgr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  have hcw : ∀ a n, ((s.sp.toNat - 120 ≤ a ∧ a + n ≤ s.sp.toNat - 104) ∨ (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 64)) →
      Outside a n (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4208 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 64 ≤ a) → Outside a n
      [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8), (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4208 64 ++ [(zp, zp + 8 * zc)]) →
      Outside a n (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl16 := hx16, kx := hkx,
    lr := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r1,
    fp := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r2,
    sn := fun hk => by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact rn hk,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ hgM]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    c0 := by omega, cap := hc1, c40 := by omega, p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega,
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    px := fun _ => Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xw := hxw,
    xr := fun a k h1 h2 => by
      rw [held_keep (hxh.sub h1 h2) hLF hMF (hCo _ _ (by omega)), hF.readLE _ _ (hFo _ _ (by omega))],
    ext := hext, bud := by omega, inv := hinv,
    lsep := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp only [win, outside_cons, outside_nil, and_true]; omega,
    ru := fun h => absurd h (by omega),
    ror := Or.inr ⟨hz, hc1, hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, hmo a n h⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [winA, outside_cons, outside_nil, and_true]; omega,
    sv := hsv }

end FvModexp.Arm64.Trunc
