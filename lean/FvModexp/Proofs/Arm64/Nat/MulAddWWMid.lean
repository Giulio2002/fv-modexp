import FvModexp.Proofs.Arm64.Nat.MulAddWWVww

/-!
# `nat.mulAddWW` (arm64): `Mid` from the entry facts, on the reuse and on the `makeslice` path of `z.make(m + 1)`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.MulAddWW

/-- **`Mid` on the reuse path** (`zc ≥ m + 1`): `p = zp`, `c = zc`, nothing allocated; `M` = the entry memory changed
only in the window (frame push and spills). -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s : State}
    {M : Memory} (hpre : Pre R b L zp zc xp xl y r s)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (hz : xl.toNat + 1 ≤ zc.toNat)
    (hF : MemFrame s.mem M (winA s 4208 72))
    (r1 : M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat) (r2 : M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (r3 : M.readLE (s.sp.toNat + 40) 8 = xl.toNat) (r4 : M.readLE (s.sp.toNat - 24) 8 = xl.toNat + 1) :
    Mid R b L zp zc xp xl s zp.toNat zc.toNat L b M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxw, hinv, _⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzx⟩ := hzw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  unfold Apart at hga
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n (winA s 4208 72) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, lr := r1, fp := r2, sm := r3, sm1 := r4,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)), cap := hz, c41 := by omega, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_frame_winA hF hout hb' (by omega) hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := winA s 4208 72) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega) }

/-- **`Mid` on the allocation path** (`zc < m + 1`): `makeslice(Word, m + 1, m + 5)` at `SP' = SP - 112` returned the
fresh block `[ptr, ptr + round)`; `M0` = the entry memory changed only in the window, `m` the memory after the call. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s : State}
    {M0 m : Memory} {ptr round : Nat} (hpre : Pre R b L zp zc xp xl y r s)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hF : MemFrame s.mem M0 (winA s 4208 72))
    (r1 : M0.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat) (r2 : M0.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (r3 : M0.readLE (s.sp.toNat + 40) 8 = xl.toNat) (r4 : M0.readLE (s.sp.toNat - 24) 8 = xl.toNat + 1)
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
      (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * (xl.toNat + 5) ≤ round) (hcost : round ≤ makeCost (xl.toNat + 1)) :
    Mid R b L zp zc xp xl s ptr (xl.toNat + 5) (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxw, hinv0, _⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hga
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hcw : ∀ a n, (s.sp.toNat - 120 ≤ a ∧ a + n ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 80 ≤ a ∧ a + n ≤ s.sp.toNat + 72) →
      Outside a n (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have rd : ∀ a, (s.sp.toNat - 120 ≤ a ∧ a + 8 ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 80 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72) →
      m.readLE a 8 = M0.readLE a 8 := fun a h => hMF.readLE a 8 (hcw a 8 h)
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n (winA s 4208 72) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hgM : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
      (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    rw [outside_append]; refine ⟨hgr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  have hpa : InRanges ptr (8 * (xl.toNat + 5)) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) →
      Outside a n (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40,
    lr := by rw [rd _ (by omega)]; exact r1, fp := by rw [rd _ (by omega)]; exact r2,
    sm := by rw [rd _ (by omega)]; exact r3, sm1 := by rw [rd _ (by omega)]; exact r4,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ hgM]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    cap := by omega, c41 := by omega, p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pheld := Or.inl hpa,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48,
    xw := by unfold Apart; omega,
    ext := hext, bud := by omega, inv := hinv, lsep := hLs,
    ror := Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, hmo a n h⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [winA, outside_cons, outside_nil, and_true]; omega }

end FvModexp.Arm64.MulAddWW
