import FvModexp.Proofs.Arm64.Nat.DivWDefs

/-!
# `nat.divW` (arm64): `Mid` from the entry facts, on the reuse and on the `makeslice` path of `z.make(m)`

Both the `divWVW` path and the `set` path (`y = 1`) start with the same inlined `z.make(m)` (`m = len x > 0`); the
lemmas take the memory `M0` after the frame push and the spills (changed only in the window) and, on the allocation
path, the `makeslice` post at `SP' = SP - 144`. Besides `Mid` they give the operand facts at `M`: its value and its
non-zero top limb (`x` normalised).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.DivW

/-- **`Mid` on the reuse path** (`zc ≥ m`): `p = zp`, `c = zc`, nothing allocated. -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    {M : Memory} (hpre : Pre R b L zp zc xp xl y s) (hx0 : 0 < xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (hz : xl.toNat ≤ zc.toNat)
    (hF : MemFrame s.mem M (winA s 4240 64))
    (r1 : M.readLE (s.sp.toNat - 144) 8 = (s.regs 30).toNat) (r2 : M.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat) :
    Mid R b L zp zc xp xl s zp.toNat zc.toNat L b M ∧ natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat ∧
      M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxn, hxw, hinv, _, hmv, -⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzx⟩ := hzw (by omega)
  replace hzw' := hzw' (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  unfold Apart at hga
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  refine ⟨{
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, x0 := hx0, lr := r1, fp := r2,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)), cap := hz, c41 := by omega, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xheld := hxh, xw := by unfold Apart; omega,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_frame_winA hF hout hb' (by omega) hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := winA s 4240 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega),
    mv := hmv }, natVal_frame hF (hFo _ _ (by omega)), ?_⟩
  rw [hF.readLE _ _ (hFo _ _ (by omega))]
  rcases hxn with h0 | h0
  · omega
  · exact h0

/-- **`Mid` on an allocation path** (`zc < m`): `makeslice(Word, m, c)` (`c = makeCap m`) at `SP' = SP - 144`
returned `[ptr, ptr + round)`; `M0` = the entry memory changed only in the window, `m` the memory after the call. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64}
    {s : State} {M0 m : Memory} {ptr round c : Nat} (hpre : Pre R b L zp zc xp xl y s) (hx0 : 0 < xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hF : MemFrame s.mem M0 (winA s 4240 64))
    (r1 : M0.readLE (s.sp.toNat - 144) 8 = (s.regs 30).toNat) (r2 : M0.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat)
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    Mid R b L zp zc xp xl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m ∧
      natVal m xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat ∧
      m.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxn, hxw, hinv0, _, hmv, -⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hga
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hgM : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 24)]) := by
    rw [outside_append]; refine ⟨hgr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  have hcw : ∀ a n, (s.sp.toNat - 152 ≤ a ∧ a + n ≤ s.sp.toNat - 136) →
      Outside a n (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
        (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n
      [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8), (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  have hxk : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → m.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [held_keep (hxh.sub h1 h2) hLF hMF (hCo _ _ (by omega)), hF.readLE _ _ (hFo _ _ (by omega))]
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4240 64 ++ zr zp zc) →
      Outside a n (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
        (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  refine ⟨{
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, x0 := hx0,
    lr := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r1,
    fp := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r2,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ hgM]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    cap := hc1, c41 := by omega, p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega,
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xheld := hext.held hxh,
    xw := by unfold Apart; omega,
    ext := hext, bud := by omega, inv := hinv,
    lsep := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp only [win, outside_cons, outside_nil, and_true]; omega,
    ror := Or.inr ⟨hx0, by omega, by omega, hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, hmo a n h⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [winA, outside_cons, outside_nil, and_true]; omega,
    mv := hmv }, hxk _ _ (Nat.le_refl _) (Nat.le_refl _), ?_⟩
  rw [hxk _ _ (by omega) (by omega)]
  rcases hxn with h0 | h0
  · omega
  · exact h0

end FvModexp.Arm64.DivW
