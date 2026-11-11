import FvModexp.Proofs.Amd64.Nat.LshDefs

/-!
# `nat.lsh` (amd64): `Mid` on the reuse and on the `makeslice` path of `z.make(n + 1)`

The lemmas take the memory `M0` after the frame push and the spills (changed only in the window) and, on the
allocation path, the `makeslice` post (callee ranges `cs` inside `[e - 4248, e - 56)`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

namespace FvModexp.Amd64.Lsh

/-- **`Mid` on the reuse path** (`n + 1 ≤ zc`): `p = zp`, `c = zc`, nothing allocated. -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl sh : Nat} {s : State}
    {M : Janus.Arm64.Memory} (hpre : Pre R b L zp zl zc x xl sh s) (hz : need xl sh ≤ zc)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hF : MemFrame s.mem M (win s 4248 64))
    (r1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (r2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r3 : M.readLE ((s.regs 4).toNat - 40) 8 = sh / 64) (r4 : M.readLE ((s.regs 4).toNat - 48) 8 = xl + sh / 64)
    (r5 : M.readLE ((s.regs 4).toNat - 56) 8 = need xl sh) :
    Mid R b L zp zc x xl sh s zp zc L b M := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, hsv, _, ⟨hz40, hzl, hzw⟩,
    ⟨hx40, hxacc, hx48, hxh, hxw⟩, hn16, hzx, _, hinv⟩, hsh0, hxl0⟩ := hpre
  have hz0 : 0 < zc := by simp only [need] at hz; omega
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hz0
  obtain ⟨hzw', hzg, hzf⟩ := hzw hz0
  have hxw' := hxw
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw'
  have htw' := htw
  unfold Apart at hga htw'
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 64 ≤ a) → Outside a n (win s 4248 64) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra,
    n16 := hn16, xl0 := hxl0, sh0 := hsh0, lr := r1, fp := r2, sq := r3, sn := r4, sn1 := r5,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hF.accessible]; exact htg.readable,
    tls := by rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hz, c40 := hz40, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pf := hzf, pheld := hzh,
    px := hzx.imp id (fun h => h hz0 hxl0),
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := hxw,
    xr := fun a k h1 h2 => hF.readLE _ _ (hFo _ _ (by omega)),
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_win hF hout hb' hinv, lsep := hLs,
    ru := fun _ => ⟨rfl, rfl⟩, ror := Or.inl ⟨rfl, rfl⟩,
    mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := win s 4248 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega),
    sv := hsv }

/-- **`Mid` on the allocation path** (`zc < n + 1`): `makeslice(Word, n + 1, n + 5)` whose stack ranges `cs` lie in
`[e - 4248, e - 56)` returned `[ptr, ptr + round)`; `M0` = the entry memory changed only in the window. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl sh : Nat} {s : State}
    {M0 m : Janus.Arm64.Memory} {ptr round : Nat} {cs : List (Nat × Nat)}
    (hpre : Pre R b L zp zl zc x xl sh s) (hz : zc < need xl sh)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hF : MemFrame s.mem M0 (win s 4248 64))
    (r1 : M0.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (r2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r3 : M0.readLE ((s.regs 4).toNat - 40) 8 = sh / 64) (r4 : M0.readLE ((s.regs 4).toNat - 48) 8 = xl + sh / 64)
    (r5 : M0.readLE ((s.regs 4).toNat - 56) 8 = need xl sh)
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 4248 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 56)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * (need xl sh + 4) ≤ round) (hcost : round ≤ makeCost (need xl sh)) :
    Mid R b L zp zc x xl sh s ptr (need xl sh + 4) (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, hsv, _, _,
    ⟨hx40, hxacc, hx48, hxh, hxw⟩, hn16, _, _, hinv0⟩, hsh0, hxl0⟩ := hpre
  have hxw' := hxw
  simp only [win, outside_cons, outside_nil, and_true] at hxw'
  have htw' := htw
  unfold Apart at hga htw'
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hto := outside_of_inRanges htr hIn
  have hcw : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat - 56 ≤ a) → Outside a n R.rt →
      Outside a n (R.rt ++ cs) := by
    intro a n h hr
    rw [outside_append]
    refine ⟨hr, outside_of_forall fun r hr' => ?_⟩
    have := hcs r hr'; omega
  have rd : ∀ a, (s.regs 4).toNat - 56 ≤ a → a + 8 ≤ (s.regs 4).toNat + 64 → m.readLE a 8 = M0.readLE a 8 :=
    fun a h1 h2 => hMF.readLE a 8 (hcw a 8 (by omega) (hout.of_sub (by omega) (by omega)))
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 64 ≤ a) → Outside a n (win s 4248 64) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hpa : InRanges ptr (8 * (need xl sh + 4)) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra,
    n16 := hn16, xl0 := hxl0, sh0 := hsh0,
    lr := by rw [rd _ (by omega) (by omega)]; exact r1, fp := by rw [rd _ (by omega) (by omega)]; exact r2,
    sq := by rw [rd _ (by omega) (by omega)]; exact r3, sn := by rw [rd _ (by omega) (by omega)]; exact r4,
    sn1 := by rw [rd _ (by omega) (by omega)]; exact r5,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ (hcw _ _ (by omega) hgr)]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hMF.accessible, hF.accessible]; exact htg.readable,
    tls := by rw [hMF.readLE _ _ (hcw _ _ (by omega) htr), hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := by omega, c40 := by simp only [need] at hn16 ⊢; omega, p8 := h8, p48 := by omega,
    pacc := Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pf := by unfold Apart; omega, pheld := Or.inl hpa,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xw := hxw,
    xr := fun a k h1 h2 => by
      rw [held_keep (hxh.sub h1 h2) hLF hMF (outside_of_forall fun r hr' => by have := hcs r hr'; omega),
        hF.readLE _ _ (hFo _ _ (by omega))],
    ext := hext, bud := by omega, inv := hinv,
    lsep := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp only [win, outside_cons, outside_nil, and_true]; omega,
    ru := fun h => absurd h (by omega),
    ror := Or.inr ⟨hz, by omega, hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, by
      simp only [outside_append, win, outside_cons, outside_nil, and_true] at h
      exact hcw a n (by omega) h.1.1⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [win, outside_cons, outside_nil, and_true]; omega,
    sv := hsv }

end FvModexp.Amd64.Lsh
