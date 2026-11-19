import FvModexp.Proofs.Amd64.Nat.MulAddWWVww

/-!
# `nat.mulAddWW` (amd64): `Mid` from the entry facts, on the reuse and on the `makeslice` path of `z.make(m + 1)`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

namespace FvModexp.Amd64.MulAddWW

/-- The facts of the entry state every constructor needs (amd64 `CallEnv` destructured). -/
theorem pre_env {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s : State}
    (hpre : Pre R b L zp zc xp xl y r s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4208 < (s.regs 4).toNat ∧ 4208 ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + 72 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4208) (4208 + 72) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

/-- **`Mid` on the reuse path** (`zc ≥ m + 1`, amd64). -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s : State}
    {M : Janus.Arm64.Memory} (hpre : Pre R b L zp zc xp xl y r s)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hz : xl.toNat + 1 ≤ zc.toNat) (hF : MemFrame s.mem M (win s 4208 72))
    (r1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (r2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r3 : M.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat) (r4 : M.readLE ((s.regs 4).toNat - 24) 8 = xl.toNat + 1) :
    Mid R b L zp zc xp xl s zp.toNat zc.toNat L b M := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxw, hinv, _⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzf, hzx⟩ := hzw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have htw' := htw
  unfold Apart at hga htw'
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n (win s 4208 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    ra47 := hra, xl40 := hx40, lr := r1, fp := r2, sm := r3, sm1 := r4,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hF.accessible]; exact htg.readable,
    tls := by rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hz, c41 := by omega, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pf := hzf, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_win hF hout hb' hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := win s 4208 72) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega) }

/-- **`Mid` on the allocation path** (amd64): `makeslice(Word, m + 1, m + 5)` whose stack ranges `cs` lie in
`[RSP - 4208, RSP - 40)` returned `[ptr, ptr + round)`. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s : State}
    {M0 m : Janus.Arm64.Memory} {ptr round : Nat} {cs : List (Nat × Nat)}
    (hpre : Pre R b L zp zc xp xl y r s)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hF : MemFrame s.mem M0 (win s 4208 72))
    (r1 : M0.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (r2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r3 : M0.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat) (r4 : M0.readLE ((s.regs 4).toNat - 24) 8 = xl.toNat + 1)
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 4208 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * (xl.toNat + 5) ≤ round) (hcost : round ≤ makeCost (xl.toNat + 1)) :
    Mid R b L zp zc xp xl s ptr (xl.toNat + 5) (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxw, hinv0, _⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have htw' := htw
  unfold Apart at hga htw'
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hto := outside_of_inRanges htr hIn
  have hcw : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat - 40 ≤ a) → Outside a n R.rt →
      Outside a n (R.rt ++ cs) := by
    intro a n h hr
    rw [outside_append]
    refine ⟨hr, outside_of_forall fun r hr' => ?_⟩
    have := hcs r hr'; omega
  have rd : ∀ a, (s.regs 4).toNat - 40 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 → m.readLE a 8 = M0.readLE a 8 :=
    fun a h1 h2 => hMF.readLE a 8 (hcw a 8 (by omega) (hout.of_sub (by omega) (by omega)))
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n (win s 4208 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hpa : InRanges ptr (8 * (xl.toNat + 5)) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra, xl40 := hx40,
    lr := by rw [rd _ (by omega) (by omega)]; exact r1, fp := by rw [rd _ (by omega) (by omega)]; exact r2,
    sm := by rw [rd _ (by omega) (by omega)]; exact r3, sm1 := by rw [rd _ (by omega) (by omega)]; exact r4,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ (hcw _ _ (by omega) hgr)]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hMF.accessible, hF.accessible]; exact htg.readable,
    tls := by rw [hMF.readLE _ _ (hcw _ _ (by omega) htr), hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := by omega, c41 := by omega, p8 := h8, p48 := by omega,
    pacc := Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pf := by unfold Apart; omega, pheld := Or.inl hpa,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48,
    xw := by unfold Apart; omega,
    ext := hext, bud := by omega, inv := hinv, lsep := hLs,
    ror := Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, by
      simp only [outside_append, win, outside_cons, outside_nil, and_true] at h
      exact hcw a n (by omega) h.1.1⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [win, outside_cons, outside_nil, and_true]; omega }

end FvModexp.Amd64.MulAddWW
