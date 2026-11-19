import FvModexp.Proofs.Amd64.Nat.DivWDefs

set_option autoImplicit false

/-!
# `nat.divW` (amd64): `Mid` from the entry facts, on the reuse and on the `makeslice` path of `z.make(m)`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

namespace FvModexp.Amd64.DivW

theorem pre_env {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre R b L zp zc xp xl y s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4232 < (s.regs 4).toNat ∧ 4232 ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + 64 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4232) (4232 + 64) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    {M : Janus.Arm64.Memory} (hpre : Pre R b L zp zc xp xl y s) (hx0 : 0 < xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hz : xl.toNat ≤ zc.toNat) (hF : MemFrame s.mem M (win s 4232 64))
    (r1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (r2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) :
    Mid R b L zp zc xp xl s zp.toNat zc.toNat L b M ∧ natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat ∧
      M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0 := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxn, hxw, hinv, _, hmv, -⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzf, hzx⟩ := hzw (by omega)
  replace hzw' := hzw' (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have htw' := htw
  unfold Apart at hga htw'
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4232 ∨ (s.regs 4).toNat + 64 ≤ a) → Outside a n (win s 4232 64) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  refine ⟨{
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    ra47 := hra, xl40 := hx40, x0 := hx0, lr := r1, fp := r2,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hF.accessible]; exact htg.readable,
    tls := by rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hz, c41 := by omega, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pf := hzf, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xheld := hxh, xw := by unfold Apart; omega,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_win hF hout hb' hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := win s 4232 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega),
    mv := hmv }, natVal_frame hF (hFo _ _ (by omega)), ?_⟩
  rw [hF.readLE _ _ (hFo _ _ (by omega))]
  rcases hxn with h0 | h0
  · omega
  · exact h0

/-- **`Mid` on an allocation path** (amd64): `makeslice(Word, m, c)` whose stack ranges `cs` lie in
`[RSP - 4232, RSP - 64)` returned `[ptr, ptr + round)`. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    {M0 m : Janus.Arm64.Memory} {ptr round c : Nat} {cs : List (Nat × Nat)}
    (hpre : Pre R b L zp zc xp xl y s) (hx0 : 0 < xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hF : MemFrame s.mem M0 (win s 4232 64))
    (r1 : M0.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (r2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 4232 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 64)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    Mid R b L zp zc xp xl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m ∧
      natVal m xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat ∧
      m.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0 := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, _, hx40, hz40, hzl, hzw', hzw, hxacc,
    hx48, hxh, hxn, hxw, hinv0, _, hmv, -⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have htw' := htw
  unfold Apart at hga htw'
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hto := outside_of_inRanges htr hIn
  have hcw : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4232 ∨ (s.regs 4).toNat - 64 ≤ a) → Outside a n R.rt →
      Outside a n (R.rt ++ cs) := by
    intro a n h hr
    rw [outside_append]
    refine ⟨hr, outside_of_forall fun r hr' => ?_⟩
    have := hcs r hr'; omega
  have rd : ∀ a, (s.regs 4).toNat - 64 ≤ a → a + 8 ≤ (s.regs 4).toNat + 64 → m.readLE a 8 = M0.readLE a 8 :=
    fun a h1 h2 => hMF.readLE a 8 (hcw a 8 (by omega) (hout.of_sub (by omega) (by omega)))
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4232 ∨ (s.regs 4).toNat + 64 ≤ a) → Outside a n (win s 4232 64) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hxk : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → m.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have hxs := hxh.sub h1 h2
    rw [show m.readLE a n = M0.readLE a n by
      rcases hxs with hin | hout'
      · exact hLF.readLE a n hin trivial
      · exact hMF.readLE a n (hcw a n (by omega) hout'), hF.readLE _ _ (hFo _ _ (by omega))]
  refine ⟨{
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra, xl40 := hx40, x0 := hx0,
    lr := by rw [rd _ (by omega) (by omega)]; exact r1, fp := by rw [rd _ (by omega) (by omega)]; exact r2,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ (hcw _ _ (by omega) hgr)]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hMF.accessible, hF.accessible]; exact htg.readable,
    tls := by rw [hMF.readLE _ _ (hcw _ _ (by omega) htr), hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hc1, c41 := by omega, p8 := h8, p48 := by omega,
    pacc := Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pf := by unfold Apart; omega,
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
    ror := Or.inr ⟨hx0, hc1, hc2, hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
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
    mv := hmv }, hxk _ _ (Nat.le_refl _) (Nat.le_refl _), ?_⟩
  rw [hxk _ _ (by omega) (by omega)]
  rcases hxn with h0 | h0
  · omega
  · exact h0

end FvModexp.Amd64.DivW
