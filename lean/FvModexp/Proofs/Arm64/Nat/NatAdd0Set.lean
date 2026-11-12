import FvModexp.Proofs.Arm64.Nat.NatAddSet
import FvModexp.Proofs.Arm64.Nat.NatAdd0Defs

set_option autoImplicit false

/-!
# `nat.add` (arm64), empty-tolerant: the `z.set(x)` path (`n = 0 < m`) under `PreS0`

Copies of `setmid_of_reuse` / `setmid_of_alloc` (NatAddSet) and `setPath` (NatAddSetE) with the hypothesis `PreS0`
(`y` empty; `z` possibly empty); the `x` facts are specialised by `0 < m`. `setTail` is reused unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatAdd

/-- **`SetMid` on the reuse path** (`zc ≥ m`). -/
theorem setmid_of_reuse0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M : Memory} (hpre : PreS0 4304 R b L zp zc xp xl xc yp yl yc s) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (hz : xl.toNat ≤ zc.toNat)
    (hF : MemFrame s.mem M (winA s 4304 80))
    (r1 : M.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (r2 : M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat) :
    SetMid R b L zp zc xp xl s zp.toNat zc.toNat L b M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, -, hxw, -, -, -, -, hinv, -, hmv⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzx, -⟩ := hzw (by omega)
  replace hzx := hzx hx0
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  unfold Apart at hga
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, x0 := hx0, lr := r1, fp := r2,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)), cap := hz, c41 := by omega, c40 := fun _ => hz40, ru := fun _ => ⟨rfl, rfl⟩, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := natVal_frame hF (hFo _ _ (by omega)),
    xn := by
      rw [hF.readLE _ _ (hFo _ _ (by omega))]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_frame_winA hF hout hb' (by omega) hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := winA s 4304 80) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega),
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

/-- **`SetMid` on an allocation path** (`zc < m`): `makeslice(Word, m, c)` (`c = makeCap m`) at `SP' = SP - 160`
returned `[ptr, ptr + round)`. -/
theorem setmid_of_alloc0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} {M0 m : Memory} {ptr round c : Nat} (hpre : PreS0 4304 R b L zp zc xp xl xc yp yl yc s)
    (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (hzlt : zc.toNat < xl.toNat)
    (hF : MemFrame s.mem M0 (winA s 4304 80))
    (r1 : M0.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (r2 : M0.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat)
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
      (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    SetMid R b L zp zc xp xl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, hxn, -, hxw, -, -, -, -, hinv0, -, hmv⟩ := hpre
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hga
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgM : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
      (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    rw [outside_append]; refine ⟨hgr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  have hcw : ∀ a n, (s.sp.toNat - 168 ≤ a ∧ a + n ≤ s.sp.toNat - 152) →
      Outside a n (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n
      [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8), (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  have hxk : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → m.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [held_keep (hxh.sub h1 h2) hLF hMF (hCo _ _ (by omega)), hF.readLE _ _ (hFo _ _ (by omega))]
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4304 80 ++ [(zp.toNat, zp.toNat + 8 * min (xl.toNat + 1) zc.toNat)]) →
      Outside a n (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, x0 := hx0,
    lr := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r1,
    fp := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r2,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ hgM]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    cap := hc1, c41 := by omega, c40 := fun _ => by omega, ru := fun h => absurd h (by omega), p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega,
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := hxk _ _ (Nat.le_refl _) (Nat.le_refl _),
    xn := by
      rw [hxk _ _ (by omega) (by omega)]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := hext, bud := by omega, inv := hinv,
    lsep := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp only [win, outside_cons, outside_nil, and_true]; omega,
    ror := Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, hmo a n h⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [winA, outside_cons, outside_nil, and_true]; omega,
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setPath0 (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibNatAdd.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibNatAdd.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = yp)
    (h7 : s.regs 7 = yl) (h8 : s.regs 8 = yc) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hpre : PreS0 4304 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatAdd.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostX 4304 R b L zp zc xp xl yp yl s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, -, -, -, -, hinv, hok, -⟩ := hpre'
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  have hneed : need xl yl = xl.toNat := by unfold need mx; rw [if_pos (by omega)]; omega
  rw [hneed] at hok
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hyl : yl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hy0)
  subst hyl
  by_cases hz : xl.toNat ≤ zc.toNat
  · clear hok
    janus_run until [hSet]
    refine setTail impl R hmv b L zp zc xp xl yp 0#64 s zp.toNat zc.toNat L b _
      (setmid_of_reuse0 hpre hy0 hx0 hl4 hl48 hz ?hF ?_ ?_) hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · obtain ⟨hok1, hcost⟩ := hok (by omega)
    clear hok
    have hwt : Apart wordT 16 (s.sp.toNat - 4304) (4304 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
    unfold Apart at hwt hga
    janus_data hd
    janus_eval_nat h_t : wordT
    rw [h_t] at hty hok1 hwt
    simp only [LiveSep, win] at hLs
    simp only [win, outside_cons, outside_nil, and_true] at hxw
    by_cases h1 : xl.toNat = 1
    · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
      subst hx1
      rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
      have hbl := blockSize_le_allocCost (8 * 1) true
      have hbs : blockSize (8 * 1) true ≤ b := by
        rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
      janus_run until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
      refine setTail impl R hmv b L zp zc xp 1#64 yp 0#64 s ptr.toNat 1 _ _ m
        (setmid_of_alloc0 hpre hy0 hx0 hl4 hl48 (by omega) ?hF ?_ ?_ hLF hMF hAp hIn (by omega)
          (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
          (by decide) (by decide) (by decide) (by decide))
        hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [winA]; janus_frame
      all_goals janus_simp
    · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1]] at hok1
      have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
        unfold makeCost makeCap; rw [if_neg h1]
      have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
      have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
      janus_run until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
      refine setTail impl R hmv b L zp zc xp xl yp 0#64 s ptr.toNat (xl.toNat + 4) _ _ m
        (setmid_of_alloc0 hpre hy0 hx0 hl4 hl48 (by omega) ?hF ?_ ?_ hLF hMF hAp hIn hle
          (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
          (by omega) (by omega) hrb (by omega))
        hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [winA]; janus_frame
      all_goals janus_simp

end FvModexp.Arm64.NatAdd
