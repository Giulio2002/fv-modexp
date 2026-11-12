import FvModexp.Proofs.Arm64.Nat.NatSubAlloc
import FvModexp.Proofs.Arm64.Nat.NatSub0Defs

set_option autoImplicit false

/-!
# `nat.sub` (arm64), empty-tolerant: the allocation path (`0 < n ≤ m`, `zc < m`) under `PreS0`

Copies of `mid_of_alloc` (NatSubMid) and `alloc` (NatSubAlloc) with the hypothesis `PreS0` (`z` possibly empty: no
window fact; the operand facts specialised by `0 < n ≤ m`). Needed only for `cap z = 0` (else `PreS0.toS`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatSub

/-- **`Mid` on the allocation path** (`zc < m + 1`): `makeslice(Word, m + 1, m + 5)` at `SP' = SP - 160` returned the
fresh block `[ptr, ptr + round)`; `M0` = the entry memory changed only in the window, `m` the memory after the call. -/
theorem mid_of_alloc0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M0 m : Memory} {ptr round c : Nat} (hpre : PreS0 4304 R b L zp zc xp xl xc yp yl yc s) (hyx : yl.toNat ≤ xl.toNat) (hx0 : 0 < xl.toNat)
    (hy0 : 0 < yl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (hzlt : zc.toNat < xl.toNat)
    (hF : MemFrame s.mem M0 (winA s 4304 80))
    (r1 : M0.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (r2 : M0.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat)
    (r3 : M0.readLE (s.sp.toNat + 32) 8 = xp.toNat) (r4 : M0.readLE (s.sp.toNat + 40) 8 = xl.toNat)
    (r5 : M0.readLE (s.sp.toNat + 48) 8 = xc.toNat) (r6 : M0.readLE (s.sp.toNat + 64) 8 = yl.toNat)
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
      (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    Mid R b L zp zc xp xl xc yp yl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, _, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, _, _, hxw, hyacc, hy48, hyh, hyw, hinv0, _, hmv⟩ := hpre
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  replace hyacc := hyacc hy0
  replace hy48 := hy48 hy0
  replace hyh := hyh hy0
  replace hyw := hyw hy0
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  unfold Apart at hga
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hcw : ∀ a n, (s.sp.toNat - 168 ≤ a ∧ a + n ≤ s.sp.toNat - 152 ∨ s.sp.toNat - 128 ≤ a ∧ a + n ≤ s.sp.toNat + 80) →
      Outside a n (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have rd : ∀ a, (s.sp.toNat - 168 ≤ a ∧ a + 8 ≤ s.sp.toNat - 152 ∨ s.sp.toNat - 128 ≤ a ∧ a + 8 ≤ s.sp.toNat + 80) →
      m.readLE a 8 = M0.readLE a 8 := fun a h => hMF.readLE a 8 (hcw a 8 h)
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hgM : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
      (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    rw [outside_append]; refine ⟨hgr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  have hpa : InRanges ptr (8 * c) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4304 80 ++ [(zp.toNat, zp.toNat + 8 * min xl.toNat zc.toNat)]) →
      Outside a n (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, yl40 := hy40,
    lr := by rw [rd _ (by omega)]; exact r1, fp := by rw [rd _ (by omega)]; exact r2,
    sxp := by rw [rd _ (by omega)]; exact r3, sxl := by rw [rd _ (by omega)]; exact r4,
    sxc := by rw [rd _ (by omega)]; exact r5, syl := by rw [rd _ (by omega)]; exact r6,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ hgM]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    cap := by omega, c41 := by omega, c40 := fun _ => by omega, ru := fun h => absurd h (by omega), p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pheld := Or.inl hpa,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    py := Or.inr ((held_apart_fresh hyh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xheld := hext.held hxh,
    xw := by unfold Apart; omega,
    yacc := by rw [hMF.accessible, hF.accessible]; exact hyacc, y48 := hy48, yheld := hext.held hyh,
    yw := by unfold Apart; omega,
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
    mv := fun d src k hk => hmv d src k (by omega) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (LibNatSub.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = yp)
    (h7 : s.regs 7 = yl) (h8 : s.regs 8 = yc) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hz : zc.toNat < xl.toNat) (hpre : PreS0 4304 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostX 4304 R b L zp zc xp xl yp yl s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, -, hge, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, hyacc, hy48, hyh, hyw, hinv, hok, -⟩ := hpre'
  replace hxacc := hxacc (by omega)
  replace hx48 := hx48 (by omega)
  replace hxh := hxh (by omega)
  replace hxw := hxw (by omega)
  replace hyacc := hyacc hy0
  replace hy48 := hy48 hy0
  replace hyh := hyh hy0
  replace hyw := hyw hy0
  obtain ⟨hok1, hcost⟩ := hok hz
  have hwt : Apart wordT 16 (s.sp.toNat - 4304) (4304 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n
      [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8), (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  by_cases h1 : xl.toNat = 1
  · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    subst hx1
    rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
    janus_run until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    refine vv impl hap R hmv b L zp zc xp 1#64 xc yp yl yc s ptr.toNat 1 _ _ m
      (mid_of_alloc0 hpre hyx (by omega) hy0 hl4 hl48 hz ?hF ?_ ?_ ?_ ?_ ?_ ?_ hLF hMF hAp hIn (by omega)
        (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
        (by decide) (by decide) (by decide) (by decide))
      hyx hy0 hxc (by omega)
      ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega)))) hge
      _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1]] at hok1
    have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
      unfold makeCost makeCap; rw [if_neg h1]
    have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
    have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
    janus_run until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    refine vv impl hap R hmv b L zp zc xp xl xc yp yl yc s ptr.toNat (xl.toNat + 4) _ _ m
      (mid_of_alloc0 hpre hyx (by omega) hy0 hl4 hl48 hz ?hF ?_ ?_ ?_ ?_ ?_ ?_ hLF hMF hAp hIn hle
        (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
        (by omega) (by omega) hrb (by omega))
      hyx hy0 hxc (by omega)
      ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega)))) hge
      _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

end FvModexp.Arm64.NatSub
