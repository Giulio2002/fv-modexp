import FvModexp.Proofs.Amd64.Nat.NatSubSetE
import FvModexp.Proofs.Amd64.Nat.NatSub0Defs

set_option autoImplicit false

/-! # `nat.sub` (amd64), empty-tolerant: the `z.set(x)` path under `PreS0` (copies of `setmid_of_reuse` /
`setmid_of_alloc` / `setPath`; twin of `FvModexp.Arm64.NatSub.setPath0`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatSub

theorem setmid_of_reuse0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M : Janus.Arm64.Memory} (hpre : PreS0 4288 R b L zp zc xp xl xc yp yl yc s) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false) (hz : xl.toNat ≤ zc.toNat)
    (hF : MemFrame s.mem M (win s 4288 80))
    (r1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (r2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) :
    SetMid R b L zp zc xp xl s zp.toNat zc.toNat L b M := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS0_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, _, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, -, hxw, -, -, -, -, hinv, -, hmv⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzf, hzx, -⟩ := hzw (by omega)
  replace hzx := hzx hx0
  replace hzw' := hzw' (by omega)
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have htw' := htw
  unfold Apart at hga htw'
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    ra47 := hra, xl40 := hx40, x0 := hx0, lr := r1, fp := r2,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hF.accessible]; exact htg.readable,
    tls := by rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hz, c41 := by omega, c40 := fun _ => hz40, ru := fun _ => ⟨rfl, rfl⟩, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pf := hzf, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := natVal_frame hF (hFo _ _ (by omega)),
    xn := by
      rw [hF.readLE _ _ (hFo _ _ (by omega))]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_win hF hout hb' hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := win s 4288 80) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega),
    mv := fun d src k hk => hmv d src k (by omega) }

theorem setmid_of_alloc0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} {M0 m : Janus.Arm64.Memory} {ptr round c : Nat} {cs : List (Nat × Nat)}
    (hpre : PreS0 4288 R b L zp zc xp xl xc yp yl yc s) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hzlt : zc.toNat < xl.toNat)
    (hF : MemFrame s.mem M0 (win s 4288 80))
    (r1 : M0.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (r2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 4288 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    SetMid R b L zp zc xp xl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS0_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, _, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, hxn, -, hxw, -, -, -, -, hinv0, -, hmv⟩ := hpre
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have htw' := htw
  unfold Apart at hga htw'
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hto := outside_of_inRanges htr hIn
  have hcw : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat - 40 ≤ a) → Outside a n R.rt → Outside a n (R.rt ++ cs) := by
    intro a n h hr
    rw [outside_append]
    refine ⟨hr, outside_of_forall fun r hr' => ?_⟩
    have := hcs r hr'; omega
  have rd : ∀ a, (s.regs 4).toNat - 40 ≤ a → a + 8 ≤ (s.regs 4).toNat + 80 → m.readLE a 8 = M0.readLE a 8 :=
    fun a h1 h2 => hMF.readLE a 8 (hcw a 8 (by omega) (hout.of_sub (by omega) (by omega)))
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hxk : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → m.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [held_keep (hxh.sub h1 h2) hLF hMF (outside_of_forall fun r hr => by have := hcs r hr; omega),
      hF.readLE _ _ (hFo _ _ (by omega))]
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra, xl40 := hx40, x0 := hx0,
    lr := by rw [rd _ (by omega) (by omega)]; exact r1, fp := by rw [rd _ (by omega) (by omega)]; exact r2,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ (hcw _ _ (by omega) hgr)]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hMF.accessible, hF.accessible]; exact htg.readable,
    tls := by rw [hMF.readLE _ _ (hcw _ _ (by omega) htr), hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hc1, c41 := by omega, c40 := fun _ => by omega, ru := fun h => absurd h (by omega), p8 := h8, p48 := by omega,
    pacc := Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pf := by unfold Apart; omega,
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
    mv := fun d src k hk => hmv d src k (by omega) }

end FvModexp.Amd64.NatSub

namespace FvModexp.Amd64.NatSub

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setPath0 (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibNatSub.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibNatSub.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hpre : PreS0 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS0_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, -, -, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, -, -, -, -, hinv, hok, -⟩ := hpre'
  replace hxacc := hxacc hx0
  replace hx48 := hx48 hx0
  replace hxh := hxh hx0
  replace hxw := hxw hx0
  have hyl : yl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hy0)
  subst hyl
  by_cases hz : xl.toNat ≤ zc.toNat
  · clear hok
    janus64_run [BitVec.msb_eq_decide] until [hSet]
    refine ReachesRet.mono (setTail impl R hmv b L zp zc xp xl yp 0#64 s zp.toNat zc.toNat L b _
      (setmid_of_reuse0 hpre hy0 hx0 hra hx15 hdf hz ?hF ?_ ?_) hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl) (fun _ h => ⟨h.1, h.2.1⟩)
    case hF => simp only [win]; janus_frame
    all_goals janus64_simp
  · obtain ⟨hok1, hcost⟩ := hok (by omega)
    clear hok
    have hwt : Apart wordT 16 ((s.regs 4).toNat - 4288) (4288 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
    unfold Apart at hwt hga
    janus64_data hd
    janus_eval_nat h_t : wordT
    rw [h_t] at hty hok1 hwt
    simp only [LiveSep, win] at hLs
    simp only [win, outside_cons, outside_nil, and_true] at hxw
    have hcs : ∀ r ∈ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)],
        (s.regs 4).toNat - 4288 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40 := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    by_cases h1x : xl.toNat = 1
    · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1x)
      subst hx1
      rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
      have hbl := blockSize_le_allocCost (8 * 1) true
      have hbs : blockSize (8 * 1) true ≤ b := by
        rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
      janus64_run [BitVec.msb_eq_decide] until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
      refine ReachesRet.mono (setTail impl R hmv b L zp zc xp 1#64 yp 0#64 s ptr.toNat 1 _ _ m
        (setmid_of_alloc0 hpre hy0 hx0 hra hx15 hdf (by omega) ?hF ?_ ?_ hcs hLF hMF hAp hIn (by omega)
          (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) h8 hinv'
          (by decide) (by decide) (by decide) (by decide))
        hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl) (fun _ h => ⟨h.1, h.2.1⟩)
      case hF => simp only [win]; janus_frame
      all_goals janus64_simp
    · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1x]] at hok1
      have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
        unfold makeCost makeCap; rw [if_neg h1x]
      have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
      have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
      janus64_run [BitVec.msb_eq_decide, FvModexp.mod64_of_lt (xl.toNat + 4) (by omega)] until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
      refine ReachesRet.mono (setTail impl R hmv b L zp zc xp xl yp 0#64 s ptr.toNat (xl.toNat + 4) _ _ m
        (setmid_of_alloc0 hpre hy0 hx0 hra hx15 hdf (by omega) ?hF ?_ ?_ hcs hLF hMF hAp hIn hle
          (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega)))
          hinv' (by omega) (by omega) hrb (by omega))
        hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl) (fun _ h => ⟨h.1, h.2.1⟩)
      case hF => simp only [win]; janus_frame
      all_goals janus64_simp

end FvModexp.Amd64.NatSub
