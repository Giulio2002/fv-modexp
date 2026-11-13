import FvModexp.Proofs.Amd64.Nat.MulAddWWXA
import FvModexp.Proofs.Amd64.Nat.MulAddWW

set_option autoImplicit false

/-!
# `nat.mulAddWW` (amd64): the EXACT-WRITE variant `ensX` (agent divmc, amd64 port of Arm64/Nat/MulAddWWX.lean)

For `nat.mul`'s call `z.mulAddWW(x, y[0], 0)` (`m ≥ 1`, `r = 0`, `m < 2^39`): `Post` and `XQ` — the result's
capacity is `< 2^40`, a fresh result has capacity `≥ m + 1`, and when `z` is large enough (`m + 1 ≤ zc`) the result is
`z`'s array with only `z[0:m+1]` written, holding `X·y` (or `y = 0`: nothing written). Paths: `y = 0` → `+0x122` →
`setWord(0)` (`toSetX` / `setZeroX`), `m + 1 ≤ zc` (`reuseX`), else `makeslice` (`allocX`); the latter two re-run
`reuse` / `alloc` with `XM`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges inv_win)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.MulAddWW

/-- `XM` on the reuse path from the window-only frame of the entry segment -/
theorem xm_of_reuse {R : RtInv} {L : List (Nat × Nat)} {zp zc xl : BitVec 64} {s : State}
    {M : Janus.Arm64.Memory} (hLs : LiveSep L (win s 4208 72)) (hz40 : zc.toNat < 2 ^ 40)
    (hF : MemFrame s.mem M (win s 4208 72)) : XM R L zp zc xl s zp.toNat zc.toNat M :=
  ⟨hz40, fun _ => ⟨rfl, rfl, hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2, setLF hF hLs⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem reuseX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hz : xl.toNat + 1 ≤ zc.toNat) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, -, hLs, -, -⟩, -, hx40, hz40, -, hzw', -, hxacc, hx48, -, hxw, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus64_run [hx0', hy0', BitVec.msb_eq_decide, mod64_of_lt (a := xl.toNat + 1) (by omega),
    toInt_small (xl + 1#64) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] until [hMid]
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n (win s 4208 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  refine vwwX impl hap R b L zp zc xp xl xc y r s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hra hx15 hdf hz ?hF ?_ ?_ ?_ ?_) (xm_of_reuse hLs hz40 ?hF) hx0 hy0
    (natVal_frame ?hF (hWo _ _ (by omega))) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem allocX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0) (hxs : xl.toNat < 2 ^ 39)
    (hz : zc.toNat < xl.toNat + 1) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, hx40, hz40, -, -, -, hxacc, hx48, hxh, hxw,
    hinv, hok⟩ := hpre'
  have hneed : need xl y r = xl.toNat + 1 := by unfold need; rw [if_neg (by omega)]
  rw [hneed] at hok
  obtain ⟨hok1, hcost⟩ := hok (by omega)
  rw [show makeCap (xl.toNat + 1) = xl.toNat + 5 by unfold makeCap; rw [if_neg (by omega)]] at hok1
  have hmc : makeCost (xl.toNat + 1) = allocCost (8 * (xl.toNat + 5)) := by
    unfold makeCost makeCap; rw [if_neg (by omega)]
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + 5)) true
  have hbs : blockSize (8 * (xl.toNat + 5)) true ≤ b := by omega
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4208) (4208 + 72) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  obtain ⟨_hwa, _hws, _hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus64_run [hx0', hy0', BitVec.msb_eq_decide, mod64_of_lt (a := xl.toNat + 1) (by omega),
    mod64_of_lt (a := xl.toNat + 5) (by omega),
    toInt_small (xl + 1#64) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] until [hMid] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n (win s 4208 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n
      [((s.regs 4).toNat - 112 - 4096, (s.regs 4).toNat - 112),
        ((s.regs 4).toNat - 112 + 8, (s.regs 4).toNat - 112 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  refine vwwX impl hap R b L zp zc xp xl xc y r s ptr.toNat (xl.toNat + 5) _ _ m
    (mid_of_alloc hpre hra hx15 hdf ?hF ?_ ?_ ?_ ?_ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega) hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega)))
      hinv' hrb (by omega))
    ⟨by omega, fun hz' => absurd hz' (by omega)⟩ hx0 hy0
    ((held_keep hxh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega))))
    _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)

/-- the post of the `y = 0`, `r = 0` path (`setWord(0)` = `z[:0]`), memory changed only in the window -/
theorem post_setZero {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s s' : State}
    (hpre : Pre R b L zp zc xp xl y r s) (hy : y.toNat = 0) (hr : r.toNat = 0)
    (hF : MemFrame s.mem s'.mem (win s 4208 72)) (hfs : s'.fsBase = s.fsBase)
    (q0 : (s'.regs 0).toNat = zp.toNat) (q1 : (s'.regs 3).toNat = 0) (q2 : (s'.regs 1).toNat = zc.toNat) :
    PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, -⟩, -, hx40, hz40, hzl, hzw', -, -, -, -, -, hinv, -⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hmf : ∀ ws, MemFrame s.mem s'.mem (R.rt ++ win s 4208 72 ++ ws) := fun ws =>
    MemFrame.mono hF fun a n h => by simp only [outside_append] at h; exact h.1.2
  refine ⟨⟨hfs, zp.toNat, 0, zc.toNat, q0, q1, q2, by simp [hy, hr], Or.inl rfl, by omega, by omega, L, b,
    LiveExt.refl R L, Nat.sub_le _ _, inv_win hF hout hb' hinv, fun hc => ?nl, Or.inl ⟨rfl, rfl⟩,
    hmf _, setLF hF hLs⟩, ?_⟩
  case nl =>
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  refine ⟨by rw [q2]; exact hz40, Or.inl ⟨q0, q2⟩, fun hz => ⟨q0, q2, Or.inr ⟨hy, hr, ?_⟩, hmf _, setLF hF hLs⟩⟩
  exact natVal_frame hF (by simp only [win, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `+0x122` with `r = 0` (`TESTQ R10, R10` → return `z[:0]`), carrying `XQ` -/
theorem setZeroX (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zc xp xl y r : BitVec 64) (s : State) (M : Janus.Arm64.Memory) (h : SetRel R b L zp zc xp xl y r s M)
    (hy : y.toNat = 0) (hr : r.toNat = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = zp) (h1 : S.regs 1 = zc) (h10 : S.regs 10 = r)
    (hsp : S.regs 4 = s.regs 4 - 104#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  have hpre := h.pre
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env h.pre
  obtain ⟨-, -, hra, -, -, hF, r1, r2, r3, -⟩ := h
  have hr0 : r = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr)
  subst hr0
  janus64_run [hm, r1, r2, BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_setZero hpre hy hr hF ?_ ?_ ?_ ?_⟩
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hx15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the entry → `+0x122` for `y = 0` (`m ≠ 0`), then `setZeroX` -/
theorem toSetX (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y r) (hx0 : xl.toNat ≠ 0) (hy : y.toNat = 0) (hr : r.toNat = 0)
    (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, -, -, hro, -⟩, -, hx40, hz40, -⟩ := hpre'
  have hxy : natVal s.mem xp.toNat xl.toNat * y.toNat = 0 := by rw [hy]; simp
  have hrel : ∀ M : Janus.Arm64.Memory, MemFrame s.mem M (win s 4208 72) →
      M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 →
      M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      M.readLE ((s.regs 4).toNat + 64) 8 = r.toNat → M.regions = s.mem.regions → SetRel R b L zp zc xp xl y r s M :=
    fun M hF r1 r2 r3 hrg => ⟨hpre, hxy, hra, hx15, hdf, hF, r1, r2, r3,
      FvModexp.dataLoaded_frame64 hd hrg hro (hF.widen R.rt) (fun q hq _ => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by simp only; omega))⟩
  have hy0 : y = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  subst hy0
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  janus64_run [hx0', BitVec.msb_eq_decide] until [hSet]
  refine setZeroX impl R b L zp zc xp xl 0#64 r s _ (hrel _ ?hF ?_ ?_ ?_ (by simp)) hy hr _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals janus64_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fullX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64)
    (hx0 : xl.toNat ≠ 0) (hxs : xl.toNat < 2 ^ 39) (hr : r.toNat = 0) :
    Summary (LibMulAddWW.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = y ∧ s.regs 10 = r ∧ Pre R b L zp zc xp xl y r s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, hpre⟩
  have he : Entry s zp zl zc xp xl xc y r := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibMulAddWW.program.link impl) := by
    rw [LibMulAddWW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibMulAddWW.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  by_cases hy0 : y.toNat = 0
  · exact toSetX impl R b L zp zl zc xp xl xc y r s he hx0 hy0 hr hpre
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact reuseX impl hap R b L zp zl zc xp xl xc y r s he hx0 hy0 hz hpre
  · exact allocX impl hap R hmk' b L zp zl zc xp xl xc y r s he hx0 hy0 hxs (by omega) hpre

/-- **`nat.mulAddWW`, exact-write variant** (amd64; `m ≥ 1`, `r = 0`, `m < 2^39`): `Post ∧ XQ` -/
theorem ensX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64)
    (hx0 : xl.toNat ≠ 0) (hxs : xl.toNat < 2 ^ 39) (hr : r.toNat = 0) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y, r]
      (Pre R b L zp zc xp xl y r) (fun s s' => Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s') := by
  rw [show names = LibMulAddWW.names from rfl, ← LibMulAddWW.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (fullX impl hap R hmk b L zp zl zc xp xl xc y r hx0 hxs hr) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      h_a7, hpre⟩ fun s' ⟨⟨a, b, c, d, e⟩, ⟨hfs, hq⟩, hx⟩ => ⟨⟨a, b, c, d⟩, ⟨hfs, e.trans h_df.symm, hq⟩, hx⟩

end FvModexp.Amd64.MulAddWW
