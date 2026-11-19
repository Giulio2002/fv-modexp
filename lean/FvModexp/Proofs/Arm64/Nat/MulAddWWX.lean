import FvModexp.Proofs.Arm64.Nat.MulAddWWXA
import FvModexp.Proofs.Arm64.Nat.MulAddWW

/-!
# `nat.mulAddWW` (arm64): the EXACT-WRITE variant `ensX` (agent divmc, wrapping asm's `MulAddWW*` proof)

For `nat.mul`'s call `z.mulAddWW(x, y[0], 0)` (`m ≥ 1`, `r = 0`, `m < 2^39`): asm's `Post` and `XQ` — the result's
capacity is `< 2^40`, a fresh result has capacity `≥ m + 1`, and when `z` is large enough (`m + 1 ≤ zc`) the result is
`z`'s array with only `z[0:m+1]` written, holding `X·y` (or `y = 0`: nothing written). Paths: `y = 0` → `setWord(0)`
(`setZeroX`), `m + 1 ≤ zc` (`reuseX`), else `makeslice` (`allocX`); the latter two re-run asm's segments with `XM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.MulAddWW

/-- `XM` on the reuse path from the window-only frame of the entry segment -/
theorem xm_of_reuse {R : RtInv} {L : List (Nat × Nat)} {zp zc xl : BitVec 64} {s : State}
    {M : Memory} (hLs : ∀ r ∈ L, Outside r.1 (r.2 - r.1) (win s 4208 72)) (hsp0 : 4208 ≤ s.sp.toNat)
    (hz40 : zc.toNat < 2 ^ 40)
    (hF : MemFrame s.mem M (winA s 4208 72)) : XM R L zp zc xl s zp.toNat zc.toNat M := by
  refine ⟨hz40, fun _ => ⟨rfl, rfl, hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2, ?_⟩⟩
  exact liveFrame_of_frame (rs := winA s 4208 72) (hF.mono fun a n h => by
      simp only [outside_append] at h; exact h.1)
    (fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
    (fun r hr => by
      simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem reuseX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (h7 : s.regs 7 = r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hz : xl.toNat + 1 ≤ zc.toNat) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, hLs, -⟩, -, hx40, hz40, -, hzw', -, hxacc,
    hx48, -, hxw, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus_run [hx0', hy0'] until [hMid]
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n (winA s 4208 72) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  refine vwwX impl hap R b L zp zc xp xl xc y r s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hl4 hl48 hz ?hF ?_ ?_ ?_ ?_) (xm_of_reuse hLs hb' hz40 ?hF) hx0 hy0
    (natVal_frame ?hF (hWo _ _ (by omega))) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals try janus_simp
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem allocX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (h7 : s.regs 7 = r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0) (hxs : xl.toNat < 2 ^ 39)
    (hz : zc.toNat < xl.toNat + 1) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hx40, hz40, -, -, -, hxacc,
    hx48, hxh, hxw, hinv, hok⟩ := hpre'
  have hneed : need xl y r = xl.toNat + 1 := by unfold need; rw [if_neg (by omega)]
  rw [hneed] at hok
  obtain ⟨hok1, hcost⟩ := hok (by omega)
  rw [show makeCap (xl.toNat + 1) = xl.toNat + 5 by unfold makeCap; rw [if_neg (by omega)]] at hok1
  have hmc : makeCost (xl.toNat + 1) = allocCost (8 * (xl.toNat + 5)) := by
    unfold makeCost makeCap; rw [if_neg (by omega)]
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + 5)) true
  have hbs : blockSize (8 * (xl.toNat + 5)) true ≤ b := by omega
  have hwt : Apart wordT 16 (s.sp.toNat - 4208) (4208 + 72) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus_run [hx0', hy0'] until [hMid] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n (winA s 4208 72) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n
      [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8), (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  refine vwwX impl hap R b L zp zc xp xl xc y r s ptr.toNat (xl.toNat + 5) _ _ m
    (mid_of_alloc hpre hl4 hl48 ?hF ?_ ?_ ?_ ?_ hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
      hrb (by omega))
    ⟨by omega, fun hz' => absurd hz' (by omega)⟩ hx0 hy0
    ((held_keep hxh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega))))
    _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals try janus_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)

/-- the post of the `y = 0`, `r = 0` path (`setWord(0)` = `z[:0]`), memory changed only in the window -/
theorem post_setZero {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s s' : State}
    (hpre : Pre R b L zp zc xp xl y r s) (hy : y.toNat = 0) (hr : r.toNat = 0)
    (hF : MemFrame s.mem s'.mem (winA s 4208 72)) (q0 : (s'.regs 0).toNat = zp.toNat)
    (q1 : (s'.regs 1).toNat = 0) (q2 : (s'.regs 2).toNat = zc.toNat) :
    Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, hx40, hz40, hzl, hzw', -, -, -, -, -,
    hinv, -⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hlf : ∀ ws, LiveFrame s.mem s'.mem L ws := fun ws =>
    liveFrame_of_frame (rs := winA s 4208 72) (ws := ws) (MemFrame.mono hF fun a n h => by
        simp only [outside_append] at h; exact h.1)
      (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)
  have hmf : ∀ ws, MemFrame s.mem s'.mem (R.rt ++ winA s 4208 72 ++ ws) := fun ws =>
    MemFrame.mono hF fun a n h => by simp only [outside_append] at h; exact h.1.2
  refine ⟨⟨zp.toNat, 0, zc.toNat, q0, q1, q2, by simp [hy, hr], Or.inl rfl, by omega, by omega, L, b,
    LiveExt.refl R L, Nat.sub_le _ _, inv_frame_winA hF hout hb' (by omega) hinv, fun hc => ?nl, Or.inl ⟨rfl, rfl⟩,
    hmf _, hlf _⟩, ?_⟩
  case nl =>
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  refine ⟨by rw [q2]; exact hz40, Or.inl ⟨q0, q2⟩, fun hz => ⟨q0, q2, Or.inr ⟨hy, hr, ?_⟩, hmf _, hlf _⟩⟩
  obtain ⟨-, -, -, hz48⟩ := hzl (by omega)
  exact natVal_frame hF (by simp only [winA, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setZeroX (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (h7 : s.regs 7 = r) (hx0 : xl.toNat ≠ 0) (hy : y.toNat = 0) (hr : r.toNat = 0)
    (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, -, -, hro⟩, -, hx40, hz40, -, -, -, -, -, -, -, -,
    -⟩ := hpre'
  have hy0 : y = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  have hr0 : r = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  subst hy0 hr0
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  janus_run [hx0']
  refine post_setZero hpre hy hr ?hF ?_ ?_ ?_
  case hF => simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fullX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64)
    (hx0 : xl.toNat ≠ 0) (hxs : xl.toNat < 2 ^ 39) (hr : r.toNat = 0) :
    Summary (LibMulAddWW.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = y ∧ s.regs 7 = r ∧
        Pre R b L zp zc xp xl y r s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibMulAddWW.program.link impl) := by
    rw [LibMulAddWW.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibMulAddWW.names
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  by_cases hy0 : y.toNat = 0
  · exact setZeroX impl R b L zp zl zc xp xl xc y r s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 hx0 hy0 hr hpre
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact reuseX impl hap R b L zp zl zc xp xl xc y r s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 hx0 hy0 hz hpre
  · exact allocX impl hap R hmk' b L zp zl zc xp xl xc y r s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 hx0 hy0 hxs
      (by omega) hpre

/-- **`nat.mulAddWW`, exact-write variant** (arm64; `m ≥ 1`, `r = 0`, `m < 2^39`): `Post ∧ XQ` -/
theorem ensX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64)
    (hx0 : xl.toNat ≠ 0) (hxs : xl.toNat < 2 ^ 39) (hr : r.toNat = 0) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y, r]
      (Pre R b L zp zc xp xl y r) (fun s s' => Post R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s') := by
  janus_ensures_old [FvModexp.Arm64.MulAddWW.Pre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.MulAddWW.wordT, FvModexp.NatLive, FvModexp.Arm64.win, Janus.Spec.GuardOK, Janus.Spec.StackOK]
  rw [show names = LibMulAddWW.names from rfl, ← LibMulAddWW.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (fullX impl hap R hmk b L zp zl zc xp xl xc y r hx0 hxs hr) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.MulAddWW
