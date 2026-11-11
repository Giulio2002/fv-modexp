import FvModexp.Proofs.Arm64.Nat.MulAddWWMid

/-!
# `nat.mulAddWW` (arm64): the entry → `+0x7c` on the reuse path (`m ≠ 0`, `y ≠ 0`, `zc ≥ m + 1`), then `vww`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.MulAddWW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem reuse (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (h7 : s.regs 7 = r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hz : xl.toNat + 1 ≤ zc.toNat) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, hx40, hz40, -, hzw', -, hxacc,
    hx48, -, hxw, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus_run [hx0', hy0'] until [hMid]
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n (winA s 4208 72) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  refine vww impl hap R b L zp zc xp xl xc y r s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hl4 hl48 hz ?hF ?_ ?_ ?_ ?_) hx0 hy0
    (natVal_frame ?hF (hWo _ _ (by omega))) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals try janus_simp
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
end FvModexp.Arm64.MulAddWW
