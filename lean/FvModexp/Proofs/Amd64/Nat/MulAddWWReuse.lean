import FvModexp.Proofs.Amd64.Nat.MulAddWWMid
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.mulAddWW` (amd64): the entry → `+0xae` on the reuse path (`m ≠ 0`, `y ≠ 0`, `zc ≥ m + 1`), then `vww`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.MulAddWW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem reuse (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hz : xl.toNat + 1 ≤ zc.toNat) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, -, -, -, -⟩, -, hx40, hz40, -, hzw', -, hxacc, hx48, -, hxw, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus64_run [hx0', hy0', BitVec.msb_eq_decide, mod64_of_lt (a := xl.toNat + 1) (by omega),
    toInt_small (xl + 1#64) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] until [hMid]
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n (win s 4208 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  refine vww impl hap R b L zp zc xp xl xc y r s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hra hx15 hdf hz ?hF ?_ ?_ ?_ ?_) hx0 hy0
    (natVal_frame ?hF (hWo _ _ (by omega))) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)

end FvModexp.Amd64.MulAddWW
