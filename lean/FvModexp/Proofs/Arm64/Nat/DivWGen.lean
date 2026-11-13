import FvModexp.Proofs.Arm64.Nat.DivWGenA1
import FvModexp.Proofs.Arm64.Nat.DivWGenAN

/-!
# `nat.divW` (arm64): the entry → `+0xbc` on the `divWVW` path (`y ∉ {0, 1}`, `m > 0`): `z.make(m)` reusing `z`
(`zc ≥ m`) or allocating (`makeslice(Word, 1, 1)` for `m = 1`, `makeslice(Word, m, m + 4)` else), then `call`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

set_option autoImplicit false

namespace FvModexp.Arm64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem genReuse (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (hx0 : 0 < xl.toNat) (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1)
    (hz : xl.toNat ≤ zc.toNat) (hpre : Pre R b L zp zc xp xl y s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, -, hx40, hz40, -, hzw', -, hxacc,
    hx48, -, -, hxw, -, -, -⟩ := hpre'
  replace hzw' := hzw' (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hx0; simp at hx0
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  janus_run [hx0', hy0', hy1'] until [hMid]
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  refine call impl hap R b L zp zc xp xl xc y s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).1 hy0 (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).2.1
    _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem genAlloc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDivW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (hx0 : 0 < xl.toNat) (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1)
    (hz : zc.toNat < xl.toNat) (hpre : Pre R b L zp zc xp xl y s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s' := by
  by_cases hm : xl.toNat = 1
  · exact genAlloc1 impl hap R hmk b L zp zl zc xp xl xc y s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hx0 hy0 hy1 hz hm hpre
  · exact genAllocN impl hap R hmk b L zp zl zc xp xl xc y s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hx0 hy0 hy1 hz hm hpre

end FvModexp.Arm64.DivW
