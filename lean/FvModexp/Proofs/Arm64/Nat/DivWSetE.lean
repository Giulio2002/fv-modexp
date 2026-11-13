import FvModexp.Proofs.Arm64.Nat.DivWSetA1
import FvModexp.Proofs.Arm64.Nat.DivWSetAN

/-!
# `nat.divW` (arm64): the entry → `+0x174` on the `z.set(x)` path (`y = 1`, `m > 0`): `z.make(m)` reusing `z`
(`zc ≥ m`) or allocating (`makeslice(Word, 1, 1)` for `m = 1`, `makeslice(Word, m, m + 4)` else), then `setTail`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

set_option autoImplicit false

namespace FvModexp.Arm64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setPath (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDivW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = 1#64)
    (hx0 : 0 < xl.toNat) (hpre : Pre R b L zp zc xp xl 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl 1#64 s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, -, hx40, hz40, -, -, -, hxacc,
    hx48, hxh, -, hxw, hinv, hok, -⟩ := hpre'
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  by_cases hz : xl.toNat ≤ zc.toNat
  · clear hok
    janus_run until [hSet]
    refine setTail impl R hmv b L zp zc xp xl s zp.toNat zc.toNat L b _
      (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).1 (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).2.1
      (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).2.2 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · by_cases hm : xl.toNat = 1
    · exact setAlloc1 impl R hmk hmv b L zp zl zc xp xl xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hx0 hz hm hpre
    · exact setAllocN impl R hmk hmv b L zp zl zc xp xl xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hx0 hz hm hpre

end FvModexp.Arm64.DivW
