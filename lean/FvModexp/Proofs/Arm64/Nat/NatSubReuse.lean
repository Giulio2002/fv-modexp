import FvModexp.Proofs.Arm64.Nat.NatSubVV

/-!
# `nat.sub` (arm64): the entry → `+0xd8` on the reuse path (`0 < n ≤ m`, `zc ≥ m`), then `vv`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem reuse (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = yp)
    (h7 : s.regs 7 = yl) (h8 : s.regs 8 = yc) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hz : xl.toNat ≤ zc.toNat) (hpre : PreS 4304 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, -, hge, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, hzw', -, hxacc, hx48, -, -, -, hxw, hyacc, hy48, -, hyw, -, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw hyw
  janus_run until [hMid]
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  refine vv impl hap R hmv b L zp zc xp xl xc yp yl yc s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hyx hl4 hl48 hz (by omega) ?hF ?_ ?_ ?_ ?_ ?_ ?_) hyx hy0 hxc (by omega)
    (natVal_frame ?hF (hWo _ _ (by omega))) (natVal_frame ?hF (hWo _ _ (by omega)))
    (natVal_frame ?hF (hWo _ _ (by omega))) hge _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals janus_simp

end FvModexp.Arm64.NatSub
