import FvModexp.Proofs.Amd64.Nat.NatSubCont
import FvModexp.Proofs.Amd64.Nat.SubVW
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.BitLemmas

/-! # `nat.sub` (amd64): the entry → `+0x13d` on the reuse path (`0 < n ≤ m`, `zc ≥ m`), then `vv` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem reuseH (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) (hV : VVStmt impl hap R hmv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hz : xl.toNat ≤ zc.toNat) (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostX 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, -, -, -, -⟩, -, -, hge, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, hzw', -, hxacc, hx48, -, -, -, hxw, hyacc, hy48, -, hyw, -, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw hyw
  janus64_run [BitVec.msb_eq_decide, mod64_of_lt (xl.toNat + 1) (by omega),
    toInt_small (xl + 1#64) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] until [hMid]
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  refine hV b L zp zc xp xl xc yp yl yc s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hyx hra hx15 hdf hz (by omega) ?hF ?_ ?_ ?_ ?_ ?_ ?_) hyx hy0 hxc (by omega)
    (natVal_frame ?hF (hWo _ _ (by omega))) (natVal_frame ?hF (hWo _ _ (by omega)))
    (natVal_frame ?hF (hWo _ _ (by omega))) hge _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals janus64_simp

end FvModexp.Amd64.NatSub
