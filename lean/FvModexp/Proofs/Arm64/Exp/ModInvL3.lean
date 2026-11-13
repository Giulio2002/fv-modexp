import FvModexp.Proofs.Arm64.Exp.ModInvPost

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): loop round, `S3` → `zz = zz.trunc(zz, i·64)` → `S4` (agent infra)

`0x1b6f20`: `trunc` call at `0x1b6f30` (`i·64` from `SP - 64`), returns to `0x1b6f34`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL3 {J : Nat} {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) {kc : Nat} (hkc : 4608 ≤ kc)
    (hkT : stkT ≤ kc) (haT : aboveT ≤ 88) {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (k4 : S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1797940 (ExL3 s n J) eL kL) :
    S3 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1797920 (ExL3 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h1 h2 hv hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have hi64 : S.mem.readLE (s.sp.toNat - 240 + 176) 8 = 2 ^ j * 64 := by
    rw [show s.sp.toNat - 240 + 176 = s.sp.toNat - 64 by omega]; exact hex.2.1
  have hsp0 : 240 ≤ s.sp.toNat := by omega
  unfold Goal
  janus_run [hi64] until [1786000]
  refine callT2 hap hns hnf htr hkc hkT haT 209 (by decide) rfl k4 hpreB.h hn hmidB.h hj1 hjn hbud hcong
    (fun M' h => ⟨slot_keep h hsp0 (by decide) (by decide) hex.1, slot_keep h hsp0 (by decide) (by decide) hex.2.1,
      hex.2.2⟩) hzs hzv hl0 hl hv hnq hql hb ?_ _ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus_simp
  have := hex.2.2.1
  simp only [eL]; omega

end FvModexp.Arm64.ModInv
