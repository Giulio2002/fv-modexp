import FvModexp.Proofs.Arm64.Exp.ModInvPost

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): final round, `S3` → the second `zz = zz.trunc(zz, n)` → `S4` (agent infra)

`1798180`: `n` from `SP + 64`, `trunc` call, returns to `1798200`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF3 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) {kc : Nat} (hkc : 4608 ≤ kc)
    (hkT : stkT ≤ kc) (haT : aboveT ≤ 88) {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (k2 : S4 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1798200 (ExF n) (eF n) (kF n)) :
    S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1798180 (ExF n) (eF n) (kF n) := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h1 h2 hv hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have r304 : S.mem.readLE (s.sp.toNat - 240 + 304) 8 = n := by
    rw [show s.sp.toNat - 240 + 304 = s.sp.toNat + 64 by omega]; exact hmidB.h.1.2.2.2.2.2.1
  unfold Goal
  janus_run [r304] until [1786000]
  refine callT2 hap hns hnf htr hkc hkT haT 274 (by decide) rfl k2 hpreB.h hn hmidB.h hj1 hjn hbud hcong
    (fun _ _ => hex) hzs hzv hl0 hl hv hnq hql hb ?_ _ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus_simp
  simp only [eF, NW]; omega

end FvModexp.Arm64.ModInv
