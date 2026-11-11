import FvModexp.Proofs.Arm64.Exp.ModInvPostM
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): final round, `S2` → `zz = zz.mul(stk, zz, x[:min(numWords, len x)])`
→ `S3` (agent infra)

`0x1b6ff4`: `k = min(numWords, len x)` (`CMP (n + 63) >> 6`, `CSEL LO`), `mul` call at `0x1b7020`, returns to
`0x1b7024`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF2 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHyp impl R ns stkM aboveM mlC) {kc : Nat}
    (hkc : 4608 ≤ kc) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88) {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hml : ∀ x y, mlC (stLen s.mem st) x y = mulC x y)
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (k3 : S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1798180 (ExF n) (eF n) (kF n)) :
    S2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1798132 (ExF n) (eF n) (kF n) := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h1 h2 hv hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have hfw := hmidB.h.1
  have hn2 : n ≤ 2 ^ 15 := hpreB.h.2.2.2.2.1
  have r288 : S.mem.readLE (s.sp.toNat - 240 + 288) 8 = xl := by
    rw [show s.sp.toNat - 240 + 288 = s.sp.toNat + 48 by omega]; exact hfw.2.2.2.1
  have r272 : S.mem.readLE (s.sp.toNat - 240 + 272) 8 = st := by
    rw [show s.sp.toNat - 240 + 272 = s.sp.toNat + 32 by omega]; exact hfw.2.1
  have r280 : S.mem.readLE (s.sp.toNat - 240 + 280) 8 = xp := by
    rw [show s.sp.toNat - 240 + 280 = s.sp.toNat + 40 by omega]; exact hfw.2.2.1
  have r296 : S.mem.readLE (s.sp.toNat - 240 + 296) 8 = xc := by
    rw [show s.sp.toNat - 240 + 296 = s.sp.toNat + 56 by omega]; exact hfw.2.2.2.2.1
  have r200 : S.mem.readLE (s.sp.toNat - 240 + 200) 8 = n + 63 := by
    rw [show s.sp.toNat - 240 + 200 = s.sp.toNat - 40 by omega]; exact hfw.2.2.2.2.2.2.1
  have r128 : S.mem.readLE (s.sp.toNat - 240 + 128) 8 = NW n := by
    rw [show s.sp.toNat - 240 + 128 = s.sp.toNat - 112 by omega]; exact hfw.2.2.2.2.2.2.2
  have hn63 : (BitVec.ofNat 64 (n + 63)).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat]; omega
  have h9a := asr_small_bv _ hn63 6 18158513697557839872#64 288230376151711743#64 ⟨by omega, by omega⟩ rfl
  have hnw : BitVec.ofNat 64 (n + 63) >>> 6 = BitVec.ofNat 64 (NW n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [NW]; omega
  have hss : ((BitVec.ofNat 64 (n + 63)).sshiftRight 6).toNat = NW n := by
    rw [BitVec.sshiftRight_eq_of_msb_false (by
      rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega)]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; simp only [NW]; omega
  have hxl : xl ≤ 2 ^ 12 := hpreB.h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsp0 : 240 ≤ s.sp.toNat := by omega
  clear hfw
  unfold Goal
  by_cases hc : xl < NW n
  · have hk : min (kF n j) xl = xl := Nat.min_eq_right (by simp only [kF]; omega)
    janus_run [r288, r272, r280, r296, r200, r128, h9a, hnw, hc] until [1814128]
    refine callMul hap hns hnf hmu hkc hkM haM hml hmm 269 (by decide) rfl k3 hpreB.h hn hmidB.h hj1 hjn hbud hcong
      (fun _ _ => hex) hzs hzv hl0 hl hv hql (by simp only [kF]; omega) (by simp only [kF, NW]; omega) hb _ ?_ ?_ ?_
      rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hk]; janus_simp; rw [hss]; simp [hc]) ?_
    all_goals janus_simp
  · have hk : min (kF n j) xl = NW n := Nat.min_eq_left (by simp only [kF]; omega)
    janus_run [r288, r272, r280, r296, r200, r128, h9a, hnw, hc] until [1814128]
    refine callMul hap hns hnf hmu hkc hkM haM hml hmm 269 (by decide) rfl k3 hpreB.h hn hmidB.h hj1 hjn hbud hcong
      (fun _ _ => hex) hzs hzv hl0 hl hv hql (by simp only [kF]; omega) (by simp only [kF, NW]; omega) hb _ ?_ ?_ ?_
      rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hk]; janus_simp; rw [hss]; simp [hc]) ?_
    all_goals janus_simp

end FvModexp.Arm64.ModInv
