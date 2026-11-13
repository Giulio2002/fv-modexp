import FvModexp.Proofs.Arm64.Exp.ModInvPostS

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): loop round, `S4` → `z = z.lsh(z, 1)` → `S5` (agent infra)

`1797940`: `zz` spilled to `SP - 24 / - 128 / - 120`, `z` reloaded from its slots, `lsh` call, returns to `1797984`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL4 {J : Nat} {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) {kc : Nat} (hkc : 4608 ≤ kc)
    (hkL : stkL ≤ kc) (haL : aboveL ≤ 88) {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (k5 : S5 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1797984 (ExL3 s n J) eL kL) :
    S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1797940 (ExL3 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h1 h2 hv hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have hsp0 : 240 ≤ s.sp.toNat := by omega
  have r224 : S.mem.readLE (s.sp.toNat - 240 + 224) 8 = p := by
    rw [show s.sp.toNat - 240 + 224 = s.sp.toNat - 16 by omega]; exact hzs.1
  have r192 : S.mem.readLE (s.sp.toNat - 240 + 192) 8 = l := by
    rw [show s.sp.toNat - 240 + 192 = s.sp.toNat - 48 by omega]; exact hzs.2.1
  have r184 : S.mem.readLE (s.sp.toNat - 240 + 184) 8 = c := by
    rw [show s.sp.toNat - 240 + 184 = s.sp.toNat - 56 by omega]; exact hzs.2.2
  have hq64 : q < 2 ^ 64 := hmidB.h.2.2.2.1.2.1
  have hqc40 : qc < 2 ^ 40 := hmidB.h.2.2.2.1.1
  have hqlc : ql ≤ qc := hmidB.h.2.2.2.2.2.2.1
  have hlc : l ≤ c := hmidB.h.2.2.2.2.2.1
  obtain ⟨m3, hqs, hsl, hpw, hqw⟩ := store_zz hpreB.h hmidB.h hq64 (by omega) (by omega) hkc
  -- (s45) the budget fact at the memory after `zz`'s spills
  have ecZZ : stCap (memZZ s S.mem q ql qc) st = stCap S.mem st := by
    simp only [memZZ]
    rw [cap_slot hpreB.h _ (a := s.sp.toNat - 240 + 120) _ (by omega) (by omega),
      cap_slot hpreB.h _ (a := s.sp.toNat - 240 + 112) _ (by omega) (by omega),
      cap_slot hpreB.h _ (a := s.sp.toNat - 240 + 216) _ (by omega) (by omega)]
  rw [← stkR_congr ecZZ] at hb
  have hbB := Box.mk hb
  clear hb ecZZ
  unfold Goal
  janus_run [r224, r192, r184] until [1784560]
  refine callLsh hap hns hnf hls hkc hkL haL 220 (by decide) rfl k5 hpreB.h hn m3 hj1 hjn hbud hcong
    (fun M' h => ⟨slot_keep h hsp0 (by decide) (by decide) ((hsl _ (by omega)).trans hex.1), slot_keep h hsp0 (by decide) (by decide) ((hsl _ (by omega)).trans hex.2.1), hex.2.2⟩) hqs ((hpw l hlc).trans hzv) hl ((hqw ql hqlc).trans hv) (norm_keep hqw hqlc hnq) hql hbB.h _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus_simp

end FvModexp.Arm64.ModInv
