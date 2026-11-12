import FvModexp.Proofs.Arm64.Exp.ModInvPostSub

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): loop round, `S5` → `z = z.subMod2N(z, zz, i·64)` → loop head `J2` at
`j + 1` (agent infra)

`0x1b6f60`: `zz` and `i·64` reloaded, `subMod2N` call at `0x1b6f7c`, returns to `0x1b6f80`; the spills reloaded into
`X3 … X9`, `X11 … X14`, `X0 = 2i`, then the loop head `0x1b6fb0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

theorem cost_mono {e n : Nat} (h : e ≤ n) : SubMod2N.cost e ≤ SubMod2N.cost n := by
  simp only [SubMod2N.cost, SubMod2N.wCost, SubMod2N.W, allocCost]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- after `subMod2N` returns (`0x1b6f80`): reload, the loop head at `j + 1` -/
theorem retL5 {impl : List Segment} {R : RtInv} {kc : Nat} (hkc : 4608 ≤ kc) {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} {j : Nat}
    (kJ : J2j impl R kc sqrC mulC b L zp zl zc st xp xl xc n s (j + 1))
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 : Nat} (s' : State)
    (hmid : Mid R kc L s zp zc st xp xl xc n s'.mem L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjlt : 2 ^ j < NW n) (hl : l ≤ NW n + 1) (hb : b - spent sqrC mulC n (j + 1) ≤ b1)
    (hcong : natVal s.mem xp xl * natVal s'.mem p l % 2 ^ (2 ^ (j + 1) * 32) = 1 % 2 ^ (2 ^ (j + 1) * 32))
    (hi : s'.mem.readLE (s.sp.toNat - 80) 8 = 2 ^ (j + 1)) (hqs : QS s s'.mem q ql qc)
    (hpc : s'.pc = BitVec.ofNat 64 1798016) (hsp : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 240))
    (h28 : s'.regs 28 = s.regs 28) (h18 : s'.regs 18 = s.regs 18)
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h1 : s'.regs 1 = BitVec.ofNat 64 l) (h2 : s'.regs 2 = BitVec.ofNat 64 c) :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  have hK := sp_K hpre
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : s'.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]; exact hw
  have hfw := hmid.1
  have r : ∀ d v, s'.mem.readLE (s.sp.toNat + d - 240) 8 = v → s'.mem.readLE (s.sp.toNat - 240 + d) 8 = v :=
    fun d v h => by rw [show s.sp.toNat - 240 + d = s.sp.toNat + d - 240 by omega]; exact h
  have r272 := r 272 st (by rw [show s.sp.toNat + 272 - 240 = s.sp.toNat + 32 by omega]; exact hfw.2.1)
  have r280 := r 280 xp (by rw [show s.sp.toNat + 280 - 240 = s.sp.toNat + 40 by omega]; exact hfw.2.2.1)
  have r288 := r 288 xl (by rw [show s.sp.toNat + 288 - 240 = s.sp.toNat + 48 by omega]; exact hfw.2.2.2.1)
  have r296 := r 296 xc (by rw [show s.sp.toNat + 296 - 240 = s.sp.toNat + 56 by omega]; exact hfw.2.2.2.2.1)
  have r304 := r 304 n (by rw [show s.sp.toNat + 304 - 240 = s.sp.toNat + 64 by omega]; exact hfw.2.2.2.2.2.1)
  have r200 := r 200 (n + 63) (by rw [show s.sp.toNat + 200 - 240 = s.sp.toNat - 40 by omega]; exact hfw.2.2.2.2.2.2.1)
  have r128 := r 128 (NW n) (by rw [show s.sp.toNat + 128 - 240 = s.sp.toNat - 112 by omega]; exact hfw.2.2.2.2.2.2.2)
  have r120 := r 120 qc (by rw [show s.sp.toNat + 120 - 240 = s.sp.toNat - 120 by omega]; exact hqs.2.2)
  have r112 := r 112 ql (by rw [show s.sp.toNat + 112 - 240 = s.sp.toNat - 128 by omega]; exact hqs.2.1)
  have r216 := r 216 q (by rw [show s.sp.toNat + 216 - 240 = s.sp.toNat - 24 by omega]; exact hqs.1)
  have r160 := r 160 (2 ^ (j + 1)) (by rw [show s.sp.toNat + 160 - 240 = s.sp.toNat - 80 by omega]; exact hi)
  clear r
  unfold Goal
  janus_run [r272, r280, r288, r296, r304, r200, r128, r120, r112, r216, r160] until [1798064]
  obtain ⟨-, hrt, hz, hzz, hap, hlc, hqlc, hnc, hqc⟩ := hmid
  refine kJ _ p l c q ql qc L1 b1 hpre hn rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrt hb hz hzz
    hnc hl hlc hqlc hqc (by omega) (by simpa using hjlt) hap hcong
  all_goals janus_simp

set_option maxHeartbeats 4000000 in
/-- the continuation after `subMod2N` (small context): value / length / budget facts, then `retL5` -/
theorem contL5 {J : Nat} {impl : List Segment} {R : RtInv} {kc : Nat} (hkc : 4608 ≤ kc) {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} {j : Nat}
    (kJ : J2j impl R kc sqrC mulC b L zp zl zc st xp xl xc n s (J + 1))
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {M : Memory} {p l c q ql qc Zv b1 : Nat}
    (hj1 : 1 ≤ j) (hex : ExL3 s n J j M) (hqs : QS s M q ql qc)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hv : natVal M p l = Zv * 2)
    (hvq : natVal M q ql = Zv * Zv % 2 ^ eL j * natVal s.mem xp (min (kL j) xl) % 2 ^ eL j)
    (hb : b - spent sqrC mulC n j - P5 sqrC mulC n ≤ b1)
    (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcm : SubMod2N.cost (2 ^ j * 64) ≤ SubMod2N.cost n)
    (s' : State) (l' : Nat) (L' : List (Nat × Nat)) (b' : Nat) (f0 : s'.pc = BitVec.ofNat 64 1798016)
    (f1 : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (f2 : s'.regs 28 = s.regs 28) (f4 : s'.regs 18 = s.regs 18)
    (g0 : s'.regs 0 = BitVec.ofNat 64 p) (g1 : s'.regs 1 = BitVec.ofNat 64 l') (g2 : s'.regs 2 = BitVec.ofNat 64 c)
    (mid2 : Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l' c q ql qc)
    (hv' : natVal s'.mem p l' = Exp.subMod2N (natVal M p l) (natVal M q ql) (2 ^ j * 64))
    (hn' : NatNorm s'.mem p l') (hbud' : b1 - SubMod2N.cost (2 ^ j * 64) ≤ b') (hsl : SlotsKept s M s'.mem) :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpre
  have hsp0 : 240 ≤ s.sp.toNat := by omega
  have hex1 := hex.1
  obtain ⟨-, -, hjlt, hJ⟩ := hex
  subst hJ
  have hcong' := round_step hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hcong
  simp only [eL, kL] at hvq
  rw [← hv, ← hvq, ← hv'] at hcong'
  have hvl : natVal s'.mem p l' < 2 ^ (64 * NW n) := by
    rw [hv']; exact Nat.lt_of_lt_of_le (Exp.subMod2N_spec _ _ _).1 (Nat.pow_le_pow_right (by omega) (by omega))
  refine retL5 hkc kJ hpre hn s' mid2 hj1 hjlt (by have := len_le hn' hvl; omega) ?_ hcong'
    (slot_keep hsl hsp0 (by decide) (by decide) hex1) (qs_keep hsl hsp0 hqs) f0 f1 f2 f4 g0 g1 g2
  rw [spent_succ _ _ _ _ hj1]; simp only [roundCost, P5, P4, P3, P2, P1] at hb hbud ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL5 {J : Nat} {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains SubMod2N.fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubMod2N.SubHypR impl R) (hadd : SubMod2N.AddHypR impl R) {kc : Nat} (hkc : 4608 ≤ kc)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat}
    {s : State} (kJ : J2j impl R kc sqrC mulC b L zp zl zc st xp xl xc n s (J + 1)) :
    S5 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797984 (ExL3 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hqs h0 h1 h2 hv hnz hl hvq hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have r216 : S.mem.readLE (s.sp.toNat - 240 + 216) 8 = q := by
    rw [show s.sp.toNat - 240 + 216 = s.sp.toNat - 24 by omega]; exact hqs.1
  have r112 : S.mem.readLE (s.sp.toNat - 240 + 112) 8 = ql := by
    rw [show s.sp.toNat - 240 + 112 = s.sp.toNat - 128 by omega]; exact hqs.2.1
  have r120 : S.mem.readLE (s.sp.toNat - 240 + 120) 8 = qc := by
    rw [show s.sp.toNat - 240 + 120 = s.sp.toNat - 120 by omega]; exact hqs.2.2
  have r176 : S.mem.readLE (s.sp.toNat - 240 + 176) 8 = 2 ^ j * 64 := by
    rw [show s.sp.toNat - 240 + 176 = s.sp.toNat - 64 by omega]; exact hex.2.1
  have hen : 2 ^ j * 64 ≤ n := by have := hex.2.2.1; simp only [NW] at this; omega
  have hcm := cost_mono hen
  have hbo : SubMod2N.cost (2 ^ j * 64) ≤ b1 :=
    bud_ok hb hbud (m := SubMod2N.cost n) (by simp only [roundCost, P5, P4, P3, P2, P1]; omega) hcm
  have hpre := hpreB.h
  have hK' := contL5 (c := c) hkc kJ hpre hn hj1 hex hqs hcong hv hvq hb hbud hcm
  clear hcong hv hvq hbud hcm hjn
  unfold Goal
  janus_run [r216, r112, r120, r176] until [1805584]
  refine callSub hap hns hnf hkT haT htr hsub hadd hkc hpre hmidB.h (e := 2 ^ j * 64)
    (by have := Nat.one_le_two_pow (n := j); omega) hen hl hql hnz hnq hbo
    (pcv := 1798016) ⟨by decide, by decide⟩ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun s' l' L' b' f0 f1 f2 f4 g0 g1 g2 mid2 hv' hn' _ _ hbud' hsl => hK' s' l' L' b' f0 f1 f2 f4 g0 g1 g2 mid2 hv' hn' hbud' hsl)
  all_goals janus_simp

end FvModexp.Arm64.ModInv
