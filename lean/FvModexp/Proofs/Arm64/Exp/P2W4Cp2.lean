import FvModexp.Proofs.Arm64.Exp.P2W4Cp1

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the first copy's `memmove` (`0x1b5fc0`) → the loop test `LT` (agent infra)

`cpM`: at the `memmove` contract entry (`dst = dp`, `src = powers[d]`, `8n` bytes; return `0x1b5fc4`) after the
spills `136/152/296` (`M → M1`): the call (`mvCallW`), the reloads, `yi <<= 64 - 2k` (`k = kk - 1`), `k--`, the
stores `200 := kk - 2`, `208 := i` and the continuation `KL` at `LT` with `li_first`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

/-- (copied from expmc's `W2Pro.e23`) -/
theorem e23 (k : Nat) (hk : k ≤ 15) : BitVec.ofNat 64 k <<< 2 = BitVec.ofNat 64 (k * 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- (window-4 form of expmc's `W2Pro.e20`) -/
theorem e20 (yi k : Nat) (hk : k ≤ 15) :
    (if 64 - k * 4 < 64 then BitVec.ofNat 64 (yi * 2 ^ ((64 - k * 4) % 64)) else 0#64) =
      BitVec.ofNat 64 (yi * 2 ^ (64 - k * 4) % 2 ^ 64) := by
  by_cases h0 : k = 0
  · subst h0; simp
  · rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
    apply BitVec.eq_of_toNat_eq; simp

theorem kk2 (kk : Nat) (h1 : 1 ≤ kk) (h : kk ≤ 16) : BitVec.ofNat 64 kk - 2#64 = BitVec.ofNat 64 (kk - 1) - 1#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cpM {impl : List Segment} (hmv : MemmoveLive (LibW.program.link impl) P2Pre.mvE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV ret : Nat} {r29 : BitVec 64}
    (KL : KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV)
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm))
    (hsl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st))
    (htz : TZ R L s.mem M L1 st sp zzp bp lm (natVal s.mem xp xl))
    (z280 : M.readLE (sp + 280) 8 = zzp) (z112 : M.readLE (sp + 112) 8 = 2 * W lm)
    (z120 : M.readLE (sp + 120) 8 = 2 * W lm) {dp dc n d i yi : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp bp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n) (hd : d < 16) (hZo : Exp.p2Pow lm (natVal s.mem xp xl) d % 2 = 1)
    (hlen : M.readLE (sp + 320 + 24 * d + 8) 8 = n)
    (s160 : M.readLE (sp + 160) 8 = yi) (s200 : M.readLE (sp + 200) 8 = kk) (s240 : M.readLE (sp + 240) 8 = kk - 1)
    (s208 : M.readLE (sp + 208) 8 = i) (hkk1 : 1 ≤ kk) (hkk : kk ≤ 16) (hi : i < yl) (hyi : yi < 2 ^ 64)
    (hbud : b + (kk - 1 + 16 * i) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm + P2Pre.tC lm ≤ b1 + cst)
    (hFV : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i
      (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) (kk - 1) (Exp.p2Pow lm (natVal s.mem xp xl) d) = FV)
    {M1 : Memory} (hF1 : MemFrame M M1 [(sp + 136, sp + 144), (sp + 152, sp + 160), (sp + 296, sp + 304)])
    (hrg1 : M1.regions = M.regions) (r136 : M1.readLE (sp + 136) 8 = n) (r152 : M1.readLE (sp + 152) 8 = dc)
    (r296 : M1.readLE (sp + 296) 8 = dp)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 P2Pre.mvE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = M1)
    (h0 : T.regs 0 = BitVec.ofNat 64 dp) (h1 : T.regs 1 = BitVec.ofNat 64 (bp + 8 * (d * W lm)))
    (h2 : T.regs 2 = BitVec.ofNat 64 (8 * n)) (h30 : T.regs 30 = BitVec.ofNat 64 1793988) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hdc0 : 0 < dc := by omega
  obtain ⟨-, hdH, hdacc, hd48⟩ := hub.live hdc0
  obtain ⟨hdW, -, -, -, -, -, hdB⟩ := hub.ap hdc0
  obtain ⟨-, -, d2, -, -⟩ := htz.pw d hd
  rw [hlen] at d2
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at d2
  have hjW : (d + 1) * W lm ≤ P2Pre.NB 16 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : d * W lm + W lm ≤ P2Pre.NB 16 lm := by rw [← Nat.succ_mul]; exact hjW
  have hbW := scr_win hP htz.bscr
  have hbs := htz.bscr
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  unfold Apart at hdW hbW hdB
  have hw1 := WC.win hP hw hF1 hrg1 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
  have k1 : ∀ a, (sp + 160 ≤ a ∧ a + 8 ≤ sp + 296 ∨ sp + 304 ≤ a ∧ a + 8 ≤ sp + 848 ∨ sp + 104 ≤ a ∧ a + 8 ≤ sp + 136) →
      M1.readLE a 8 = M.readLE a 8 := fun a ha =>
    hF1.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r816, r824, r840, -⟩ := hsl0
  have hsl784 : M.readLE (sp + 784) 8 = st := hsl.2.2.2.2.2.2.2.2.1
  refine mvCallW hmv ret0 Q hP hw1 (dst := dp) (src := bp + 8 * (d * W lm)) (n := 8 * n) (ra := 1793988)
    (by decide) (by decide) (by omega) (by omega)
    (by rw [hF1.accessible]; exact Memory.accessible_mono _ hdacc (Nat.le_refl _) (by omega))
    (hdH.sub (Nat.le_refl _) (by omega)) (by unfold Apart; omega) (by have := hbs.b48; omega)
    (by rw [hF1.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hbs.acc (by omega) (by omega)))
    (by unfold Apart; omega) T hpc hsp h28 hm h0 h1 h2 h30 fun junk f v m ex ep hF2 hLF2 hinv2 hcp hrg2 => ?_
  have km : ∀ a, (sp + 32 ≤ a ∧ a + 8 ≤ sp + 848) → m.readLE a 8 = M1.readLE a 8 := fun a ha =>
    mv_rdW hP hF2 (Or.inr ha) (by unfold Apart; omega)
  have q136 : m.readLE (sp + 136) 8 = n := by rw [km _ (by omega)]; exact r136
  have q152 : m.readLE (sp + 152) 8 = dc := by rw [km _ (by omega)]; exact r152
  have q296 : m.readLE (sp + 296) 8 = dp := by rw [km _ (by omega)]; exact r296
  have q840 : m.readLE (sp + 840) 8 = lm := by rw [km _ (by omega), k1 _ (by omega)]; exact r840
  have q824 : m.readLE (sp + 824) 8 = yl := by rw [km _ (by omega), k1 _ (by omega)]; exact r824
  have q816 : m.readLE (sp + 816) 8 = yp := by rw [km _ (by omega), k1 _ (by omega)]; exact r816
  have q784 : m.readLE (sp + 784) 8 = st := by rw [km _ (by omega), k1 _ (by omega)]; exact hsl784
  have q200 : m.readLE (sp + 200) 8 = kk := by rw [km _ (by omega), k1 _ (by omega)]; exact s200
  have q240 : m.readLE (sp + 240) 8 = kk - 1 := by rw [km _ (by omega), k1 _ (by omega)]; exact s240
  have q208 : m.readLE (sp + 208) 8 = i := by rw [km _ (by omega), k1 _ (by omega)]; exact s208
  have q160 : m.readLE (sp + 160) 8 = yi := by rw [km _ (by omega), k1 _ (by omega)]; exact s160
  have q112 : m.readLE (sp + 112) 8 = 2 * W lm := by rw [km _ (by omega), k1 _ (by omega)]; exact z112
  have q120 : m.readLE (sp + 120) 8 = 2 * W lm := by rw [km _ (by omega), k1 _ (by omega)]; exact z120
  have q280 : m.readLE (sp + 280) 8 = zzp := by rw [km _ (by omega), k1 _ (by omega)]; exact z280
  have hk : kk - 1 ≤ 15 := by omega
  have e64 : 64#64 - BitVec.ofNat 64 ((kk - 1) * 4) = BitVec.ofNat 64 (64 - (kk - 1) * 4) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h63b : (BitVec.ofNat 64 (64 - (kk - 1) * 4)).getLsbD 63 = false := by
    show (BitVec.ofNat 64 (64 - (kk - 1) * 4)).toNat.testBit 63 = false
    rw [BitVec.toNat_ofNat]; exact Nat.testBit_lt_two_pow (by omega)
  have hmacc : m.accessible (sp - K) (K + 848) true = true := by
    rw [hF2.accessible, hw1.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  clear hbs
  janus_run [q136, q152, q296, q840, q824, q816, q784, q200, q240, q208, q160, q112, q120, q280,
    e23 _ hk, e64, h63b, hmacc] until [LT]
  refine KL _ _ L1 b1 i (kk - 1) (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) _ dp n dc zzp (2 * W lm) (2 * W lm) true
    ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (li_first hP hw hsl htz hub hnd hn1 hd hZo hlen hF1 hrg1 hF2 hLF2 hinv2 hcp hrg2 ?F3 ?rg3 ?r200 ?r208)
    hi (Nat.mod_lt _ (by decide)) (by omega) (by simp only [true_iff]; omega) hbud hFV
  case F3 => janus_frame
  case rg3 => simp only [Memory.regions_writeLE]
  case r200 =>
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  case r208 => rw [Memory.readLE_writeLE_self]; omega
  all_goals first | (janus_simp [e20 yi _ hk, kk2 kk hkk1 hkk]; done) | skip

end

end FvModexp.Arm64.P2W4
