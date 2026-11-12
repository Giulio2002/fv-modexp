import FvModexp.Proofs.Arm64.Exp.P2W2Cp3
import FvModexp.Proofs.Arm64.Exp.P2W2Ret1
import FvModexp.Proofs.Common.GenReg
import FvModexp.Proofs.Common.Util

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `bitLen(yi)` and `z = z.make(len powers[d])` (`blE = 0x1b66f4` → `CP`)
(agent infra)

`kk = (bitLen yi + 1)/2`, `k = kk - 1`, `d = yi >> 2k` (`< 4`, the `BCS` panic refuted), slots `160 := yi`,
`200 := kk`, `240 := k`, `208 := i`; `n = len powers[d]`; `cap z ≥ n` → reuse `z` (`ub_z`); else
`[168] := n`, `[304] := src` and `makeslice(Word, 1, 1)` (`n = 1`) / `makeslice(Word, n, n + 4)` (`[104] := n + 4`),
the result fresh (`ub_fresh`); then `cpC`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- `kk` of the first window -/
@[reducible] def kkOf (yi : Nat) : Nat := (Exp.bitLen yi + 1) / 2

theorem bitLen_pos (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : 1 ≤ Exp.bitLen yi ∧ Exp.bitLen yi ≤ 64 := by
  unfold Exp.bitLen
  rw [if_neg (by omega)]
  have := Nat.log2_lt (show yi ≠ 0 by omega) |>.2 h
  omega

theorem kk_facts (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) :
    1 ≤ kkOf yi ∧ kkOf yi ≤ 32 ∧ yi / 2 ^ ((kkOf yi - 1) * 2) < 4 := by
  have hb := bitLen_pos yi h0 h
  refine ⟨by unfold kkOf; omega, by unfold kkOf; omega, ?_⟩
  have h1 : yi < 2 ^ Exp.bitLen yi := by
    unfold Exp.bitLen; rw [if_neg (by omega)]; exact Nat.lt_log2_self
  have h2 : 2 ^ Exp.bitLen yi ≤ 2 ^ ((kkOf yi - 1) * 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by unfold kkOf; omega)
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm]; omega)

/-- (copied from expmc's `W2Pro.lsr1`) -/
theorem lsr1 (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (9223372036854775807#64)[i] = decide (i < 63) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 63
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

/-- (copied from expmc's `W2Pro.e23a`) -/
theorem e23a (k : Nat) (hk : k ≤ 31) : BitVec.ofNat 64 k + BitVec.ofNat 64 k = BitVec.ofNat 64 (k * 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- (copied from expmc's `W2Pro.ed`) -/
theorem ed (yi k : Nat) (h : yi < 2 ^ 64) :
    BitVec.ofNat 64 yi >>> (k * 2) = BitVec.ofNat 64 (yi / 2 ^ (k * 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem eKK (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) :
    (64#64 - BitVec.ofNat 64 (clzNat 64 yi) + 1#64) >>> 1 = BitVec.ofNat 64 (kkOf yi) := by
  have hc := Util.clz_bl 64 yi h
  have hb : Aux.bitLen yi = Exp.bitLen yi := rfl
  have := bitLen_pos yi h0 h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, kkOf]
  omega

/-- the table entries of an odd base are odd -/
theorem p2Pow_odd (L x d : Nat) (hL : 1 ≤ L) (hx : x % 2 = 1) : Exp.p2Pow L x d % 2 = 1 := by
  rw [(Exp.p2Pow_rep L x hL d).2]
  have h2 : 2 ∣ 2 ^ L := Nat.pow_dvd_pow_iff_le_right'.2 hL |> fun h => by simpa using h
  rw [Nat.mod_mod_of_dvd _ h2, Nat.pow_mod, hx, Nat.one_pow]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {ret : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp bp : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem blH {impl : List Segment} (hmv : MemmoveLive (LibExp.program.link impl) P2Pre.mvE 4096 R)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) mkE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {cst FV : Nat} {r29 : BitVec 64}
    (KL : ∀ kk, KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV)
    (hc : CPF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp)
    (S : State) (i yi : Nat) (hpc : S.pc = BitVec.ofNat 64 blE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h2 : S.regs 2 = BitVec.ofNat 64 lm) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 i)
    (h12 : S.regs 12 = BitVec.ofNat 64 yp) (h13 : S.regs 13 = BitVec.ofNat 64 yi) (hi : i < yl) (hyi0 : 0 < yi)
    (hyi : yi < 2 ^ 64) (hX : natVal s.mem xp xl % 2 = 1)
    (hbud : b + (kkOf yi - 1 + 32 * i) * bc sqC mlC (ℓL (stLen s.mem st) lm) lm + P2Pre.tC lm + P2Pre.tC lm ≤ b1 + cst)
    (htc : P2Pre.tC lm ≤ b1)
    (hFV : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i
      (yi * 2 ^ (64 - (kkOf yi - 1) * 2) % 2 ^ 64) (kkOf yi - 1)
      (Exp.p2Pow lm (natVal s.mem xp xl) (yi / 2 ^ ((kkOf yi - 1) * 2))) = FV) :
    ReachesRet (LibExp.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [hc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  subst hm
  obtain ⟨hk1, hk32, hd4⟩ := kk_facts yi hyi0 hyi
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e22 : BitVec.ofNat 64 (kkOf yi) - 1#64 = BitVec.ofNat 64 (kkOf yi - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h63 : (BitVec.ofNat 64 ((kkOf yi - 1) * 2)).getLsbD 63 = false := by
    show (BitVec.ofNat 64 ((kkOf yi - 1) * 2)).toNat.testBit 63 = false
    rw [BitVec.toNat_ofNat]; exact Nat.testBit_lt_two_pow (by omega)
  have hk4 : (kkOf yi - 1) * 2 % 18446744073709551616 = (kkOf yi - 1) * 2 := by omega
  have hk4' : (kkOf yi - 1) * 2 % 64 = (kkOf yi - 1) * 2 := by omega
  have hk64 : (kkOf yi - 1) * 2 < 64 := by omega
  have hdm : yi / 2 ^ ((kkOf yi - 1) * 2) % 18446744073709551616 = yi / 2 ^ ((kkOf yi - 1) * 2) :=
    Nat.mod_eq_of_lt (by omega)
  janus_run [hmacc, lsr1, eKK yi hyi0 hyi, e22, e23a _ (show kkOf yi - 1 ≤ 31 by omega), h63, hk4, hk4',
    ed yi _ hyi, hk64, hdm] until [1795888]
  generalize hM1 : (((S.mem.writeLE (sp + 160) 8 yi).writeLE (sp + 200) 8 (kkOf yi)).writeLE (sp + 240) 8
    (kkOf yi - 1)).writeLE (sp + 208) 8 i = M1
  have hF1 : MemFrame S.mem M1 [(sp + 160, sp + 168), (sp + 200, sp + 208), (sp + 240, sp + 248),
      (sp + 208, sp + 216)] := by rw [← hM1]; janus_frame
  have hc1 := CPF.stores hP hc hF1 (by rw [← hM1]; simp only [Memory.regions_writeLE]) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [StS] <;> omega)
  have q160 : M1.readLE (sp + 160) 8 = yi := by
    rw [← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]; omega
  have q200 : M1.readLE (sp + 200) 8 = kkOf yi := by
    rw [← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]; omega
  have q240 : M1.readLE (sp + 240) 8 = kkOf yi - 1 := by
    rw [← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]; omega
  have q208 : M1.readLE (sp + 208) 8 = i := by
    rw [← hM1, Memory.readLE_writeLE_self]; omega
  generalize hdd : yi / 2 ^ ((kkOf yi - 1) * 2) = d at hd4 hdm hFV ⊢
  obtain ⟨d0, d1, d2, d3, d4⟩ := hc1.tz.pw d hd4
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at d0 d1 d2 d3 d4
  generalize hn : M1.readLE (sp + 320 + 24 * d + 8) 8 = n at d2 d3 d4
  have eh1 : M1.readLE (sp + 320 + (8 * d + 2 * (8 * d))) 8 = bp + 8 * (d * W lm) := by
    rw [show 8 * d + 2 * (8 * d) = 24 * d by omega]; exact d0
  have eh2 : M1.readLE (sp + 320 + (8 * d + 2 * (8 * d)) + 8) 8 = n := by
    rw [show sp + 320 + (8 * d + 2 * (8 * d)) + 8 = sp + 320 + 24 * d + 8 by omega]; exact hn
  have hsl0 := hc1.esl
  obtain ⟨-, -, -, -, -, -, r472, r488, -⟩ := hsl0
  have hzc40 : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
  have t1 : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have t2 : (BitVec.ofNat 64 zc).toInt = (zc : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := p2Pow_odd lm (natVal s.mem xp xl) d (by have := hP.2.2.2.2.2.1; omega) hX
      rw [← d3, h0] at this; simp [natVal, Memory.readLE] at this
    · exact h0
  have hmacc1 : M1.accessible (sp - K) (K + 560) true = true := by
    rw [hc1.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hlpos : 0 < ℓL (stLen s.mem st) lm := by have := hP.2.2.2.2.2.1; simp only [ℓL, ℓZ, ℓR, W]; omega
  have hb48 := hc1.tz.bscr.b48
  have hjW : (d + 1) * W lm ≤ P2Pre.NB 4 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : d * W lm + W lm ≤ P2Pre.NB 4 lm := by rw [← Nat.succ_mul]; exact hjW
  have ha8 : allocCost 8 ≤ P2Pre.tC lm := by simp only [P2Pre.tC, makeCost, makeCap, allocCost]; split <;> omega
  have haW : allocCost (8 * (n + 4)) ≤ P2Pre.tC lm := by
    simp only [P2Pre.tC, makeCost, makeCap, allocCost]; split <;> omega
  janus_run [eh1, eh2, r472, r488, t1, t2, hmacc1] until [CP, mkE]
  rotate_right
  · -- reuse `z` (`n ≤ cap z`)
    have hnz : n ≤ zc := by omega
    refine cpC hmv ret0 Q hP (KL (kkOf yi)) hc1 (ub_z hP hc1.wc hc1.tz) hnz hn1 hd4 hn q160 q200 q240 q208 hk1 hk32
      hi hyi (by omega) hFV _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
  · -- `make(nat, 1)`
    have hn1' : n = 1 := by omega
    subst hn1'
    generalize hM2 : (M1.writeLE (sp + 168) 8 1).writeLE (sp + 304) 8 (bp + 8 * (d * W lm)) = M2
    have hF2 : MemFrame M1 M2 [(sp + 168, sp + 176), (sp + 304, sp + 312)] := by rw [← hM2]; janus_frame
    have hc2 := CPF.stores hP hc1 hF2 (by rw [← hM2]; simp only [Memory.regions_writeLE]) (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [StS] <;> omega)
    have k2 : ∀ a, (a + 8 ≤ sp + 168 ∨ (sp + 176 ≤ a ∧ a + 8 ≤ sp + 304) ∨ sp + 312 ≤ a) →
        M2.readLE a 8 = M1.readLE a 8 := fun a ha =>
      hF2.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have p168 : M2.readLE (sp + 168) 8 = 1 := by
      rw [← hM2, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    have p304 : M2.readLE (sp + 304) 8 = bp + 8 * (d * W lm) := by
      rw [← hM2, Memory.readLE_writeLE_self]; omega
    have hcost : blockSize (8 * 1) true ≤ b1 := by have := blockSize_le_allocCost 8 true; simp only [Nat.mul_one]; omega
    refine mkCall mkE_eq hmk _ _ hP hc2.wc (n := 1) (c := 1) (ra := 1795972) (by decide) (by decide) (by decide)
      (by decide) (by decide) hcost _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun ptr junk f v m ex ep hA => ?_)
    all_goals first | (janus_simp; done) | skip
    have hc3 := CPF.alloc hP hc2 hA
    have qk : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 560 → m.readLE a 8 = M2.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    have u200 : m.readLE (sp + 200) 8 = kkOf yi := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q200
    have u240 : m.readLE (sp + 240) 8 = kkOf yi - 1 := by
      rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q240
    have u208 : m.readLE (sp + 208) 8 = i := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q208
    have u160 : m.readLE (sp + 160) 8 = yi := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q160
    have u168 : m.readLE (sp + 168) 8 = 1 := by rw [qk _ (by omega) (by omega)]; exact p168
    have u304 : m.readLE (sp + 304) 8 = bp + 8 * (d * W lm) := by rw [qk _ (by omega) (by omega)]; exact p304
    have ulen : m.readLE (sp + 320 + 24 * d + 8) 8 = 1 := by
      rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact hn
    have hsl3 := hc3.esl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, u528, u536, u552, -⟩ := hsl3
    have hmacc3 : m.accessible (sp - K) (K + 560) true = true := by
      rw [hc3.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
    have hr8 : blockSize (8 * 1) true ≤ allocCost 8 := blockSize_le_allocCost _ _
    have hsz := hA.sz
    clear hc1 hF1 hF2 k2 hM1 hM2 q200 q240 q208 q160 p168 p304
    janus_run [u200, u240, u208, u160, u168, u304, u528, u536, u552, hmacc3] until [CP]
    refine cpC hmv ret0 Q hP (KL (kkOf yi)) hc3
      (ub_fresh hP hc2.wc hlpos hA hc2.tz (c := 1) (by decide) (by omega) (by decide)) (Nat.le_refl 1) (by decide)
      hd4 ulen u160 u200 u240 u208 hk1 hk32 hi hyi (by omega) hFV _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
  · -- `make(nat, n, n + 4)`
    have hn2 : n ≠ 1 := by omega
    have hn4 : (n + 4) % 18446744073709551616 = n + 4 := by omega
    generalize hM2 : ((M1.writeLE (sp + 168) 8 n).writeLE (sp + 304) 8 (bp + 8 * (d * W lm))).writeLE (sp + 104) 8
      (n + 4) = M2
    have e4 : BitVec.ofNat 64 n + 4#64 = BitVec.ofNat 64 (n + 4) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hF2 : MemFrame M1 M2 [(sp + 168, sp + 176), (sp + 304, sp + 312), (sp + 104, sp + 112)] := by
      rw [← hM2]; janus_frame
    have hc2 := CPF.stores hP hc1 hF2 (by rw [← hM2]; simp only [Memory.regions_writeLE]) (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [StS] <;> omega)
    have k2 : ∀ a, (sp + 112 ≤ a ∧ a + 8 ≤ sp + 168 ∨ (sp + 176 ≤ a ∧ a + 8 ≤ sp + 304) ∨ sp + 312 ≤ a) →
        M2.readLE a 8 = M1.readLE a 8 := fun a ha =>
      hF2.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have p168 : M2.readLE (sp + 168) 8 = n := by
      rw [← hM2, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self]; omega
    have p304 : M2.readLE (sp + 304) 8 = bp + 8 * (d * W lm) := by
      rw [← hM2, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]; omega
    have p104 : M2.readLE (sp + 104) 8 = n + 4 := by rw [← hM2, Memory.readLE_writeLE_self]; omega
    have hcost : blockSize (8 * (n + 4)) true ≤ b1 := by have := blockSize_le_allocCost (8 * (n + 4)) true; omega
    refine mkCall mkE_eq hmk _ _ hP hc2.wc (n := n) (c := n + 4) (ra := 1796044) (by omega) (by omega) (by omega)
      (by decide) (by decide) hcost _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun ptr junk f v m ex ep hA => ?_)
    all_goals first | (janus_simp [e4]; done) | skip
    have hc3 := CPF.alloc hP hc2 hA
    have qk : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 560 → m.readLE a 8 = M2.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    have u200 : m.readLE (sp + 200) 8 = kkOf yi := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q200
    have u240 : m.readLE (sp + 240) 8 = kkOf yi - 1 := by
      rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q240
    have u208 : m.readLE (sp + 208) 8 = i := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q208
    have u160 : m.readLE (sp + 160) 8 = yi := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact q160
    have u168 : m.readLE (sp + 168) 8 = n := by rw [qk _ (by omega) (by omega)]; exact p168
    have u304 : m.readLE (sp + 304) 8 = bp + 8 * (d * W lm) := by rw [qk _ (by omega) (by omega)]; exact p304
    have u104 : m.readLE (sp + 104) 8 = n + 4 := by rw [qk _ (by omega) (by omega)]; exact p104
    have ulen : m.readLE (sp + 320 + 24 * d + 8) 8 = n := by
      rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact hn
    have hsl3 := hc3.esl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, u528, u536, u552, -⟩ := hsl3
    have hmacc3 : m.accessible (sp - K) (K + 560) true = true := by
      rw [hc3.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
    have hr8 : blockSize (8 * (n + 4)) true ≤ allocCost (8 * (n + 4)) := blockSize_le_allocCost _ _
    have hsz := hA.sz
    clear hc1 hF1 hF2 k2 hM1 hM2 q200 q240 q208 q160 p168 p304 p104
    janus_run [u200, u240, u208, u160, u168, u304, u104, u528, u536, u552, hmacc3] until [CP]
    refine cpC hmv ret0 Q hP (KL (kkOf yi)) hc3
      (ub_fresh hP hc2.wc hlpos hA hc2.tz (c := n + 4) (by omega) (by omega) (by omega)) (by omega) hn1
      hd4 ulen u160 u200 u240 u208 hk1 hk32 hi hyi (by omega) hFV _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip

end

end FvModexp.Arm64.P2W2
