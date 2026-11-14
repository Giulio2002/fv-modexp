import FvModexp.Proofs.Amd64.Exp.P2W2Cp2
import FvModexp.Proofs.Amd64.Exp.P2W2Seg
import FvModexp.Proofs.Amd64.Exp.P2W2Sk
import FvModexp.Proofs.Common.Util

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): `bitLen(yi)` and `z = z.make(len powers[d])` (`blE` = fn+0x3d8 → `CP`)
(agent divmc s71; amd64 twin of agent infra's `Arm64.P2W2Cp4`)

`kk = (bitLen yi + 1)/2` (`BSRQ`/`CMOVE`, R10), `k2 = 2kk - 2` (CX), `d = yi >> k2` (`< 4`, the `JAE` panic +0x94a
refuted), slots `0xe8 := yi`, `0xc0 := kk`, `0xf0 := k2`, `0xc8 := i`; `n = len powers[d]` (SI), `src` (R15);
`cap z (0x200) ≥ n` → reuse `z` (`R9 = [0x1f0]`, `ub_z`) → `CP`; else `0xa0 := n`, `0x130 := src` and
`makeslice(Word, 1, 1)` (`n = 1`, CALL +0x48a) / `makeslice(Word, n, n + 4)` (`0x60 := n + 4`, CALL +0x500), the result
fresh (`ub_fresh`), reloads → `CP`; then `cpC`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

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

/-- the table entries of an odd base are odd -/
theorem p2Pow_odd (L x d : Nat) (hL : 1 ≤ L) (hx : x % 2 = 1) : Exp.p2Pow L x d % 2 = 1 := by
  rw [(Exp.p2Pow_rep L x hL d).2]
  have h2 : 2 ∣ 2 ^ L := Nat.pow_dvd_pow_iff_le_right'.2 hL |> fun h => by simpa using h
  rw [Nat.mod_mod_of_dvd _ h2, Nat.pow_mod, hx, Nat.one_pow]

theorem ed (yi k : Nat) (h : yi < 2 ^ 64) :
    BitVec.ofNat 64 yi >>> (k * 2) = BitVec.ofNat 64 (yi / 2 ^ (k * 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem eKK (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) :
    (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 yi) + 2#64) >>> 1 = BitVec.ofNat 64 (kkOf yi) := by
  have hc := Util.clz_bl 64 yi h
  have hb : Aux.bitLen yi = Exp.bitLen yi := rfl
  have := bitLen_pos yi h0 h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kkOf]
  omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp tp : Nat}

/-- the table-lookup point (fn+0x430, after the slot stores; `R15 = d`) -/
abbrev TL : Nat := 6201936

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the table lookup to the copy point**: `n = len powers[d]`, reuse `z` or `make` (see the module doc) -/
theorem blH2 {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (ret0 : W64) (Q : State → Prop) (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    {cst FV : Nat} {r5 : W64} {kk d i yi : Nat}
    (KL : KL impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV)
    (hc : CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    (s0e8 : M.readLE (sp + 0xe8) 8 = yi) (s0c0 : M.readLE (sp + 0xc0) 8 = kk)
    (s0f0 : M.readLE (sp + 0xf0) 8 = (kk - 1) * 2) (s0c8 : M.readLE (sp + 0xc8) 8 = i)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 TL) (hKp : Kp sp g r5 s.fsBase false M S)
    (h15 : S.regs 15 = BitVec.ofNat 64 d) (hd4 : d < 4) (hk1 : 1 ≤ kk) (hk32 : kk ≤ 32)
    (hi : i < yl) (hyi : yi < 2 ^ 64) (hX : natVal s.mem xp xl % 2 = 1)
    (hbud : b + (kk - 1 + 32 * i) * bc lm + P2Pre.tC lm + P2Pre.tC lm ≤ b1 + cst)
    (htc : P2Pre.tC lm ≤ b1)
    (hFV : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i
      (yi * 2 ^ (64 - (kk - 1) * 2) % 2 ^ 64) (kk - 1) (Exp.p2Pow lm (natVal s.mem xp xl) d) = FV) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm⟩ := hKp
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hlm := hP.2.2.2.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := (hc.wc.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  obtain ⟨d0, d1, d2, d3, d4⟩ := hc.tz.pw d hd4
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at d0 d1 d2 d3 d4
  generalize hn : M.readLE (sp + 0x140 + 24 * d + 8) 8 = n at d2 d3 d4
  have eh1 : M.readLE (sp + (d + d * 2) * 8 + 320) 8 = tp + 8 * (d * W lm) := by
    rw [show sp + (d + d * 2) * 8 + 320 = sp + 0x140 + 24 * d by omega]; exact d0
  have eh2 : M.readLE (sp + (d + d * 2) * 8 + 328) 8 = n := by
    rw [show sp + (d + d * 2) * 8 + 328 = sp + 0x140 + 24 * d + 8 by omega]; exact hn
  have hsl0 := hc.esl
  obtain ⟨-, -, -, -, -, -, r1f0, r200, -⟩ := hsl0
  have hzc40 : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have t1 : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have t2 : (BitVec.ofNat 64 zc).toInt = (zc : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := p2Pow_odd lm (natVal s.mem xp xl) d (by have := hP.2.2.2.2.1; omega) hX
      rw [← d3, h0] at this; simp [natVal, Janus.Arm64.Memory.readLE] at this
    · exact h0
  have hZo := p2Pow_odd lm (natVal s.mem xp xl) d (by have := hP.2.2.2.2.1; omega) hX
  have hlpos : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
  have hb48 := hc.tz.bscr.b48
  have hjW : (d + 1) * W lm ≤ P2Pre.NB 4 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : d * W lm + W lm ≤ P2Pre.NB 4 lm := by rw [← Nat.succ_mul]; exact hjW
  have ha8 : allocCost 8 ≤ P2Pre.tC lm := by simp only [P2Pre.tC, makeCost, makeCap, allocCost]; split <;> omega
  have haW : allocCost (8 * (n + 4)) ≤ P2Pre.tC lm := by
    simp only [P2Pre.tC, makeCost, makeCap, allocCost]; split <;> omega
  have hwH : HdM (CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) := ⟨hc⟩
  clear hc
  subst hm
  janus64_run [hwacc, hwaccF, eh1, eh2, r1f0, r200, t1, t2] until [CP, mkE]
  all_goals first
    | (-- reuse `z` (`n ≤ cap z`)
      refine cpC hmv ret0 Q hP KL hwH.h (ub_z hP hwH.h.wc hwH.h.tz) (by omega) hn1 hd4 hZo hn s0e8 s0c0 s0f0 s0c8
        hk1 hk32 hi hyi (by omega) hFV _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
      all_goals first | exact hfs | (janus64_simp; done))
    | skip
  all_goals by_cases hn1' : n = 1
  all_goals first | (exfalso; omega) | skip
  · -- `make(nat, 1)`
    subst hn1'
    have hF2 : MemFrame S.mem (((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031) [(sp + 0xa0, sp + 0xa8), (sp + 0x130, sp + 0x138), (sp - 8, sp)] := by janus_frame
    have hrg2 : (((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031).regions = S.mem.regions := by simp only [Janus.Arm64.Memory.regions_writeLE]
    have rpu : (((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031).readLE (sp - 8) 8 < 2 ^ 47 := by rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
    have rret : (((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031).readLE (sp - 8) 8 = 6202031 := Janus.Arm64.Memory.readLE_writeLE_self ..
    have p0a0 : (((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031).readLE (sp + 0xa0) 8 = 1 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    have p130 : (((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031).readLE (sp + 0x130) 8 = tp + 8 * (d * W lm) := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
      omega
    have hc2 := CPF.stores hP hwH.h hF2 hrg2 (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp only [StS] <;> omega)
    generalize hM2 : ((S.mem.writeLE (sp + 160) 8 1).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
        (sp - 8) 8 6202031 = M2 at hF2 hrg2 rpu rret p0a0 p130 hc2 ⊢
    have k2 : ∀ a, (a + 8 ≤ sp - 8 ∨ (sp ≤ a ∧ a + 8 ≤ sp + 0xa0) ∨ (sp + 0xa8 ≤ a ∧ a + 8 ≤ sp + 0x130) ∨
        sp + 0x138 ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a ha =>
      hF2.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hcost : blockSize (8 * 1) true ≤ b1 := by have := blockSize_le_allocCost 8 true; simp only [Nat.mul_one]; omega
    refine mkCall hmk hP hc2.wc (n := 1) (c := 1) (by decide) (by decide) (by decide) hcost _ ?_ ?_ ?_ ?_ rpu ?_ ?_ ?_
      (fun ptr junk f x yh m zh kr hA => ?_)
    all_goals first | (janus64_simp; done) | skip
    case refine_2 =>
      simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    have hc3 := CPF.alloc hP hc2 hA
    have qk : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 0x230 → m.readLE a 8 = M2.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    have u0f0 : m.readLE (sp + 0xf0) 8 = (kk - 1) * 2 := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0f0
    have u0e8 : m.readLE (sp + 0xe8) 8 = yi := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0e8
    have u0c0 : m.readLE (sp + 0xc0) 8 = kk := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0c0
    have u0c8 : m.readLE (sp + 0xc8) 8 = i := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0c8
    have u0a0 : m.readLE (sp + 0xa0) 8 = 1 := by rw [qk _ (by omega) (by omega)]; exact p0a0
    have u130 : m.readLE (sp + 0x130) 8 = tp + 8 * (d * W lm) := by rw [qk _ (by omega) (by omega)]; exact p130
    have ulen : m.readLE (sp + 0x140 + 24 * d + 8) 8 = 1 := by
      rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact hn
    have hsl3 := hc3.esl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, u1d8, u1e0, u228, -⟩ := hsl3
    have hwacc3 : m.accessible (sp - 8 - K) (K + 0x238) true = true := by
      rw [hA.macc, hF2.accessible]; exact hwacc
    have hwaccF3 : m.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc3
    have hr8 : blockSize (8 * 1) true ≤ allocCost 8 := blockSize_le_allocCost _ _
    have hsz := hA.sz
    have hpl := ptr.isLt
    have hub := ub_fresh hP hc2.wc hlpos hA hc2.tz (c := 1) (by decide) (by omega) (by decide)
    have hc3H : HdM (CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s m (L1 ++ [(ptr.toNat, ptr.toNat +
      blockSize (8 * 1) true)]) (b1 - blockSize (8 * 1) true) zzp tp) := ⟨hc3⟩
    clear hc3 hc2 hwH hF2 k2 hM2 hA qk
    refine SegProg.lift P2W2Seg.codeIn (r := BitVec.ofNat 64 CP) ?_
    janus64_run [u0f0, u0e8, u0c0, u0c8, u0a0, u130, u1d8, u1e0, u228, hwacc3, hwaccF3, rret] until [CP]
    refine cpC hmv ret0 Q hP KL hc3H.h hub (Nat.le_refl 1) (by decide) hd4 hZo ulen u0e8 u0c0 u0f0 u0c8 hk1 hk32
      hi hyi (by omega) hFV _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
    all_goals first | exact hfs | (janus64_simp; done) | skip
  all_goals (
      have hF2 : MemFrame S.mem ((((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8 (n + 4)).writeLE
          (sp - 8) 8 6202149)
          [(sp + 0xa0, sp + 0xa8), (sp + 0x130, sp + 0x138), (sp + 0x60, sp + 0x68), (sp - 8, sp)] := by janus_frame
      have hrg2 : ((((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8 (n + 4)).writeLE
          (sp - 8) 8 6202149).regions = S.mem.regions := by
        simp only [Janus.Arm64.Memory.regions_writeLE]
      have rpu : ((((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8 (n + 4)).writeLE
          (sp - 8) 8 6202149).readLE (sp - 8) 8 < 2 ^ 47 := by
        rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
      have rret : ((((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8 (n + 4)).writeLE
          (sp - 8) 8 6202149).readLE (sp - 8) 8 = 6202149 :=
        Janus.Arm64.Memory.readLE_writeLE_self ..
      have p0a0 : ((((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8 (n + 4)).writeLE
          (sp - 8) 8 6202149).readLE (sp + 0xa0) 8 = n := by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
      have p130 : ((((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8 (n + 4)).writeLE
          (sp - 8) 8 6202149).readLE (sp + 0x130) 8 = tp + 8 * (d * W lm) := by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
        omega
      have hc2 := CPF.stores hP hwH.h hF2 hrg2 (by
        intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> simp only [StS] <;> omega)
      generalize hM2 : (((S.mem.writeLE (sp + 160) 8 n).writeLE (sp + 304) 8 (tp + 8 * (d * W lm))).writeLE
          (sp + 96) 8           (n + 4)).writeLE (sp - 8) 8 6202149 = M2 at hF2 hrg2 rpu rret p0a0 p130 hc2 ⊢
      have p060 : M2.readLE (sp + 0x60) 8 = n + 4 := by
        rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
        omega
      have k2 : ∀ a, (a + 8 ≤ sp - 8 ∨ (sp ≤ a ∧ a + 8 ≤ sp + 0x60) ∨ (sp + 0x68 ≤ a ∧ a + 8 ≤ sp + 0xa0) ∨
          (sp + 0xa8 ≤ a ∧ a + 8 ≤ sp + 0x130) ∨
          sp + 0x138 ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a ha =>
        hF2.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
      have hcost : blockSize (8 * (n + 4)) true ≤ b1 := by have := blockSize_le_allocCost (8 * (n + 4)) true; omega
      have e4 : BitVec.ofNat 64 n + 4#64 = BitVec.ofNat 64 (n + 4) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine mkCall hmk hP hc2.wc (n := n) (c := n + 4) (by omega) (by omega) (by omega) hcost _ ?_ ?_ ?_ ?_
        rpu ?_ ?_ ?_
        (fun ptr junk f x yh m zh kr hA => ?_)
      all_goals first | (janus64_simp [e4]; done) | skip
      case refine_2 =>
        simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      have hc3 := CPF.alloc hP hc2 hA
      have qk : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 0x230 → m.readLE a 8 = M2.readLE a 8 := fun a h1 h2 =>
        hA.keep a 8 (Or.inr ⟨h1, h2⟩)
      have u0f0 : m.readLE (sp + 0xf0) 8 = (kk - 1) * 2 := by
        rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0f0
      have u0e8 : m.readLE (sp + 0xe8) 8 = yi := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0e8
      have u0c0 : m.readLE (sp + 0xc0) 8 = kk := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0c0
      have u0c8 : m.readLE (sp + 0xc8) 8 = i := by rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact s0c8
      have u0a0 : m.readLE (sp + 0xa0) 8 = n := by rw [qk _ (by omega) (by omega)]; exact p0a0
      have u060 : m.readLE (sp + 0x60) 8 = n + 4 := by rw [qk _ (by omega) (by omega)]; exact p060
      have u130 : m.readLE (sp + 0x130) 8 = tp + 8 * (d * W lm) := by rw [qk _ (by omega) (by omega)]; exact p130
      have ulen : m.readLE (sp + 0x140 + 24 * d + 8) 8 = n := by
        rw [qk _ (by omega) (by omega), k2 _ (by omega)]; exact hn
      have hsl3 := hc3.esl
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, u1d8, u1e0, u228, -⟩ := hsl3
      have hwacc3 : m.accessible (sp - 8 - K) (K + 0x238) true = true := by
        rw [hA.macc, hF2.accessible]; exact hwacc
      have hwaccF3 : m.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc3
      have hr8 : blockSize (8 * (n + 4)) true ≤ allocCost (8 * (n + 4)) := blockSize_le_allocCost _ _
      have hsz := hA.sz
      have hpl := ptr.isLt
      have hub := ub_fresh hP hc2.wc hlpos hA hc2.tz (c := n + 4) (by omega) (by omega) (by omega)
      have hc3H : HdM (CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s m (L1 ++ [(ptr.toNat, ptr.toNat +
        blockSize (8 * (n + 4)) true)]) (b1 - blockSize (8 * (n + 4)) true) zzp tp) := ⟨hc3⟩
      clear hc3 hc2 hwH hF2 k2 hM2 hA qk p060
      refine SegProg.lift P2W2Seg.codeIn (r := BitVec.ofNat 64 CP) ?_
      janus64_run [u0f0, u0e8, u0c0, u0c8, u0a0, u060, u130, u1d8, u1e0, u228, hwacc3, hwaccF3, rret] until [CP]
      refine cpC hmv ret0 Q hP KL hc3H.h hub (by omega) hn1 hd4 hZo ulen u0e8 u0c0 u0f0 u0c8 hk1 hk32
        hi hyi (by omega) hFV _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
      all_goals first | exact hfs | (janus64_simp; done) | skip
    )

end

end FvModexp.Amd64.P2W2
