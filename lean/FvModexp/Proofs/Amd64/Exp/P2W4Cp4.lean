import FvModexp.Proofs.Amd64.Exp.P2W4Cp3
import FvModexp.Proofs.Amd64.Exp.P2W4Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `bitLen(yi)` from `blE` (fn+0x3eb) to the table lookup `TL` (agent divmc s77, port of divmc s71;
amd64 twin of the first part of agent infra's `Arm64.P2W4Cp4`)

`kk = (bitLen yi + 3)/4` (`BSRQ`/`CMOVE`), `k4 = 4kk - 4`, `d = yi >> k4 < 16` (the `JAE` panic refuted), the stores
`0xf8 := yi`, `0xf0 := kk`, `0xe8 := k4`, `0xd0 := i`, then `blH2`. The `kk = 1` case (shift count `0`) is split off.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- `(kk - 1) << 2` as `janus64_run` leaves it (`LEAQ -1(CX)`; `SHLQ $2`) -/
theorem ek4 (kk : Nat) (h1 : 1 ≤ kk) (h : kk ≤ 16) :
    (BitVec.ofNat 64 kk - 1#64) <<< 2 = BitVec.ofNat 64 ((kk - 1) * 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show kk < 2 ^ 64 by omega)]
  rw [show (2 ^ 64 - 1 % 2 ^ 64 + kk) % 2 ^ 64 = kk - 1 by omega]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp tp : Nat}

/-- the stores of the `bitLen` segment -/
@[reducible] def blSt (M0 : Memory) (sp yi kk i : Nat) : Memory :=
  (((M0.writeLE (sp + 0xf8) 8 yi).writeLE (sp + 0xf0) 8 kk).writeLE (sp + 0xe8) 8 ((kk - 1) * 4)).writeLE (sp + 0xd0) 8 i

set_option maxRecDepth 20000 in
/-- `blH2` from the stores of the `bitLen` segment -/
theorem blH3 {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (ret0 : W64) (Q : State → Prop) (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    {cst FV : Nat} {r5 : W64} {kk d i yi : Nat}
    (KL : KL impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV)
    (hc : CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 TL) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (h5 : S.regs 5 = r5) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) (hm : S.mem = blSt M sp yi kk i)
    (h15 : S.regs 15 = BitVec.ofNat 64 d) (hd4 : d < 16) (hk1 : 1 ≤ kk) (hk32 : kk ≤ 16)
    (hi : i < yl) (hyi : yi < 2 ^ 64) (hX : natVal s.mem xp xl % 2 = 1)
    (hbud : b + (kk - 1 + 16 * i) * bc lm + P2Pre.tC lm + P2Pre.tC lm ≤ b1 + cst)
    (htc : P2Pre.tC lm ≤ b1)
    (hFV : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i
      (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) (kk - 1) (Exp.p2Pow lm (natVal s.mem xp xl) d) = FV) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hil : i < 2 ^ 12 := by have := hP.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hF : MemFrame M (blSt M sp yi kk i) [(sp + 0xf8, sp + 0x100), (sp + 0xf0, sp + 0xf8), (sp + 0xe8, sp + 0xf0),
      (sp + 0xd0, sp + 0xd8)] := by simp only [blSt]; janus_frame
  have hc1 := CPF.stores hP hc hF (by simp only [blSt, Janus.Arm64.Memory.regions_writeLE]) (by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [StS] <;> omega)
  have q0e8 : (blSt M sp yi kk i).readLE (sp + 0xf8) 8 = yi := by
    simp only [blSt]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have q0c0 : (blSt M sp yi kk i).readLE (sp + 0xf0) 8 = kk := by
    simp only [blSt]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have q0f0 : (blSt M sp yi kk i).readLE (sp + 0xe8) 8 = (kk - 1) * 4 := by
    simp only [blSt]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have q0c8 : (blSt M sp yi kk i).readLE (sp + 0xd0) 8 = i := by
    simp only [blSt]; rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
  exact blH2 hmv hmk ret0 Q hP KL hc1 q0e8 q0c0 q0f0 q0c8 S hpc ⟨hsp, h14, h5, hx15, hfs, hdf, hm⟩ h15 hd4 hk1 hk32
    hi hyi hX hbud htc hFV

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from `bitLen` to the loop test** -/
theorem blH {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (ret0 : W64) (Q : State → Prop) (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    {cst FV : Nat} {r5 : W64}
    (KL : ∀ kk, KL impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV)
    (hc : CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    (S : State) (i yi : Nat) (hpc : S.rip = BitVec.ofNat 64 blE) (hKp : Kp sp g r5 s.fsBase false M S)
    (h0 : S.regs 0 = BitVec.ofNat 64 lm) (h12 : S.regs 12 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 i)
    (h13 : S.regs 13 = BitVec.ofNat 64 yp) (h15 : S.regs 15 = BitVec.ofNat 64 yi) (hi : i < yl) (hyi0 : 0 < yi)
    (hyi : yi < 2 ^ 64) (hX : natVal s.mem xp xl % 2 = 1)
    (hbud : b + (kkOf yi - 1 + 16 * i) * bc lm + P2Pre.tC lm + P2Pre.tC lm ≤ b1 + cst)
    (htc : P2Pre.tC lm ≤ b1)
    (hFV : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i
      (yi * 2 ^ (64 - (kkOf yi - 1) * 4) % 2 ^ 64) (kkOf yi - 1)
      (Exp.p2Pow lm (natVal s.mem xp xl) (yi / 2 ^ ((kkOf yi - 1) * 4))) = FV) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm⟩ := hKp
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := (hc.wc.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  obtain ⟨hk1, hk32, hd4⟩ := kk_facts yi hyi0 hyi
  have hyz : (yi = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
  have e1 := eKK yi hyi0 hyi
  generalize hKK : kkOf yi = kk at e1 hk1 hk32 hd4 hbud hFV
  have ek2 := ek4 kk hk1 hk32
  have hk2m : (kk - 1) * 4 % 64 = (kk - 1) * 4 := by omega
  have e4 := ed yi (kk - 1) hyi
  generalize hD : yi / 2 ^ ((kk - 1) * 4) = d at e4 hd4 hFV
  have hd4' : BitVec.ofNat 64 d < 16#64 := by simp only [BitVec.lt_def, BitVec.toNat_ofNat]; omega
  have hD0 : kk = 1 → d = yi := by intro h; subst h; rw [← hD]; simp
  have hwH : HdM (CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) := ⟨hc⟩
  clear hc
  subst hm
  by_cases hk1' : kk = 1
  · have e5 := hD0 hk1'
    subst hk1'
    refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 TL) ?_
    janus64_run [hwacc, hwaccF, hyz, e1, ek2, hk2m, e4, hd4'] until [TL]
    refine blH3 hmv hmk ret0 Q hP (KL 1) hwH.h (d := d) (i := i) (yi := yi) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hd4 (Nat.le_refl 1)
      (by decide) hi hyi hX hbud htc hFV
    all_goals first | exact hfs | (janus64_simp [e5]; done) | skip
  · have hz : ((kk - 1) * 4 = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 TL) ?_
    janus64_run [hwacc, hwaccF, hyz, e1, ek2, hk2m, e4, hd4', hz] until [TL]
    refine blH3 hmv hmk ret0 Q hP (KL kk) hwH.h (d := d) (i := i) (yi := yi) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hd4 hk1
      hk32 hi hyi hX hbud htc hFV
    all_goals first | exact hfs | (janus64_simp; done) | skip

end

end FvModexp.Amd64.P2W4
