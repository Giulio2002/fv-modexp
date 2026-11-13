import FvModexp.Proofs.Amd64.Exp.ModInvSeg2
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `J0` (`+0x7b`) → `JM` / `JA` (agent infra s54; twin of `Arm64/Exp/ModInvMake`)

```
+0x7b   LEAQ 0x3f(R10), DX; SARQ $0x3f, DX; SHRQ $0x3a, DX; LEAQ (R10)(DX*1), BX; LEAQ 0x3f(BX), BX   // n + 63
        TESTQ CX, CX; JEQ +0xad; … CMPQ R11, DX; JNE +0xad                // alias(z, x): false (Pre's Apart z x)
+0xad   spills stk, n, x, k0 (0x100 / 0x120 / 0x118 / 0x110 / 0x108 / 0x90(SP))
        SARQ $6, BX; MOVQ BX, 0x78(SP); LEAQ 1(BX), DX                     // numWords, numWords + 1
        CMPQ CX, DX; JLT +0xfa; JCC +0x1b6 (JM: reuse)
+0xfa   TESTQ BX, BX; JNE +0x154 (JA: makeslice(Word, numWords + 1, numWords + 5))
```
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem k0_lt (s : State) (xp xl n : Nat) : k0 s xp xl n < 2 ^ 64 := by
  unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make (impl : List Amd64.Segment) (R : RtInv)
    (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State)
    (kM : JM impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s)
    (kA : JA impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s) :
    J0 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S hpre hn hpc ⟨h4, h5, ⟨a14, afs, ax15, adf⟩, h0, h1, h7, h6, h8, h9, h10, h12, hF, hrg, hfw, r8, r40⟩
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, -, -, -, -, -, -⟩, -, -, hn1, hn2, -, hzp, hzc0, ⟨hzc40, hzlive, -⟩, hx0, hxc,
    hxc40, -, -, -, -, ⟨-, hx48⟩, hzx, -⟩ := hpre'
  simp only [K, A, regSP] at hw hb' ha
  obtain ⟨f1, f2⟩ := hfw
  unfold Goal
  have hn63 : (BitVec.ofNat 64 n + 63#64).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hna : ¬ xp + 8 * (xc - 1) = zp + 8 * (zc - 1) := by
    have ha2 := (hzlive hzc0).2.2.2; unfold Apart at hzx; omega
  have hk0 := k0_lt s xp xl n
  have hzl48 := (hzlive hzc0).2.2.2
  have hna' : (BitVec.ofNat 64 xp + BitVec.ofNat 64 xc <<< 3 - 8#64 -
      (BitVec.ofNat 64 zp + BitVec.ofNat 64 zc <<< 3 - 8#64) = 0#64) = False := by
    apply propext; constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat] at this
      unfold Apart at hzx; omega
    · exact False.elim
  have hnw : BitVec.sshiftRight (BitVec.ofNat 64 n + (BitVec.ofNat 64 n + 63#64) >>> 121 + 63#64) 6 =
      BitVec.ofNat 64 (NW n) := by
    have e0 : (BitVec.ofNat 64 n + 63#64) >>> 121 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp only [BitVec.toNat_ofNat]
      exact Nat.div_eq_of_lt (by omega)
    rw [e0, BitVec.add_zero, sshiftRight_small _ hn63]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    simp only [NW]; omega
  janus64_run [sshiftRight_small _ hn63, hna', hnw] until [0x5ea8c0 + 0xea]
  have hnwb : NW n + 1 < 2 ^ 40 := by simp only [NW]; omega
  by_cases hr : NW n + 1 ≤ zc
  · janus64_run [BitVec.msb_eq_decide, toInt_small (BitVec.ofNat 64 zc) (by rw [BitVec.toNat_ofNat]; omega),
      toInt_small (BitVec.ofNat 64 (NW n + 1)) (by rw [BitVec.toNat_ofNat]; omega), hr] until [0x5ea8c0 + 0x1b6]
    refine kM _ zp zc L (b + stkR H s.mem st) hpre hn ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (rt0 hpre ?hF ?hR).1 ?hbq (rt0 hpre ?hF ?hR).2 hr
    case hbq => rw [stkR_congr (rt0_cap hpre ?hF)]; omega
    case hF =>
      refine hF.trans (?_ : MemFrame S.mem _ (win s (K kc) A)) fun a k h => ⟨h, h⟩
      simp only [win, K, A]; janus_frame
    case hR => janus64_simp; exact hrg
    all_goals janus64_simp
    all_goals first | exact afs | exact a14 | exact ax15 | exact adf
  · have hr' : zc < NW n + 1 := by omega
    have hnw0 : (NW n = 0) = False := eq_false (by simp only [NW]; omega)
    janus64_run [BitVec.msb_eq_decide, toInt_small (BitVec.ofNat 64 zc) (by rw [BitVec.toNat_ofNat]; omega),
      toInt_small (BitVec.ofNat 64 (NW n + 1)) (by rw [BitVec.toNat_ofNat]; omega), hr, hnw0] until [0x5ea8c0 + 0x154]
    refine kA _ hpre hn hr' ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?hF ?hR
    case hF =>
      refine hF.trans (?_ : MemFrame S.mem _ (win s (K kc) A)) fun a k h => ⟨h, h⟩
      simp only [win, K, A]; janus_frame
    case hR => janus64_simp; exact hrg
    all_goals janus64_simp
    all_goals first | exact afs | exact a14 | exact ax15 | exact adf

end FvModexp.Amd64.ModInv
