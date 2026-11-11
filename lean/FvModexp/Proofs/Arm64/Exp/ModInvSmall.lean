import FvModexp.Proofs.Arm64.Exp.ModInvSeg
import FvModexp.Proofs.Common.GenReg
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `n ≤ 64` (nat.go:1301-1304) (agent infra)

`k0 &= (1 << n) - 1; return z.setWord(k0)`: `z[:0]` when the masked `k0` is zero, else `z.make(1)` (`z[:1]`, or
`makeslice(Word, 1, 1)` when `cap z = 0`) with `z[0] = k0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-- the mask `k0 & ((1 << n) - 1)` for `1 ≤ n ≤ 64` (`CSEL LO` picks `0` for `n = 64`) -/
theorem mask_eq (k n : Nat) (hk : k < 2 ^ 64) (hn1 : 1 ≤ n) (hn : n ≤ 64) :
    (BitVec.ofNat 64 k &&& (if n < 64 then BitVec.ofNat 64 (2 ^ (n % 64)) else 0#64) - 1#64).toNat = k % 2 ^ n := by
  rw [BitVec.toNat_and]
  have hm : ((if n < 64 then BitVec.ofNat 64 (2 ^ (n % 64)) else 0#64) - 1#64).toNat = 2 ^ n - 1 := by
    split
    · rename_i h
      have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) h
      have h2 := Nat.one_le_two_pow (n := n)
      rw [Nat.mod_eq_of_lt h, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · rename_i h
      rw [show n = 64 by omega]; rfl
  rw [hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.and_two_pow_sub_one_eq_mod]

theorem small (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4608 ≤ kc) :
    JS impl R kc sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S hpre hs hpc hsp h28 h18 h0 h2 h7 h10 hF hrg hfw
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgrt, hLs, hro⟩, hsv, -, hn1, hn2, hzl, hzp, ⟨hzc40, hzlive, hzw⟩,
    -⟩ := hpre'
  simp only [K, A] at hw hout hb' ha hga
  rw [show (1797104 + 0x64 : Nat) = 1797204 from rfl] at hpc
  obtain ⟨f1, f2⟩ := hfw
  unfold Goal
  janus_run [hs] until [1797736]
  gen_reg 3 as m with hm
  have hk0 : k0 s xp xl n < 2 ^ 64 := by
    unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
  have hmv : m.toNat = k0 s xp xl n % 2 ^ n := by rw [← hm]; exact mask_eq _ n hk0 hn1 hs
  clear hm
  by_cases hv : k0 s xp xl n % 2 ^ n = 0
  · have hm0 : m = 0#64 := by apply BitVec.eq_of_toNat_eq; rw [hmv, hv]; rfl
    janus_run [hm0, f1, f2]
    trace_state
    sorry
  · sorry

end FvModexp.Arm64.ModInv
