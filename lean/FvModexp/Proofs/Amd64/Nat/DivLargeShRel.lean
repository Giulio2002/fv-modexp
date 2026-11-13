import FvModexp.Proofs.Amd64.Nat.DivLargeCpRel
import FvModexp.Proofs.Amd64.Nat.DivLargeCallees
import FvModexp.Proofs.Common.DivLargeMath
import FvModexp.Proofs.Common.SetBytesMath

set_option autoImplicit false

/-!
# `divLarge` (amd64): the shift path's relations (`shift ≠ 0`, natdiv.go:614-616; pure)

`AtS1`: after `lshVU(v, vIn, shift)` (`fn + 0x37c`, `XORPS X15, X15`): `v` (at `t`) = `vIn · 2^shift` (normalised).
`AtS2`: after `lshVU(u[:il], uIn, shift)` (`fn + 0x3e6`): `u[:il] = uIn · 2^shift mod 2^(64 il)`, the carry in the
ABI0 result word `RSP - 248` (`0x38(SP')`). `sh_val`: the scaled divisor's value and top word.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivLarge

/-- the return of the first `lshVU.abi0` (`fn + 0x37c`) -/
abbrev shRet1 : Nat := segAddr Extracted.program fn + 0x37c

/-- the return of the second `lshVU.abi0` (`fn + 0x3e6`) -/
abbrev shRet2 : Nat := segAddr Extracted.program fn + 0x3e6

/-- `ADDQ $-0x3f, DX; NEGQ DX` on `DX = 63 - sh`: `DX = sh` -/
theorem dx_sh (sh : Nat) (h0 : 1 ≤ sh) (h : sh ≤ 63) :
    -(BitVec.ofNat 64 (63 - sh) + 18446744073709551553#64) = BitVec.ofNat 64 sh := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  have e1 : (63 - sh) % 18446744073709551616 = 63 - sh := Nat.mod_eq_of_lt (by omega)
  have e2 : (18446744073709551553 : Nat) % 18446744073709551616 = 18446744073709551553 := rfl
  have e3 : (63 - sh + 18446744073709551553) % 18446744073709551616 = 18446744073709551616 - sh := by
    rw [show 63 - sh + 18446744073709551553 = 18446744073709551616 - sh by omega]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, Nat.mod_eq_of_lt (show sh < 18446744073709551616 by omega),
    show 18446744073709551616 - (18446744073709551616 - sh) = sh by omega]
  exact Nat.mod_eq_of_lt (by omega)

/-- the top word of a nat from its value (copy of the arm64 lemma) -/
theorem top_of_natVal (m : Janus.Arm64.Memory) (p n : Nat) (hn : 1 ≤ n) :
    m.readLE (p + 8 * (n - 1)) 8 = natVal m p n / 2 ^ (64 * (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [natVal_succ]
  have hlo : natVal m p k < 2 ^ (64 * k) := by
    unfold natVal; have := Janus.Arm64.Memory.readLE_lt m p (8 * k)
    rw [show (256 : Nat) ^ (8 * k) = 2 ^ (64 * k) by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this
    exact this
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.zero_add]

/-- the scaled divisor (pure): `lshVU`'s value `V·2^sh mod 2^(64 n)` is `V·2^sh`, its top word `≥ 2^63` -/
theorem sh_val (m0 m : Janus.Arm64.Memory) (vp t vl sh : Nat) (hv2 : 2 ≤ vl)
    (hvn : m0.readLE (vp + 8 * (vl - 1)) 8 ≠ 0) (hsh : Janus.Arm64.clzNat 64 (m0.readLE (vp + 8 * (vl - 1)) 8) = sh)
    (hq : natVal m t vl = natVal m0 vp vl * 2 ^ sh % 2 ^ (64 * vl)) :
    natVal m t vl = natVal m0 vp vl * 2 ^ sh ∧ 2 ^ 63 ≤ m.readLE (t + 8 * (vl - 1)) 8 := by
  have hsv := natVal_succ m0 vp (vl - 1)
  rw [show vl - 1 + 1 = vl by omega] at hsv
  have hlo : natVal m0 vp (vl - 1) < 2 ^ (64 * (vl - 1)) := by
    unfold natVal
    have := Janus.Arm64.Memory.readLE_lt m0 vp (8 * (vl - 1))
    rw [show (256 : Nat) ^ (8 * (vl - 1)) = 2 ^ (64 * (vl - 1)) by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this
    exact this
  obtain ⟨hsc1, hsc2⟩ := DivLargeMath.scale_v (natVal m0 vp (vl - 1)) (m0.readLE (vp + 8 * (vl - 1)) 8) (vl - 1)
    hlo hvn (Janus.Arm64.Memory.readLE_lt _ _ _)
  rw [← hsv, hsh, show vl - 1 + 1 = vl by omega] at hsc1
  rw [← hsv, hsh] at hsc2
  have hT : natVal m t vl = natVal m0 vp vl * 2 ^ sh := by rw [hq, Nat.mod_eq_of_lt hsc1]
  exact ⟨hT, by rw [top_of_natVal _ _ _ (by omega), hT]; exact hsc2⟩

/-- after `lshVU(v, vIn, shift)` (`shRet1`) -/
structure AtS1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat) (S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 shRet1
  sp : S.regs 4 = s.regs 4 - 304#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  fs : S.fsBase = s.fsBase
  df : S.df = false
  mem : MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C sh S.mem
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C S.mem
  ext2 : LiveExt R L1 Lk
  bud2 : b1 - makeCost (il + 1) ≤ bk
  sh1 : 1 ≤ sh
  sh63 : sh ≤ 63
  vval : natVal S.mem t vl = natVal s.mem vp vl * 2 ^ sh
  vtop : 2 ^ 63 ≤ S.mem.readLE (t + 8 * (vl - 1)) 8
  is : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S.mem.readLE a n = s.mem.readLE a n
  reg : S.mem.regions = s.mem.regions

/-- after `lshVU(u[:il], uIn, shift)` (`shRet2`): `u[:il]` and the carry (`RSP - 248`) -/
structure AtS2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat) (S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 shRet2
  sp : S.regs 4 = s.regs 4 - 304#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  fs : S.fsBase = s.fsBase
  df : S.df = false
  mem : MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C sh S.mem
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C S.mem
  ext2 : LiveExt R L1 Lk
  bud2 : b1 - makeCost (il + 1) ≤ bk
  sh1 : 1 ≤ sh
  sh63 : sh ≤ 63
  vval : natVal S.mem t vl = natVal s.mem vp vl * 2 ^ sh
  vtop : 2 ^ 63 ≤ S.mem.readLE (t + 8 * (vl - 1)) 8
  uval : natVal S.mem P il = natVal s.mem ip il * 2 ^ sh % 2 ^ (64 * il)
  cy : S.mem.readLE ((s.regs 4).toNat - 248) 8 = natVal s.mem ip il * 2 ^ sh / 2 ^ (64 * il)
  reg : S.mem.regions = s.mem.regions

end FvModexp.Amd64.DivLarge
