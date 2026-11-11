import FvModexp.Proofs.Arm64.Nat.LshFin
import FvModexp.Proofs.Arm64.Nat.Callees2
import FvModexp.Proofs.Common.DivmcBits

/-! # `nat.lsh` (arm64): shift path, pure memory facts after `lshVU` and `z[n] = carry` -/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh

abbrev callLsh : Nat := segAddr Extracted.program fn + 0x204

theorem and63 (sh : Nat) (hsh : sh < 2 ^ 64) : BitVec.ofNat 64 sh &&& 63#64 = BitVec.ofNat 64 (sh % 64) := by
  have e : sh &&& 63 = sh % 64 := Nat.and_two_pow_sub_one_eq_mod sh 6
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, e]
  omega

theorem carry_lt (X r n : Nat) (hX : X < 2 ^ (64 * n)) (hr : r < 64) : X * 2 ^ r / 2 ^ (64 * n) < 2 ^ 64 := by
  apply Nat.div_lt_of_lt_mul
  calc X * 2 ^ r < 2 ^ (64 * n) * 2 ^ r := Nat.mul_lt_mul_of_pos_right hX (Nat.two_pow_pos _)
    _ ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))

set_option maxRecDepth 20000 in
/-- memory facts after `lshVU` and `z[n] = carry` (pure) -/
theorem shift_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M C w : Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M C [(s.sp.toNat - 152, s.sp.toNat - 96), (s.sp.toNat - 80, s.sp.toNat - 72),
      (s.sp.toNat - 32, s.sp.toNat - 16)])
    (hQ1 : natVal w (p + 8 * (sh / 64)) xl = natVal C x xl * 2 ^ (sh % 64) % 2 ^ (64 * xl))
    (hQ2 : w.readLE (s.sp.toNat - 96) 8 = natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl))
    (hQ3 : MemFrame C w [(p + 8 * (sh / 64), p + 8 * (sh / 64) + 8 * xl), (s.sp.toNat - 96, s.sp.toNat - 88)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' w)) :
    MemFrame M (w.writeLE (p + 8 * (xl + sh / 64)) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl))) (R.rt ++ ws s p c) ∧ LiveFrame M (w.writeLE (p + 8 * (xl + sh / 64)) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl))) L' [(p, p + 8 * c)] ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' (w.writeLE (p + 8 * (xl + sh / 64)) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl)))) ∧
    natVal (w.writeLE (p + 8 * (xl + sh / 64)) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl))) (p + 8 * (sh / 64)) (xl + 1) = natVal s.mem x xl * 2 ^ (sh % 64) := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt
  simp only [need] at hcap
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hS : MemFrame w (w.writeLE (p + 8 * (xl + sh / 64)) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl))) [(p + 8 * (xl + sh / 64), p + 8 * (xl + sh / 64) + 8)] := by
    janus_frame
  have hA : MemFrame M w (R.rt ++ ws s p c) := hF.trans hQ3 fun a k ho => by
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2', h3'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩
  have hxC : natVal C x xl = natVal s.mem x xl := by
    simp only [natVal]
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact h.xr _ _ (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨hA.trans hS fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hS.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ3.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · exact inv_store_held hinv (h.pheld.sub (by omega) (by omega))
  · rw [show p + 8 * (xl + sh / 64) = p + 8 * (sh / 64) + 8 * xl by omega,
      natVal_store_top _ _ _ _ (carry_lt _ _ _ (natVal_lt _ _ _) (Nat.mod_lt _ (by decide))), hQ1, hxC,
      Nat.mod_add_div]


end FvModexp.Arm64.Lsh
