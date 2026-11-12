import FvModexp.Proofs.Arm64.Exp.P2DEnt
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.ExpBase
import FvModexp.Proofs.Common.GenReg

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the window dispatch run (odd `x`, `logM ≥ 2`, nat.go:960-966) (agent infra)

`winR`: from `oddE` (`0x1b5990`): `logM < 48` → window 2; else `bitLen y = 64 (len y - 1) + bitLen(top)` (smear +
`CLZ`, `BitLenA64.bl_exact`) `< 48` → window 2, else window 4. Exits: the window entries (`w2E = 0x1b6410`, return
`1792484`; `w4E = 0x1b5ba0`, return `1792468`) with every argument register kept.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

abbrev w2E : Nat := 1795088
abbrev w4E : Nat := 1792928
abbrev w2R : Nat := 1792484
abbrev w4R : Nat := 1792468

theorem bitLen_eq {x k : Nat} (hk : 0 < k) (h1 : 2 ^ (k - 1) ≤ x) (h2 : x < 2 ^ k) : Exp.bitLen x = k := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) h1
  have a := Exp.bitLen_le_of_lt h2
  have b := Exp.bitLen_lt hx
  rcases Nat.lt_or_ge (Exp.bitLen x) k with h | h
  · have : 2 ^ Exp.bitLen x ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · omega

theorem aux_bitLen_eq (w : Nat) : Aux.bitLen w = Exp.bitLen w := by
  unfold Aux.bitLen Exp.bitLen; rfl

/-- the bit length of a normalised nat from its top word -/
theorem bitLen_natVal (m : Memory) (p l : Nat) (h1 : 1 ≤ l) (hn : m.readLE (p + 8 * (l - 1)) 8 ≠ 0) :
    Exp.bitLen (natVal m p l) = 64 * (l - 1) + Aux.bitLen (m.readLE (p + 8 * (l - 1)) 8) := by
  have hlt := BitLenA64.natVal_lt_bl m p l h1
  have e := natVal_succ m p (l - 1)
  rw [Nat.sub_add_cancel h1] at e
  generalize hw : m.readLE (p + 8 * (l - 1)) 8 = w at *
  have hw0 : 0 < w := Nat.pos_of_ne_zero hn
  have hb := Exp.bitLen_ge hw0
  rw [aux_bitLen_eq] at hlt ⊢
  have hbp := Exp.bitLen_pos hw0
  refine bitLen_eq (by omega) ?_ hlt
  rw [e, show 64 * (l - 1) + Exp.bitLen w - 1 = 64 * (l - 1) + (Exp.bitLen w - 1) by omega, Nat.pow_add]
  have := Nat.mul_le_mul_left (2 ^ (64 * (l - 1))) hb
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem winR (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (yp yl lm w : Nat) (M : Memory)
    (hyl0 : 1 ≤ yl) (hyl : yl ≤ 2 ^ 9) (hlm : lm ≤ 2 ^ 13) (hyp : yp + 8 * yl ≤ 2 ^ 48)
    (hya : M.accessible (yp + 8 * (yl - 1)) 8 false = true) (hw : M.readLE (yp + 8 * (yl - 1)) 8 = w)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oddE) (h7 : S.regs 7 = BitVec.ofNat 64 yp)
    (h8 : S.regs 8 = BitVec.ofNat 64 yl) (h10 : S.regs 10 = BitVec.ofNat 64 lm) (hmem : S.mem = M)
    (K : ∀ (c : Nat), (c = w2E ∧ (lm < 48 ∨ 64 * (yl - 1) + Aux.bitLen w < 48) ∨
        c = w4E ∧ 48 ≤ lm ∧ 48 ≤ 64 * (yl - 1) + Aux.bitLen w) → ∀ S' : State, S'.pc = BitVec.ofNat 64 c →
      S'.sp = S.sp → (∀ i, i ≤ 10 → S'.regs i = S.regs i) → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.regs 30 = BitVec.ofNat 64 (if c = w2E then w2R else w4R) → S'.mem = M →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have ry : M.readLE (yp + (yl - 1) * 8) 8 = w := by rw [Nat.mul_comm]; exact hw
  have hya' : M.accessible (yp + (yl - 1) * 8) 8 false = true := by rw [Nat.mul_comm]; exact hya
  subst hmem
  have hw64 : w < 2 ^ 64 := by rw [← hw]; exact Memory.readLE_lt _ _ _
  janus_run [hw, ry, hya'] until [1792440, w2E]
  · exact K w2E (Or.inl ⟨rfl, Or.inl hbr⟩) _ rfl rfl (fun i hi => by simp only [setReg_apply, if_neg (show i ≠ 30 by omega)]) (by janus_simp)
      (by janus_simp) (by janus_simp) (by janus_simp) rfl
  gen_reg 12 as t with hT
  have hT' : BitLenA64.smearBV (BitVec.ofNat 64 w) = t := by rw [← hT, ← BitLenA64.smearBV]
  have hcl : clzNat 64 t.toNat = clzNat 64 w := by
    rw [← hT', BitLenA64.clz_smear, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw64]
  have hv := BitLenA64.bl_exact w yl hw64 hyl0 (by omega)
  have hb64 : Aux.bitLen w ≤ 64 := by
    rw [aux_bitLen_eq]; exact Exp.bitLen_le_of_lt hw64
  have hti : (64#64 - BitVec.ofNat 64 (clzNat 64 w) + (BitVec.ofNat 64 yl - 1#64) <<< 6).toInt =
      ((64 * (yl - 1) + Aux.bitLen w : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, hv, if_pos (by omega)]
  janus_run [hcl, hti] until [w2E, w4E]
  · exact K w2E (Or.inl ⟨rfl, Or.inr (by omega)⟩) _ rfl rfl
      (fun i hi => by simp only [setReg_apply, if_neg (show i ≠ 30 by omega), if_neg (show i ≠ 12 by omega),
        if_neg (show i ≠ 13 by omega), if_neg (show i ≠ 11 by omega)]) (by janus_simp)
      (by janus_simp) (by janus_simp) (by janus_simp) rfl
  · exact K w4E (Or.inr ⟨rfl, by omega, by omega⟩) _ rfl rfl
      (fun i hi => by simp only [setReg_apply, if_neg (show i ≠ 30 by omega), if_neg (show i ≠ 12 by omega),
        if_neg (show i ≠ 13 by omega), if_neg (show i ≠ 11 by omega)]) (by janus_simp)
      (by janus_simp) (by janus_simp) (by janus_simp) rfl

end FvModexp.Arm64.P2D
