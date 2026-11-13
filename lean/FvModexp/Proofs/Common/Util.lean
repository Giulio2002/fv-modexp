-- adapted from fv-uint256 lean/Fv256/Proofs/Common/Util.lean
import Janus
import FvModexp.Proofs.Common.Spec
import FvModexp.Proofs.Common.UtilDefs

open Lean Elab Tactic Meta in
/-- collect the propositions `p` of every `(decide p).toNat` in an expression -/
partial def collectDecToNat (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app f a =>
    let acc := collectDecToNat f (collectDecToNat a acc)
    if e.isAppOfArity ``Bool.toNat 1 then
      match a.getAppFnArgs with
      | (``Decidable.decide, #[p, _]) => if acc.contains p then acc else acc.push p
      | _ => acc
    else acc
  | .lam _ t b _ | .forallE _ t b _ => collectDecToNat b (collectDecToNat t acc)
  | .mdata _ b => collectDecToNat b acc
  | _ => acc

/-! Shared lemmas: the 256-bit value at a pointer as four 64-bit limbs, and bitwise operations limb by limb. -/

namespace FvModexp.Util

theorem readLE_32 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

theorem or_split (k a b c d : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * c) ||| (b + 2 ^ k * d) = (a ||| b) + 2 ^ k * (c ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hab : a ||| b < 2 ^ k := Nat.or_lt_two_pow ha hb
  rw [Nat.testBit_or, Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a ||| b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hab]
  by_cases h : i < k
  · simp [h, Nat.testBit_or]
  · simp [h, Nat.testBit_or]

theorem readLE8_lt (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 8 < 18446744073709551616 := by
  simpa using Janus.Arm64.Memory.readLE_lt m a 8

@[simp] theorem readLE8_mod (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 8 % 18446744073709551616 = m.readLE a 8 := Nat.mod_eq_of_lt (readLE8_lt m a)

theorem dec_toNat (p : Prop) [Decidable p] :
    ((decide p).toNat = 1 ∧ p) ∨ ((decide p).toNat = 0 ∧ ¬ p) := by
  by_cases h : p <;> simp [h]

open Janus.Amd64 in
open Lean Elab Tactic Meta in
/-- For every `(decide p).toNat` in the goal add the fact `dec_toNat p` (the value is 1 and `p`, or 0 and `¬p`), so that
`omega` can reason about carries without a case split. -/
elab "dec_facts" : tactic => withMainContext do
  let mut ps := collectDecToNat (← instantiateMVars (← getMainTarget)) #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then ps := collectDecToNat (← instantiateMVars d.type) ps
  for p in ps do
    evalTactic (← `(tactic| have := FvModexp.Util.dec_toNat $(← Term.exprToSyntax p)))

open Lean Elab Tactic Meta in
/-- Like `dec_facts` but only for the goal (not the hypotheses). -/
elab "dec_goal" : tactic => withMainContext do
  let ps := collectDecToNat (← instantiateMVars (← getMainTarget)) #[]
  for p in ps do
    evalTactic (← `(tactic| have := FvModexp.Util.dec_toNat $(← Term.exprToSyntax p)))

theorem msb_m1 : (18446744073709551615#64).msb = true := by decide
theorem ow2_refl (m : Janus.Arm64.Memory) (p n q k : Nat) : OnlyWrites2 m m p n q k := ⟨rfl, fun _ _ _ => rfl⟩

theorem ow2_self_iff (m : Janus.Arm64.Memory) (p n q k : Nat) : OnlyWrites2 m m p n q k ↔ True :=
  ⟨fun _ => trivial, fun _ => ow2_refl m p n q k⟩

theorem bitLen_bounds (v : Nat) (h : v ≠ 0) : 2 ^ (Aux.bitLen v - 1) ≤ v ∧ v < 2 ^ Aux.bitLen v := by
  simp only [Aux.bitLen, if_neg h, Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le h, Nat.lt_log2_self⟩

theorem clz_bl (n x : Nat) (hx : x < 2 ^ n) : Janus.Arm64.clzNat n x + Aux.bitLen x = n := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst this; simp [Janus.Arm64.clzNat, Aux.bitLen]
  | succ n ih =>
    unfold Janus.Arm64.clzNat
    by_cases hb : x.testBit n = true
    · have h1 : 2 ^ n ≤ x := Nat.ge_two_pow_of_testBit hb
      have h2 : Nat.log2 x = n := by
        rw [Nat.log2_eq_iff (by omega)]; exact ⟨h1, by simpa [Nat.pow_succ] using hx⟩
      simp [hb, Aux.bitLen, h2]; omega
    · have hb' : x.testBit n = false := by simpa using hb
      have h3 : x < 2 ^ n := by
        refine Classical.byContradiction fun hc => ?_
        have h1 : 2 ^ n ≤ x := by omega
        apply hb
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hd : x / 2 ^ n = 1 := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.pow_succ] at hx; omega)
        simp [hd]
      simp only [hb', Bool.false_eq_true, ite_false]
      have := ih x h3
      omega

theorem bl_split (k a c : Nat) (ha : a < 2 ^ k) : Aux.bitLen (a + 2 ^ k * c) = if c = 0 then Aux.bitLen a else k + Aux.bitLen c := by
  by_cases hc : c = 0
  · simp [hc]
  · have hP : 0 < 2 ^ k := Nat.two_pow_pos k
    have hm := (Nat.log2_eq_iff hc).mp rfl
    obtain ⟨m1, m2⟩ := hm
    have e1 : 2 ^ k * 2 ^ Nat.log2 c ≤ 2 ^ k * c := Nat.mul_le_mul_left _ m1
    have e2 : 2 ^ k * (c + 1) ≤ 2 ^ k * 2 ^ (Nat.log2 c + 1) := Nat.mul_le_mul_left _ m2
    have hne : a + 2 ^ k * c ≠ 0 := by
      have : 0 < 2 ^ k * c := Nat.mul_pos hP (Nat.pos_of_ne_zero hc)
      omega
    have : Nat.log2 (a + 2 ^ k * c) = k + Nat.log2 c := by
      rw [Nat.log2_eq_iff hne]
      constructor
      · rw [Nat.pow_add]; omega
      · rw [show k + Nat.log2 c + 1 = k + (Nat.log2 c + 1) from by omega, Nat.pow_add]
        rw [Nat.mul_add] at e2; omega
    unfold Aux.bitLen; rw [if_neg hne, if_neg hc, this]; rw [if_neg hc]; omega

theorem bl_4 (a0 a1 a2 a3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) :
    Aux.bitLen (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) =
    if a3 ≠ 0 then 192 + Aux.bitLen a3 else if a2 ≠ 0 then 128 + Aux.bitLen a2 else if a1 ≠ 0 then 64 + Aux.bitLen a1 else Aux.bitLen a0 := by
  have e : a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 =
      (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2) + 2 ^ 192 * a3 := by omega
  have l1 : a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 < 2 ^ 192 := by omega
  have s1 := bl_split 192 _ a3 l1
  have l2 : a0 + 2 ^ 64 * a1 < 2 ^ 128 := by omega
  have s2 := bl_split 128 _ a2 l2
  have s3 := bl_split 64 a0 a1 (by omega)
  rw [e, s1]
  by_cases c3 : a3 = 0
  · simp only [c3, if_true]
    rw [show a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 = (a0 + 2 ^ 64 * a1) + 2 ^ 128 * a2 by omega, s2]
    by_cases c2 : a2 = 0
    · simp only [c2, if_true]; rw [s3]; simp
    · simp [c2]
  · simp [c3]

section BEsec
open Janus.Arm64

theorem fromBE_add (f : Nat → Nat) (m n : Nat) :
    Aux.fromBE f (m + n) = Aux.fromBE f m * 256 ^ n + Aux.fromBE (fun i => f (m + i)) n := by
  induction m generalizing f with
  | zero => simp [Aux.fromBE]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [Aux.fromBE]
    rw [ih (fun i => f (i + 1))]
    have e : (fun i => f (m + i + 1)) = fun i => f (m + 1 + i) :=
      funext fun i => by rw [show m + i + 1 = m + 1 + i by omega]
    simp only [e]
    rw [Nat.pow_add, Nat.add_mul, Nat.mul_assoc]
    omega

theorem revBytes_readLE (m : Memory) (a k : Nat) :
    revBytesNat k (m.readLE a k) = Aux.fromBE (fun i => m.readLE (a + i) 1) k := by
  induction k generalizing a with
  | zero => simp [revBytesNat, Aux.fromBE]
  | succ k ih =>
    rw [Memory.readLE_succ, revBytesNat]
    have h1 : ((m.bytes a).toNat + 256 * m.readLE (a + 1) k) % 256 = (m.bytes a).toNat := by
      have := (m.bytes a).isLt
      omega
    have h2 : ((m.bytes a).toNat + 256 * m.readLE (a + 1) k) / 256 = m.readLE (a + 1) k := by
      have := (m.bytes a).isLt
      omega
    rw [h1, h2, ih (a + 1)]
    simp only [Aux.fromBE, Nat.add_zero, Memory.readLE_one]
    have e : (fun i => (m.bytes (a + 1 + i)).toNat) = fun i => (m.bytes (a + (i + 1))).toNat :=
      funext fun i => by rw [show a + 1 + i = a + (i + 1) by omega]
    rw [e]

theorem be32_rev (m : Memory) (p : Nat) :
    Aux.fromBE (fun i => m.readLE (p + i) 1) 32 =
      revBytesNat 8 (m.readLE p 8) * 2 ^ 192 + revBytesNat 8 (m.readLE (p + 8) 8) * 2 ^ 128 +
        revBytesNat 8 (m.readLE (p + 16) 8) * 2 ^ 64 + revBytesNat 8 (m.readLE (p + 24) 8) := by
  have h : ∀ q, Aux.fromBE (fun i => m.readLE (p + (q + i)) 1) 8 = revBytesNat 8 (m.readLE (p + q) 8) := by
    intro q
    rw [revBytes_readLE]
    simp only [Nat.add_assoc]
  have e0 : Aux.fromBE (fun i => m.readLE (p + i) 1) 8 = revBytesNat 8 (m.readLE p 8) :=
    revBytes_readLE m p 8 ▸ rfl
  rw [show 32 = 8 + 24 from rfl, fromBE_add, show 24 = 8 + 16 from rfl, fromBE_add, show 16 = 8 + 8 from rfl, fromBE_add]
  have h2 := h (8 + 8)
  have h3 := h (8 + (8 + 8))
  simp only [Nat.add_assoc] at h2 h3
  rw [e0, h 8, h2, h3]
  simp only [Nat.reduceAdd, Nat.reducePow, Nat.add_mul]
  omega

theorem revBytes_lt (k x : Nat) : revBytesNat k x < 256 ^ k := by
  induction k generalizing x with
  | zero => simp [revBytesNat]
  | succ k ih =>
    unfold revBytesNat
    have h1 : x % 256 < 256 := Nat.mod_lt _ (by decide)
    have h2 := ih (x / 256)
    rw [Nat.pow_succ]
    have : (x % 256) * 256 ^ k + revBytesNat k (x / 256) < 256 * 256 ^ k := by
      have : (x % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

theorem rc_rev8 (v : Nat) (hv : v < 18446744073709551616) :
    revContainersNat 8 1 v % 18446744073709551616 = revBytesNat 8 v := by
  have h := revBytes_lt 8 v
  simp only [revContainersNat, Nat.reducePow, Nat.mod_eq_of_lt hv] at *
  omega

theorem chunk8 (m : Memory) (a : Nat) :
    revContainersNat 8 1 (m.readLE a 8) % 18446744073709551616 =
      Aux.fromBE (fun i => m.readLE (a + i) 1) 8 := by
  rw [rc_rev8 _ (readLE8_lt _ _), revBytes_readLE]

theorem chunk4 (m : Memory) (a : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 4 1 (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 4))).toNat))).toNat =
      Aux.fromBE (fun i => m.readLE (a + i) 1) 4 := by
  have h4 : m.readLE a 4 < 4294967296 := by simpa using Memory.readLE_lt m a 4
  have hr := revBytes_lt 4 (m.readLE a 4)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, revContainersNat]
  rw [← revBytes_readLE]
  simp only [Nat.reducePow] at hr
  have e1 : m.readLE a 4 % 18446744073709551616 % 4294967296 = m.readLE a 4 := by omega
  rw [e1]
  have e2 : revBytesNat 4 (m.readLE a 4 % 4294967296) = revBytesNat 4 (m.readLE a 4) := by
    rw [Nat.mod_eq_of_lt h4]
  omega

theorem rot0 {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem chunk2 (m : Memory) (a : Nat) :
    ((BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 2 2 (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 2))).toNat))).rotateRight 0).toNat % 65536 =
      Aux.fromBE (fun i => m.readLE (a + i) 1) 2 := by
  have h2 : m.readLE a 2 < 65536 := by simpa using Memory.readLE_lt m a 2
  have hr := revBytes_lt 2 (m.readLE a 2)
  simp only [rot0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, revContainersNat]
  rw [← revBytes_readLE]
  simp only [Nat.reducePow] at hr
  have e1 : m.readLE a 2 % 18446744073709551616 % 4294967296 = m.readLE a 2 := by omega
  rw [e1]
  have e2 : m.readLE a 2 % 65536 = m.readLE a 2 := Nat.mod_eq_of_lt h2
  have e3 : m.readLE a 2 / 65536 = 0 := by omega
  simp only [e2, e3, Nat.zero_mod, revBytesNat, Nat.mul_zero, Nat.add_zero]
  omega

theorem or_hi (a c k : Nat) (ha : a < 2 ^ k) : a ||| (c * 2 ^ k) = a + c * 2 ^ k := by
  have := or_split k a 0 0 c ha (Nat.two_pow_pos k)
  simpa [Nat.mul_comm] using this

theorem or_hi16 (a c : Nat) (ha : a < 65536) : a ||| (c * 65536) = a + c * 65536 := or_hi a c 16 ha
theorem or_hi24 (a c : Nat) (ha : a < 16777216) : a ||| (c * 16777216) = a + c * 16777216 := or_hi a c 24 ha
theorem or_hi32 (a c : Nat) (ha : a < 4294967296) : a ||| (c * 4294967296) = a + c * 4294967296 := or_hi a c 32 ha
theorem or_hi40 (a c : Nat) (ha : a < 1099511627776) : a ||| (c * 1099511627776) = a + c * 1099511627776 := or_hi a c 40 ha
theorem or_hi48 (a c : Nat) (ha : a < 281474976710656) : a ||| (c * 281474976710656) = a + c * 281474976710656 := or_hi a c 48 ha
theorem or_hi56 (a c : Nat) (ha : a < 72057594037927936) : a ||| (c * 72057594037927936) = a + c * 72057594037927936 := or_hi a c 56 ha

theorem rd1_lt (m : Memory) (a : Nat) : m.readLE a 1 < 256 := by simpa using Memory.readLE_lt m a 1

theorem chunk2n (m : Janus.Arm64.Memory) (a : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 2 2 (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 2))).toNat))).toNat % 65536 =
      Aux.fromBE (fun i => m.readLE (a + i) 1) 2 := by
  have := chunk2 m a
  simpa [rot0] using this

end BEsec

theorem pq_eq (t : Nat) (ht : t ≤ 64) : 2 ^ t * 2 ^ (64 - t) = 18446744073709551616 := by
  rw [← Nat.pow_add, show t + (64 - t) = 64 by omega]

theorem shl_lo (x t : Nat) (ht : t ≤ 64) :
    x * 2 ^ t % 18446744073709551616 = 2 ^ t * (x % 2 ^ (64 - t)) := by
  have h := pq_eq t ht
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have hd := Nat.div_add_mod x (2 ^ (64 - t))
  have e1 : x * 2 ^ t = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) + 2 ^ t * (x % 2 ^ (64 - t)) := by
    calc x * 2 ^ t = 2 ^ t * x := Nat.mul_comm _ _
      _ = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t)) + x % 2 ^ (64 - t)) := by rw [hd]
      _ = _ := Nat.mul_add _ _ _
  have e2 : 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) = 18446744073709551616 * (x / 2 ^ (64 - t)) := by
    rw [← Nat.mul_assoc, h]
  have hlt : 2 ^ t * (x % 2 ^ (64 - t)) < 18446744073709551616 := by
    rw [← h]
    exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hQ) hP
  rw [e1, e2, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- `x * 2^t = 2^64 * (x / 2^(64-t)) + (x * 2^t % 2^64)`. -/
theorem shl_split (x t : Nat) (ht : t ≤ 64) :
    x * 2 ^ t = 18446744073709551616 * (x / 2 ^ (64 - t)) + x * 2 ^ t % 18446744073709551616 := by
  have h := pq_eq t ht
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have hd := Nat.div_add_mod x (2 ^ (64 - t))
  have e1 : x * 2 ^ t = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) + 2 ^ t * (x % 2 ^ (64 - t)) := by
    calc x * 2 ^ t = 2 ^ t * x := Nat.mul_comm _ _
      _ = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t)) + x % 2 ^ (64 - t)) := by rw [hd]
      _ = _ := Nat.mul_add _ _ _
  have e2 : 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) = 18446744073709551616 * (x / 2 ^ (64 - t)) := by
    rw [← Nat.mul_assoc, h]
  rw [shl_lo x t ht]
  omega

theorem lo_hi_lt (x y t : Nat) (ht : t < 64) (hy : y < 18446744073709551616) :
    x * 2 ^ t % 18446744073709551616 + y / 2 ^ (64 - t) < 18446744073709551616 := by
  have h := pq_eq t (by omega)
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  rw [shl_lo x t (by omega)]
  have h1 : y / 2 ^ (64 - t) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul hQ]
    rw [h]; exact hy
  have h2 : x % 2 ^ (64 - t) + 1 ≤ 2 ^ (64 - t) := Nat.mod_lt _ hQ
  have h3 : 2 ^ t * (x % 2 ^ (64 - t) + 1) ≤ 2 ^ t * 2 ^ (64 - t) := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_add, h] at h3
  omega

theorem shl_or (a b t : Nat) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ t % 18446744073709551616 ||| b / 2 ^ (64 - t)) % 18446744073709551616 =
      a * 2 ^ t % 18446744073709551616 + b / 2 ^ (64 - t) := by
  have h := pq_eq t (by omega)
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have hv : b / 2 ^ (64 - t) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul hQ, h]; exact hb
  have hlt := lo_hi_lt a b t ht hb
  rw [shl_lo a t (by omega)]
  rw [Nat.or_comm, show 2 ^ t * (a % 2 ^ (64 - t)) = (a % 2 ^ (64 - t)) * 2 ^ t from Nat.mul_comm _ _, or_hi _ _ _ hv]
  rw [shl_lo a t (by omega)] at hlt
  rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm] at hlt; omega)]
  rw [Nat.mul_comm]; omega

section W16sec
open Janus.Arm64

end W16sec

theorem hi16 (A B : Nat) (hA : A < 18446744073709551616) (hB : B < 18446744073709551616) :
    (A + 18446744073709551616 * B) / 18446744073709551616 % 18446744073709551616 = B := by
  omega

theorem bv128_zero_toNat : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) = 0 := rfl

@[simp] theorem rd4mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 4 % 4294967296 = m.readLE a 4 := by
  exact Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt m a 4)
@[simp] theorem rd2mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 2 % 65536 = m.readLE a 2 := by
  exact Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt m a 2)
@[simp] theorem rd1mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 1 % 256 = m.readLE a 1 := by
  exact Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt m a 1)

theorem or_hi_comm (a c k : Nat) (ha : a < 2 ^ k) : c * 2 ^ k ||| a = a + c * 2 ^ k := by
  rw [Nat.or_comm]; exact or_hi a c k ha
theorem orc_hi16 (a c : Nat) (ha : a < 65536) : c * 65536 ||| a = a + c * 65536 := or_hi_comm a c 16 ha
theorem orc_hi24 (a c : Nat) (ha : a < 16777216) : c * 16777216 ||| a = a + c * 16777216 := or_hi_comm a c 24 ha
theorem orc_hi32 (a c : Nat) (ha : a < 4294967296) : c * 4294967296 ||| a = a + c * 4294967296 := or_hi_comm a c 32 ha
theorem orc_hi40 (a c : Nat) (ha : a < 1099511627776) : c * 1099511627776 ||| a = a + c * 1099511627776 := or_hi_comm a c 40 ha
theorem orc_hi48 (a c : Nat) (ha : a < 281474976710656) : c * 281474976710656 ||| a = a + c * 281474976710656 := or_hi_comm a c 48 ha
theorem orc_hi56 (a c : Nat) (ha : a < 72057594037927936) : c * 72057594037927936 ||| a = a + c * 72057594037927936 := or_hi_comm a c 56 ha

theorem bswap16 (v : Nat) (hv : v < 65536) :
    ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64 |||
      BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8)).toNat
      = v % 256 * 256 + v / 256 := by
  simp [BitVec.toNat_or, BitVec.toNat_and, BitVec.rotateLeft, BitVec.rotateLeftAux]
  have h0 : v % 65536 = v := Nat.mod_eq_of_lt hv
  have h1 : v % 65536 % 18446744073709551616 = v := by omega
  rw [h1, h0]
  have hand : v &&& 18446744073709486080 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    have hm : (18446744073709486080 : Nat) = 2 ^ 16 * 281474976710655 + 0 := by decide
    by_cases hi : i < 16
    · rw [hm, Nat.testBit_two_pow_mul_add _ (by decide : (0:Nat) < 2 ^ 16)]
      simp [hi]
    · have : v.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by simpa using hv : v < 2 ^ 16) (Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : 16 ≤ i)))
      simp [this]
  rw [hand, Nat.zero_or]
  have e1 : v <<< 8 % 65536 = v % 256 * 256 := by
    simp only [Nat.shiftLeft_eq]; omega
  have e2 : v >>> 8 = v / 256 := by rw [Nat.shiftRight_eq_div_pow]
  rw [e1, e2, Nat.or_comm]
  have e3 : v % 256 * 256 % 18446744073709551616 = v % 256 * 256 := by omega
  rw [e3]
  have := or_hi (v / 256) (v % 256) 8 (by omega)
  simp only [Nat.reducePow] at this
  omega
theorem rd2_lt (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 2 < 65536 := by
  simpa using Janus.Arm64.Memory.readLE_lt m a 2

theorem rd2_bytes (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 2 = m.readLE a 1 + 256 * m.readLE (a + 1) 1 := by
  rw [show 2 = 1 + 1 from rfl, Janus.Arm64.Memory.readLE_add]

theorem bswap16n (v : Nat) (hv : v < 65536) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64).toNat |||
      (BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8)).toNat)
      = v % 256 * 256 + v / 256 := by
  have := bswap16 v hv
  rwa [BitVec.toNat_or] at this

theorem bswap16m (v : Nat) (hv : v < 65536) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64).toNat |||
      ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat)
      = v % 256 * 256 + v / 256 := by
  have := bswap16n v hv
  have h : (BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8)).toNat =
      ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))
  rwa [h] at this

theorem bswap16w (v : Nat) (hv : v < 65536) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16
      ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64 |||
        BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8))))).toNat
      = v % 256 * 256 + v / 256 := by
  have h := bswap16 v hv
  have h2 : v % 256 * 256 + v / 256 < 65536 := by omega
  have e1 : (v % 256 * 256 + v / 256) % 65536 = v % 256 * 256 + v / 256 := Nat.mod_eq_of_lt h2
  have e2 : (v % 256 * 256 + v / 256) % 4294967296 = v % 256 * 256 + v / 256 := Nat.mod_eq_of_lt (Nat.lt_trans h2 (by decide))
  have e3 : (v % 256 * 256 + v / 256) % 18446744073709551616 = v % 256 * 256 + v / 256 := Nat.mod_eq_of_lt (Nat.lt_trans h2 (by decide))
  simp only [BitVec.toNat_setWidth, h, e1, e2, e3, Nat.reducePow]

theorem bswap16x (v : Nat) (hv : v < 65536) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64).toNat |||
      (((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat % 18446744073709551616))
      = v % 256 * 256 + v / 256 := by
  have := bswap16m v hv
  have h : ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat % 18446744073709551616 =
      ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))
  rwa [← h] at this

-- SRsh helpers
theorem mask_val (r : Nat) (hr : 0 < r) (hr2 : r < 64) :
    (if 64 - r < 64 then -BitVec.ofNat 64 (2 ^ ((64 - r) % 64)) else 0#64).toNat =
      18446744073709551616 - 2 ^ (64 - r) := by
  have hc : 64 - r < 64 := by omega
  simp only [hc, if_true, BitVec.toNat_neg, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 64 - r < 64)]
  have hp : 2 ^ (64 - r) < 18446744073709551616 := by
    calc 2 ^ (64 - r) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
      _ = 18446744073709551616 := by decide
  have hq : 2 ^ (64 - r) % 18446744073709551616 = 2 ^ (64 - r) := Nat.mod_eq_of_lt hp
  show (2 ^ 64 - 2 ^ (64 - r) % 2 ^ 64) % 2 ^ 64 = _
  have h64 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  rw [h64, hq]
  have := Nat.two_pow_pos (64 - r)
  omega

def blS (u : BitVec 64) : BitVec 64 :=
  ((if u.getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 |||
      u.rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 61

section RC8
open Janus.Arm64
end RC8

-- byte `e/8` (from the low end) of a 256-bit number written as four limbs; stated with explicit literals so that it can be applied in omega-hostile contexts

theorem wb0 (h i j k : Nat) (hh : h < 18446744073709551616) (hi : i < 18446744073709551616) (hj : j < 18446744073709551616) (hk : k < 18446744073709551616) :
    (h + 18446744073709551616 * i + 340282366920938463463374607431768211456 * j + 6277101735386680763835789423207666416102355444464034512896 * k) / 1 % 256 = h / 1 % 256 := by omega
section B20
open Janus.Arm64
end B20

-- MulOverflow helper
section WTS
open Janus.Arm64
def wts (M : Memory) (d e : Nat) (zl : Nat → Nat) : Nat → Memory
  | 0 => M
  | i + 1 => (wts M d e zl i).writeLE (d + (e - i)) 1 (zl (i / 8) / 2 ^ (8 * (i % 8)) % 256)

theorem fromBE_congr {f g : Nat → Nat} {n : Nat} (h : ∀ a, a < n → f a = g a) :
    FvModexp.Aux.fromBE f n = FvModexp.Aux.fromBE g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [FvModexp.Aux.fromBE]
    rw [h 0 (by omega), ih (fun a ha => h (a + 1) (by omega))]

end WTS

section CH32
open Janus.Arm64
end CH32

-- ByteLen amd64 helper
theorem fromBE_lt (f : Nat → Nat) (hf : ∀ i, f i < 256) (n : Nat) : Aux.fromBE f n < 256 ^ n := by
  induction n generalizing f with
  | zero => simp [Aux.fromBE]
  | succ n ih =>
    simp only [Aux.fromBE]
    have h1 := hf 0
    have h2 := ih (fun i => f (i + 1)) (fun i => hf (i + 1))
    rw [Nat.pow_succ]
    have : f 0 * 256 ^ n + 256 ^ n ≤ 256 ^ n * 256 := by
      have : (f 0 + 1) * 256 ^ n ≤ 256 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 256] at this; exact this
    omega

theorem and_ones (x : Nat) (h : x < 18446744073709551616) : x &&& 18446744073709551615 = x := by
  have := Nat.and_two_pow_sub_one_eq_mod x 64
  simp only [Nat.reducePow, Nat.reduceSub] at this
  rw [this]; exact Nat.mod_eq_of_lt h

theorem fin1 (x0 x1 x2 x3 : Nat) (h3 : x3 = 0) :
    0 * 6277101735386680763835789423207666416102355444464034512896 + x2 * 340282366920938463463374607431768211456 + x1 * 18446744073709551616 + x0 = x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 := by omega
theorem fin2 (x0 x1 x2 x3 : Nat) (h3 : x3 = 0) (h2 : x2 = 0) :
    0 * 6277101735386680763835789423207666416102355444464034512896 + 0 * 340282366920938463463374607431768211456 + x1 * 18446744073709551616 + x0 = x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 := by omega
theorem fin3 (x0 x1 x2 x3 : Nat) (h3 : x3 = 0) (h2 : x2 = 0) (h1 : x1 = 0) :
    0 * 6277101735386680763835789423207666416102355444464034512896 + 0 * 340282366920938463463374607431768211456 + 0 * 18446744073709551616 + x0 = x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 := by omega

section SBQ
open Janus.Arm64
end SBQ

end FvModexp.Util
