import FvModexp.Proofs.Arm64.Exp.ModInvDefs

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the Newton loop (nat.go:1297-1300) (agent infra)

```
+0x4c  CMP R8, R1 ; BCC +0x3c      // for i := uint(1); i < n0; i <<= 1 {
+0x3c  MUL R9, R9, R9               //   t *= t
       ADD $1, R9, R11 ; ADD R1, R1, R1
       MUL R11, R10, R10            //   k0 *= (t + 1) }
```
with `i = 2^j` in `R1`, `n0` in `R8`, `t` in `R9`, `k0` in `R10`; the model is `Exp.newtonLoop n0 j t k`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- one test of the loop at `+0x4c` -/
theorem newtonIter (impl : List Segment) {ret : BitVec 64} {Q : State → Prop} (S : State) (n0 j t k : Nat)
    (hpc : S.pc = BitVec.ofNat 64 1797196) (h1 : S.regs 1 = BitVec.ofNat 64 (2 ^ j))
    (h8 : S.regs 8 = BitVec.ofNat 64 n0) (h9 : S.regs 9 = BitVec.ofNat 64 t) (h10 : S.regs 10 = BitVec.ofNat 64 k)
    (hn0 : n0 ≤ 64) (hj : 2 ^ j ≤ 64) (ht : t < 2 ^ 64) (hk : k < 2 ^ 64)
    (KL : ∀ S' : State, 2 ^ j < n0 → S'.pc = BitVec.ofNat 64 1797196 →
      S'.regs 1 = BitVec.ofNat 64 (2 ^ (j + 1)) → S'.regs 8 = BitVec.ofNat 64 n0 →
      S'.regs 9 = BitVec.ofNat 64 (t * t % Exp.B) →
      S'.regs 10 = BitVec.ofNat 64 (k * ((t * t % Exp.B + 1) % Exp.B) % Exp.B) →
      S'.regs 0 = S.regs 0 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 → S'.regs 4 = S.regs 4 →
      S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = S.mem → S'.sp = S.sp →
      ReachesRet (LibW.program.link impl) ret S' Q)
    (KE : ∀ S' : State, ¬ 2 ^ j < n0 → S'.pc = BitVec.ofNat 64 1797204 → S'.regs 10 = BitVec.ofNat 64 k →
      S'.regs 0 = S.regs 0 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 → S'.regs 4 = S.regs 4 →
      S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = S.mem → S'.sp = S.sp →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hB : Exp.B = 2 ^ 64 := Exp.B_def
  have hjp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
  by_cases hc : 2 ^ j < n0
  · janus_run [hc] until [1797196]
    refine KL _ hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try janus_simp
    all_goals apply BitVec.eq_of_toNat_eq
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hB, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt hk]
    · rw [hjp]; omega
    · rw [Nat.mod_mod]
    · simp only [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  · janus_run [hc] until [1797204]
    refine KE _ hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals janus_simp

/-- the whole loop from `i = 2^j`: `R10 = newtonLoop n0 j t k` at `+0x54` -/
theorem newtonLoop_run (impl : List Segment) {ret : BitVec 64} {Q : State → Prop} (n0 : Nat) (hn0 : n0 ≤ 64) :
    ∀ (fuel j : Nat) (S : State) (t k : Nat), 6 - j ≤ fuel → j ≤ 6 → t < 2 ^ 64 → k < 2 ^ 64 →
    S.pc = BitVec.ofNat 64 1797196 → S.regs 1 = BitVec.ofNat 64 (2 ^ j) →
    S.regs 8 = BitVec.ofNat 64 n0 → S.regs 9 = BitVec.ofNat 64 t → S.regs 10 = BitVec.ofNat 64 k →
    (∀ S' : State, S'.pc = BitVec.ofNat 64 1797204 → S'.regs 10 = BitVec.ofNat 64 (Exp.newtonLoop n0 j t k) →
      S'.regs 0 = S.regs 0 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 → S'.regs 4 = S.regs 4 →
      S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = S.mem → S'.sp = S.sp →
      ReachesRet (LibW.program.link impl) ret S' Q) →
    ReachesRet (LibW.program.link impl) ret S Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro j S t k hf hj ht hk hpc h1 h8 h9 h10 K
    have h64 : 2 ^ j = 64 := by rw [show j = 6 by omega]
    refine newtonIter impl S n0 j t k hpc h1 h8 h9 h10 hn0 (by omega) ht hk (fun _ hc => absurd hc (by omega))
      fun S' hc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 => K S' a1 ?_ a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
    rw [Exp.newtonLoop, dite_eq_right hc]; exact a2
  | succ f ih =>
    intro j S t k hf hj ht hk hpc h1 h8 h9 h10 K
    have hjp : 2 ^ j ≤ 64 := by
      calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hj
        _ = 64 := rfl
    refine newtonIter impl S n0 j t k hpc h1 h8 h9 h10 hn0 hjp ht hk ?_ ?_
    · intro S' hc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
      have hj6 : j < 6 := by
        refine Nat.lt_of_not_le fun h => ?_
        have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h
        simp at this; omega
      refine ih (j + 1) S' (t * t % Exp.B) (k * ((t * t % Exp.B + 1) % Exp.B) % Exp.B) (by omega) (by omega)
        (by rw [Exp.B_def]; exact Nat.mod_lt _ (by decide)) (by rw [Exp.B_def]; exact Nat.mod_lt _ (by decide)) a1 a2 a3 a4 a5
        fun S'' b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 => K S'' b1 ?_ (b3.trans a6) (b4.trans a7) (b5.trans a8)
          (b6.trans a9) (b7.trans a10) (b8.trans a11) (b9.trans a12) (b10.trans a13) (b11.trans a14) (b12.trans a15)
          (b13.trans a16) (b14.trans a17)
      rw [Exp.newtonLoop, dite_eq_left hc]; exact b2
    · intro S' hc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      refine K S' a1 ?_ a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      rw [Exp.newtonLoop, dite_eq_right hc]; exact a2

end FvModexp.Arm64.ModInv
