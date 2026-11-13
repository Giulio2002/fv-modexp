import FvModexp.Proofs.Amd64.Exp.ModInvDefs

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the Newton loop (nat.go:1297-1300) (agent infra s53; twin of
`FvModexp.Arm64.ModInv.newtonLoop_run`)

```
+0x6c  CMPQ RBX, RDX ; JCS +0x5d       // for i := uint(1); i < n0; i <<= 1 {
+0x5d  IMULQ R11, R11                  //   t *= t
       LEAQ 1(R11), R13 ; ADDQ RBX, RBX
       IMULQ R13, R12                  //   k0 *= (t + 1) }
+0x71  (exit)
```
with `i = 2^j` in `RBX`, `n0` in `RDX`, `t` in `R11`, `k0` in `R12`; the model is `Exp.newtonLoop n0 j t k`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

/-- what the loop leaves alone: the argument registers, `RSP`, `RBP`, `R14`, memory, `fs`, `X15`, `DF` -/
def NKeep (S S' : State) : Prop :=
  S'.regs 0 = S.regs 0 ∧ S'.regs 1 = S.regs 1 ∧ S'.regs 4 = S.regs 4 ∧ S'.regs 5 = S.regs 5 ∧
    S'.regs 6 = S.regs 6 ∧ S'.regs 7 = S.regs 7 ∧ S'.regs 8 = S.regs 8 ∧ S'.regs 9 = S.regs 9 ∧
    S'.regs 10 = S.regs 10 ∧ S'.regs 14 = S.regs 14 ∧ S'.mem = S.mem ∧ S'.fsBase = S.fsBase ∧
    S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df

theorem NKeep.trans {S S' S'' : State} (h1 : NKeep S S') (h2 : NKeep S' S'') : NKeep S S'' := by
  obtain ⟨a0, a1, a4, a5, a6, a7, a8, a9, a10, a14, am, af, ax, ad⟩ := h1
  obtain ⟨b0, b1, b4, b5, b6, b7, b8, b9, b10, b14, bm, bf, bx, bd⟩ := h2
  exact ⟨b0.trans a0, b1.trans a1, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7, b8.trans a8, b9.trans a9,
    b10.trans a10, b14.trans a14, bm.trans am, bf.trans af, bx.trans ax, bd.trans ad⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- one test of the loop at `+0x6c` -/
theorem newtonIter (impl : List Amd64.Segment) {ret : BitVec 64} {Q : State → Prop} (S : State) (n0 j t k : Nat)
    (hpc : S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x6c)) (h3 : S.regs 3 = BitVec.ofNat 64 (2 ^ j))
    (h2 : S.regs 2 = BitVec.ofNat 64 n0) (h11 : S.regs 11 = BitVec.ofNat 64 t) (h12 : S.regs 12 = BitVec.ofNat 64 k)
    (hn0 : n0 ≤ 64) (hj : 2 ^ j ≤ 64) (ht : t < 2 ^ 64) (hk : k < 2 ^ 64)
    (KL : ∀ S' : State, 2 ^ j < n0 → S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x6c) →
      S'.regs 3 = BitVec.ofNat 64 (2 ^ (j + 1)) → S'.regs 2 = BitVec.ofNat 64 n0 →
      S'.regs 11 = BitVec.ofNat 64 (t * t % Exp.B) →
      S'.regs 12 = BitVec.ofNat 64 (k * ((t * t % Exp.B + 1) % Exp.B) % Exp.B) → NKeep S S' →
      ReachesRet (LibW.program.link impl) ret S' Q)
    (KE : ∀ S' : State, ¬ 2 ^ j < n0 → S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x71) →
      S'.regs 12 = BitVec.ofNat 64 k → NKeep S S' → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hB : Exp.B = 2 ^ 64 := Exp.B_def
  have hjp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
  by_cases hc : 2 ^ j < n0
  · janus64_run [hc] until [0x5ea8c0 + 0x6c]
    refine KL _ hc ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try janus64_simp
    all_goals apply BitVec.eq_of_toNat_eq
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hB, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt hk]
    · rw [hjp]; omega
    · rw [Nat.mod_mod]
    · simp only [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  · janus64_run [hc] until [0x5ea8c0 + 0x71]
    refine KE _ hc ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals janus64_simp

/-- the whole loop from `i = 2^j`: `R12 = newtonLoop n0 j t k` at `+0x71` -/
theorem newtonLoop_run (impl : List Amd64.Segment) {ret : BitVec 64} {Q : State → Prop} (n0 : Nat) (hn0 : n0 ≤ 64) :
    ∀ (fuel j : Nat) (S : State) (t k : Nat), 6 - j ≤ fuel → j ≤ 6 → t < 2 ^ 64 → k < 2 ^ 64 →
    S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x6c) → S.regs 3 = BitVec.ofNat 64 (2 ^ j) →
    S.regs 2 = BitVec.ofNat 64 n0 → S.regs 11 = BitVec.ofNat 64 t → S.regs 12 = BitVec.ofNat 64 k →
    (∀ S' : State, S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x71) →
      S'.regs 12 = BitVec.ofNat 64 (Exp.newtonLoop n0 j t k) → NKeep S S' →
      ReachesRet (LibW.program.link impl) ret S' Q) →
    ReachesRet (LibW.program.link impl) ret S Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro j S t k hf hj ht hk hpc h3 h2 h11 h12 K
    refine newtonIter impl S n0 j t k hpc h3 h2 h11 h12 hn0 (by rw [show j = 6 by omega]; decide) ht hk
      (fun _ hc => absurd hc (by rw [show j = 6 by omega]; omega)) fun S' hc a1 a2 a3 => K S' a1 ?_ a3
    rw [Exp.newtonLoop, dite_eq_right hc]; exact a2
  | succ f ih =>
    intro j S t k hf hj ht hk hpc h3 h2 h11 h12 K
    have hjp : 2 ^ j ≤ 64 := by
      calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hj
        _ = 64 := rfl
    refine newtonIter impl S n0 j t k hpc h3 h2 h11 h12 hn0 hjp ht hk ?_ ?_
    · intro S' hc a1 a2 a3 a4 a5 a6
      have hj6 : j < 6 := by
        refine Nat.lt_of_not_le fun h => ?_
        have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h
        simp at this; omega
      refine ih (j + 1) S' (t * t % Exp.B) (k * ((t * t % Exp.B + 1) % Exp.B) % Exp.B) (by omega) (by omega)
        (by rw [Exp.B_def]; exact Nat.mod_lt _ (by decide)) (by rw [Exp.B_def]; exact Nat.mod_lt _ (by decide)) a1 a2 a3 a4 a5
        fun S'' b1 b2 b3 => K S'' b1 ?_ (a6.trans b3)
      rw [Exp.newtonLoop, dite_eq_left hc]; exact b2
    · intro S' hc a1 a2 a3
      refine K S' a1 ?_ a3
      rw [Exp.newtonLoop, dite_eq_right hc]; exact a2

end FvModexp.Amd64.ModInv
