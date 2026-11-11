import FvModexp.Proofs.Common.Conv

/-!
# `(*Int).Bytes` (`int.go:527`, `nat.bytes` `nat.go:1628`): the byte-level facts

`nat.bytes` writes the bytes of the limbs, least significant first, from the END of `buf` backwards: after all
`8·len` bytes, `buf[N-1-i] = byte i of abs` (little-endian memory order of the limbs), i.e. `buf` is the big-endian form of
`natVal abs`. Then the leading zero bytes are skipped.
-/

open Janus Janus.Arm64

namespace FvModexp

/-- A buffer holding the bytes of `[a, a + N)` in reverse order is the big-endian form of their little-endian value. -/
theorem beVal_rev {m m' : Memory} {p : Nat} : ∀ {N a : Nat},
    (∀ i, i < N → (m.bytes (p + (N - 1 - i))).toNat = (m'.bytes (a + i)).toNat) → beVal m p N = m'.readLE a N
  | 0, _, _ => rfl
  | N + 1, a, h => by
    rw [beVal_succ, Memory.readLE_succ]
    have h0 := h 0 (by omega)
    have ih := beVal_rev (m := m) (m' := m') (p := p) (N := N) (a := a + 1) fun i hi => by
      have := h (i + 1) (by omega)
      rw [show N + 1 - 1 - (i + 1) = N - 1 - i by omega, show a + (i + 1) = a + 1 + i by omega] at this
      exact this
    rw [ih, show N + 1 - 1 - 0 = N by omega, Nat.add_zero] at *
    rw [h0]; omega

/-- Leading zero bytes do not change the big-endian value. -/
theorem beVal_skip {m : Memory} {p k n : Nat} (h : ∀ i, i < k → (m.bytes (p + i)).toNat = 0) :
    beVal m p (k + n) = beVal m (p + k) n := by
  have hz : beVal m p k = 0 := by
    clear n
    induction k with
    | zero => rfl
    | succ k ih => rw [beVal_succ, ih (fun i hi => h i (by omega)), h k (by omega)]
  rw [beVal_add, hz]; simp

end FvModexp
