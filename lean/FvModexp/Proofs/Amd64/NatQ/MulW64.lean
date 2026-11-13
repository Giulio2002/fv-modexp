import FvModexp.Proofs.Common.MulCost

set_option autoImplicit false

/-!
# Stack windows of the multiplication SCC on amd64 (divmc s40; the amd64 twin of `Common/MulCost` §Stack windows)

amd64 frame offsets of a callee's entry RSP below the caller's entry RSP (checked on the disassembly,
scratchpad s40/mulx-amd64.s): `nat.mul` (`0x5f0840`: `PUSHQ BP; SUBQ $0xf8` + the CALL push) = 264 (arm64: 256),
`karatsuba` (`0x5f1da0`: `SUBQ $0x1b8`) = 456 (arm64: 448), `(*Int).mul` (`0x5e29e0`: `SUBQ $0x50`) = 96 (= arm64).
`Common/MulCost`'s `mulW`/`kW` are tight for the arm64 offsets (`kW_call` holds with equality), so amd64 uses its own
windows with the per-level slope 1080 (= 264 + 456 + 96 + 264) instead of 1056.
-/

namespace FvModexp.Amd64

open FvModexp

/-- the window of `nat.mul` (`len x = m`, `len y = n`) at its entry (amd64) -/
def mulW64 (m n : Nat) : Nat := 1080 * Nat.log2 (m * n) + 4608 + if m < n then 264 else 0

/-- the window of `karatsuba` on `n`-word operands (amd64) -/
def kW64 (n : Nat) : Nat := 1080 * Nat.log2 (kh n * kh n) + 4608 + 816

/-- the window of `(*Int).mul` on operands of `xl`, `yl` words (amd64) -/
def imW64 (xl yl : Nat) : Nat := mulW64 xl yl + 96

/-- the exported window (`xl, yl ≤ 2^12`, amd64) -/
abbrev mulWX64 : Nat := 30792

theorem mulW64_ge (m n : Nat) : 4608 ≤ mulW64 m n := by unfold mulW64; omega

theorem kW64_ge (n : Nat) : 5424 ≤ kW64 n := by unfold kW64; omega

theorem mulW64_swap {m n : Nat} (h : m < n) : mulW64 n m + 264 ≤ mulW64 m n := by
  unfold mulW64; rw [Nat.mul_comm n m, if_neg (by omega), if_pos h]; omega

/-- the chunk product `t.mul(c, n)` (`0 < c ≤ n`, `2c ≤ m`) one `nat.mul` frame down -/
theorem mulW64_chunk {m n c : Nat} (hc0 : 0 < c) (hcn : c ≤ n) (h2 : 2 * c ≤ m) :
    mulW64 c n + 264 ≤ mulW64 m n := by
  have hp : 0 < c * n := Nat.mul_pos hc0 (by omega)
  have : 2 * (c * n) ≤ m * n := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right n h2
  have := log2_step hp this
  unfold mulW64; split <;> split <;> omega

/-- `karatsuba(n)` (`40 ≤ n ≤ m`) one `nat.mul` frame down -/
theorem kW64_call {m n : Nat} (h40 : 40 ≤ n) (hnm : n ≤ m) : kW64 n + 264 ≤ mulW64 m n := by
  have hkh : kh n = (n + 1) / 2 := rfl
  have hp : 0 < kh n * kh n := Nat.mul_pos (by omega) (by omega)
  have h1 := two_kh_sq h40
  have h2 : n * n ≤ m * n := Nat.mul_le_mul_right n hnm
  have := log2_step hp (Nat.le_trans h1 h2)
  unfold kW64 mulW64; rw [if_neg (by omega)]; omega

/-- an inner `(*Int).mul` of `karatsuba(n)` (operands `≤ n2` words) one `karatsuba` frame down -/
theorem imW64_inner {n a b : Nat} (ha : a ≤ kh n) (hb : b ≤ kh n) : imW64 a b + 456 ≤ kW64 n := by
  have := log2_mono (Nat.mul_le_mul ha hb)
  unfold imW64 mulW64 kW64; split <;> omega

/-- `nat.mul` one `(*Int).mul` frame down -/
theorem imW64_call (a b : Nat) : mulW64 a b + 96 ≤ imW64 a b := Nat.le_refl _

theorem mulW64_le_X {xl yl : Nat} (hx : xl ≤ 2 ^ 12) (hy : yl ≤ 2 ^ 12) : mulW64 xl yl ≤ mulWX64 := by
  have h1 : xl * yl ≤ 2 ^ 12 * 2 ^ 12 := Nat.mul_le_mul hx hy
  have h2 : Nat.log2 (xl * yl) ≤ 24 := by
    have := log2_mono h1
    rw [show (2 : Nat) ^ 12 * 2 ^ 12 = 2 ^ 24 from rfl, Nat.log2_two_pow] at this; exact this
  unfold mulW64 mulWX64; split <;> omega

end FvModexp.Amd64
