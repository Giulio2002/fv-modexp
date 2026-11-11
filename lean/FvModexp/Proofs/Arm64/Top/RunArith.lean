/-!
# `Run` (arm64): small arithmetic facts of the operand phase, proved outside the large segment contexts

PERF (docs/PERF.md): an `omega` inside a segment proof sees every hypothesis of the context (RunD3P: 97 s for one
`BitVec` subtraction fact). These lemmas take exactly the facts they need.
-/

namespace FvModexp.Arm64.Run

/-- The end of the slice `data[start:]` read so far fits the input capacity after the header offset. -/
theorem cap_le (m l cp off : Nat) (hm : m ≤ l - 96) (hlcp : l ≤ cp)
    (ho : (96 < l ∧ off = 96) ∨ (l ≤ 96 ∧ off = 0)) : m ≤ cp - off := by omega

/-- The input rest copied by `RightPadBytes` lies inside the input. -/
theorem rng_le (p l off mN m : Nat) (hm : mN ≤ m) (hm2 : m ≤ l - 96)
    (ho : (96 < l ∧ off = 96) ∨ (l ≤ 96 ∧ off = 0)) (hmN : l - 96 - m = 0 ∨ mN = m) :
    p ≤ p + off + mN ∧ p + off + mN + (l - 96 - m) ≤ p + l ∧ off + mN ≤ l := by omega

/-- A stack address of `Run`'s frame is not an input address. -/
theorem stk_ne (sp p l off mN k : Nat) (hpw : p + l ≤ sp - 4800 ∨ sp + 40 ≤ p) (h : off + mN ≤ l) (hsp : 4800 ≤ sp)
    (hk : k < 4800) (hk0 : 0 < k) : (sp - k = p + off + mN) = False := by simp only [eq_iff_iff, iff_false]; omega

/-- A nonempty input rest means the input is longer than the header: offset 96. -/
theorem off_of (l off m : Nat) (ho : (96 < l ∧ off = 96) ∨ (l ≤ 96 ∧ off = 0)) (hn : 0 < l - 96 - m) : off = 96 := by
  omega

end FvModexp.Arm64.Run
