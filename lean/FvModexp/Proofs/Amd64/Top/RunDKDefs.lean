import FvModexp.Proofs.Amd64.Top.RunDJDefs
import FvModexp.Proofs.Amd64.Top.RunHMask

/-! # `Run` (amd64): small arithmetic facts of the exponent / modulus operands (`getData(input[96:], a, h)`)

The code computes `st = min(a, len - 96)`, `end = min(st + h, len - 96)` and the re-sliced pointer
`p + k + (st if st < cap - k else 0)` (`k = inOff len`). These lemmas are stated over plain `Nat`s so that `omega`
runs in a small context. -/

namespace FvModexp.Amd64.Run

/-- The source of operand `j`'s copy and its length: inside the input, at `p + 96 + a` when non-empty, and the
available length is `opAvail`'s `min h (len - 96 - a)`. -/
theorem opsrc {pp l cp a h st k : Nat} (hst : st = min a (l - 96)) (hk : k = if 96 < l then 96 else 0) (hcp : l ≤ cp) :
    pp ≤ pp + k + (if st < cp - k then st else 0) ∧
    pp + k + (if st < cp - k then st else 0) + (min (st + h) (l - 96) - st) ≤ pp + l ∧
    (0 < min (st + h) (l - 96) - st → pp + k + (if st < cp - k then st else 0) = pp + 96 + a) ∧
    min (st + h) (l - 96) - st = min h (l - 96 - a) := by
  subst hst hk
  split <;> split <;> omega

/-- The direct case `st + h ≤ len - 96`. -/
theorem opsrc_dir {pp l cp a h st k : Nat} (hst : st = min a (l - 96)) (hk : k = if 96 < l then 96 else 0)
    (hcp : l ≤ cp) (hd : st + h ≤ l - 96) :
    pp ≤ pp + k + (if st < cp - k then st else 0) ∧
    pp + k + (if st < cp - k then st else 0) + h ≤ pp + l ∧
    (0 < h → pp + k + (if st < cp - k then st else 0) = pp + 96 + a) := by
  subst hst hk
  split <;> split <;> omega

/-- The padded case: the available length is `len - 96 - st < h`. -/
theorem opavail_pad {l a h st : Nat} (hst : st = min a (l - 96)) (hd : l - 96 < st + h) :
    l - 96 - st = min h (l - 96 - a) := by
  subst hst; omega

open Janus Janus.Contracts in
/-- `n0_of_eq` for an operand starting at `a`: a fresh buffer at the copy source copies nothing. -/
theorem n0_of_eq' {R : RtInv} {L L0 : List (Nat × Nat)} {dst src e h0 n p l a : Nat} (heq : dst = src)
    (hfe : dst + h0 ≤ e) (hfrt : InRanges dst (e - dst) R.rt) (hheld : Held R L p l) (hext : LiveExt R L L0)
    (hsep : LiveSep L0 [(dst, e)]) (hsrc : 0 < n → src = p + 96 + a) (hs : src + n ≤ p + l) (hn : n ≤ h0) :
    n = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact h
  · exfalso
    have hs' := hsrc h
    rcases hheld with ⟨r, hr, h1, h2⟩ | hout
    · have := hsep r (hext.mem_old hr)
      simp only [Janus.outside_cons, Janus.outside_nil, and_true] at this
      omega
    · obtain ⟨r, hr, h1, h2⟩ := hfrt
      have := MemFrame.outside_mem hout hr
      omega

/-- `x - y` of two small `ofNat`s. -/
theorem ofNat_sub64 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
open Janus Janus.Amd64 in
/-- The `type:uint8` descriptor words read by `makeslice` (size 1, ptrdata 0), from the loaded rodata. -/
theorem uint8_words {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE 7231264 8 = 1 ∧ m.readLE 7231272 8 = 0 := by
  janus64_data hd
  exact ⟨by rw [h_rodata _ _ (by decide)]; decide, by rw [h_rodata _ _ (by decide)]; decide⟩

set_option maxRecDepth 20000 in
open Janus Janus.Amd64 in
theorem uint8_acc {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.accessible 7231264 16 false = true := by
  janus64_data hd; exact Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)

end FvModexp.Amd64.Run
