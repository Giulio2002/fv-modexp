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

end FvModexp.Amd64.Run
