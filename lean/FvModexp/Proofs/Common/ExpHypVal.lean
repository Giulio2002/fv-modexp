/-!
# Value meaning of the comparison result of `nat.cmp` (nat.go:84-110), ISA-independent

`x.cmp(y)`: lengths first (`m < n → -1`, `m > n → 1`), equal lengths (incl. 0) compare the limbs from the top, which is
the numeric comparison of the two `len`-limb values.
-/

namespace FvModexp.Exp

/-- the `int` result of `x.cmp(y)` for limb counts `xl`, `yl` and values `X`, `Y` (values of exactly `xl`/`yl` limbs) -/
def cmpVal (xl yl X Y : Nat) : Int :=
  if xl < yl then -1 else if yl < xl then 1 else if X < Y then -1 else if X = Y then 0 else 1

end FvModexp.Exp
