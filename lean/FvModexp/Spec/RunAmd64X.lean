import Janus
import Extracted

set_option autoImplicit false

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1b): two more facts about `math/big`'s package
globals at the call of amd64 `(*bigModExp).Run` (row 1, success half), kept in their own module so the existing
`Spec.RunAmd64` definitions stay unchanged.

* `math/big.hasADX` (`arith_amd64.go:11`: `var hasADX = cpu.X86.HasADX && cpu.X86.HasBMI2`, `.noptrbss`, 1 byte) is
  readable. The amd64 assembly `addMulVVWW` reads it to choose its code path (both paths are proved, so its VALUE is
  unconstrained); `(*Int).Mod` and `(*Int).exp` reach `addMulVVWW` through `nat.mul`/`nat.sqr`/`divBasic`.
* the backing word `natOne[0]` (`var natOne = nat{1}`, statically allocated in the data segment) is apart from the 32
  bytes of threshold globals at `divRecursiveThreshold` (`Spec.RunAmd64.Globals`): two distinct package variables do not
  overlap. `(*Int).exp`'s `nat.expNN` reads `natOne` while its callees read the thresholds. -/

namespace FvModexp.Spec.RunAmd64

open Janus Janus.Amd64 Janus.Spec

/-- `hasADX` readable; `natOne`'s word apart from the threshold globals (see the module doc) -/
def CpuOne (m : Memory) : Prop :=
  m.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
    Apart (m.readLE Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» 8) 8
      Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» 32

end FvModexp.Spec.RunAmd64
