import Extracted

/-! The restricted program of `github.com/ethereum/go-bigmodexpfix/src/math/big.addVW` (arm64, pinned Run extraction):
written as `scripts/gen-libprog-sub.py` would (segment `seg29` of the Run extraction). -/

namespace FvModexp.Arm64.LibAddVW
open Janus

def names : List String := ["github.com/ethereum/go-bigmodexpfix/src/math/big.addVW"]

def program : Program := { Extracted.program with segments := [Extracted.seg29] }

theorem eq_only : program = Extracted.program.onlySegments names := by
  unfold program names; simp only [Program.onlySegments]; congr 1

end FvModexp.Arm64.LibAddVW
