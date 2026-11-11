import Extracted

/-! The restricted program of `github.com/ethereum/go-bigmodexpfix/src/math/big.addVW` (amd64, pinned Run extraction):
written as `scripts/gen-libprog-sub.py` would (segment `seg29` of the Run extraction). -/

namespace FvModexp.Amd64.LibAddVW
open Janus

def names : List String := ["github.com/ethereum/go-bigmodexpfix/src/math/big.addVW"]

def program : Amd64.Program := { Extracted.program with segments := [Extracted.seg29] }

theorem eq_only : program = Extracted.program.onlySegments names := by
  unfold program names; simp only [Amd64.Program.onlySegments]; congr 1

end FvModexp.Amd64.LibAddVW
