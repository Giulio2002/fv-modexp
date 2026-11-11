import Extracted

/-! The restricted program of `github.com/ethereum/go-bigmodexpfix/src/math/big.subVW` (amd64, pinned Run extraction):
written as `scripts/gen-libprog-sub.py` would (segment `seg25` of the Run extraction). -/

namespace FvModexp.Amd64.LibSubVW
open Janus

def names : List String := ["github.com/ethereum/go-bigmodexpfix/src/math/big.subVW"]

def program : Amd64.Program := { Extracted.program with segments := [Extracted.seg25] }

theorem eq_only : program = Extracted.program.onlySegments names := by
  unfold program names; simp only [Amd64.Program.onlySegments]; congr 1

end FvModexp.Amd64.LibSubVW
