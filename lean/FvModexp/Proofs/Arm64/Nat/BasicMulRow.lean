import FvModexp.Proofs.Arm64.Nat.BasicMul
import FvModexp.Proofs.Arm64.Nat.RowLink

/-!
# Calibration row: `basicMul` (arm64) verified standalone on the Run extraction
`correctness` = `BasicMul.ens` moved to `Extracted.program.link impl` (`Ensures.full`). No witness yet.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.BasicMulRow

theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.basicMul")
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (BasicMul.Pre R b L zp zl zc xp xl yp yl) (BasicMul.Post R b L zp xp xl yp yl) :=
  Ensures.full hap (BasicMul.ens impl hap R hmc b L zp zl zc xp xl xc yp yl yc)

end FvModexp.Arm64.BasicMulRow
