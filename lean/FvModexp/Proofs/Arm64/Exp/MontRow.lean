import FvModexp.Proofs.Arm64.Exp.Mont
import FvModexp.Proofs.Arm64.Nat.RowLink

/-!
# Calibration row: `nat.montgomery` (arm64) verified standalone on the Run extraction
`correctness` = `Mont.ens` moved to `Extracted.program.link impl` (`Ensures.full`, divmc's RowLink). No witness yet.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.MontRow

theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc mp ml mc k n : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery")
      [zp, zl, zc, xp, xl, xc, yp, yl, yc, mp, ml, mc, k, n]
      (Mont.Pre R b L zp zc xp xl yp yl mp ml mc k n) (Mont.Post R b L zp zc xp yp mp k n) :=
  Ensures.full hap (Mont.ens impl hap R hclr hmv b L zp zl zc xp xl xc yp yl yc mp ml mc k n)

end FvModexp.Arm64.MontRow
