import FvModexp.Proofs.Arm64.Top.RunD2Lem
import FvModexp.Proofs.Arm64.Top.RunD2J

/-!
# `Run` (arm64): the exponent operand, `makeslice` buffer with no input byte to copy: the cut after `makeslice`

`Z2` (`fn + 0x5cc`) is the return of `makeslice` in `RightPadBytes(getData(input, baseLen, expLen), expLen)` when the
input has no byte left for the exponent: `X0` = the fresh zeroed buffer `B`, the slots `88(RSP)` (`len(src) = 0`) and
`400(RSP)` (`src`, a pointer into or one past the input) hold the `copy` arguments. From `Z2` the code compares
`src` with `B` and either skips the `memmove` (`B = src`, possible when `src` is one past the end of the input) or
calls it with 0 bytes; both paths reach `J2`. The two tails are separate modules (`RunD2ZE`, `RunD2ZN`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcZ2 : Nat := segAddr Extracted.program fn + 0x5cc

/-- The state at `Z2`: as `JoinD2` without the `X1`, `X2`, `X7` facts, plus the two spilled `copy` arguments. -/
def JoinZ2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret : Nat)
    (Lk : List (Nat × Nat)) (bk B src : Nat) (U : State) : Prop :=
  U.sp = s.sp - 624#64 ∧ U.regs 28 = s.regs 28 ∧ U.regs 29 = s.sp - 632#64 ∧ U.regs 18 = s.regs 18 ∧
  U.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ U.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  U.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ U.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  U.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ U.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  U.mem.readLE (s.sp.toNat - 520) 8 = hdrV s p len 0 ∧ U.mem.readLE (s.sp.toNat - 528) 8 = hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ U.mem.readLE (s.sp.toNat - 480) 8 = len.toNat - 96 ∧
  U.mem.readLE (s.sp.toNat - 472) 8 = cp.toNat - inOff len ∧ U.mem.readLE (s.sp.toNat - 216) 8 = p.toNat + inOff len ∧
  U.mem.readLE (s.sp.toNat - 504) 8 = min (hdrV s p len 0) (len.toNat - 96) ∧
  U.mem.readLE (s.sp.toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 160) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 152) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 144) 8 = 0 ∧
  hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024 ∧ ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) ∧
  32 < hdrV s p len 1 ∧
  (U.regs 0).toNat = B ∧ U.mem.readLE (s.sp.toNat - 536) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 224) 8 = src ∧
  p.toNat ≤ src ∧ src ≤ p.toNat + len.toNat ∧
  B + hdrV s p len 1 ≤ 2 ^ 48 ∧ s.mem.accessible B (hdrV s p len 1) true = true ∧ Held R Lk B (hdrV s p len 1) ∧
  (B + hdrV s p len 1 ≤ s.sp.toNat - 624 - 4160 ∨ s.sp.toNat + 40 ≤ B) ∧
  InRanges B (hdrV s p len 1) R.rt ∧ LiveSep Lk [(B, B)] ∧
  (∀ j, j < hdrV s p len 1 →
    (U.mem.bytes (B + j)).toNat = padByte s.mem p.toNat len.toNat (96 + hdrV s p len 0 + j)) ∧
  Extracted.program.DataLoaded U.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → U.mem.readLE a n = s.mem.readLE a n) ∧
  U.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + dCost + allocCost 1024) ≤ bk ∧
  R.inv bk Lk (s.regs 28).toNat (view R.rt Lk U.mem) ∧ LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem U.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem U.mem L [] ∧ OpDone U.mem s p len Lk 0

end FvModexp.Arm64.Run

