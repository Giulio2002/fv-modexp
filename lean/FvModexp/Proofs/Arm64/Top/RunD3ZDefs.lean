import FvModexp.Proofs.Arm64.Top.RunD2Lem
import FvModexp.Proofs.Arm64.Top.RunD3J

/-!
# `Run` (arm64): the modulus operand, `makeslice` buffer with no input byte to copy: the cut after `makeslice`

`Z3` (`fn + 0x6f8`) is the return of `makeslice` in `RightPadBytes(getData(input, baseLen + expLen, modLen), modLen)` when the
input has fewer than `modLen` bytes left for the modulus (`nb` of them, the rest of the input): `X0` = the fresh zeroed buffer `B`, the slots `88(RSP)` (`len(src) = 0`) and
`400(RSP)` (`src`, a pointer into or one past the input) hold the `copy` arguments. From `Z3` the code compares
`src` with `B` and either skips the `memmove` (`B = src`, possible when `src` is one past the end of the input) or
calls it with 0 bytes; both paths reach `J3`. The two tails are separate modules (`RunD3ZE`, `RunD3ZN`). With `nb > 0`
bytes the source is inside the input, apart from `B`, and `RunD3LB` copies them.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcZ3 : Nat := segAddr Extracted.program fn + 0x6f8

/-- The state at `Z3`: as `JoinD3` without the `X1`, `X2`, `X7` facts, plus the two spilled `copy` arguments. -/
def JoinZ3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret : Nat)
    (Lk : List (Nat × Nat)) (bk B src nb : Nat) (U : State) : Prop :=
  U.sp = s.sp - 624#64 ∧ U.regs 28 = s.regs 28 ∧ U.regs 29 = s.sp - 632#64 ∧ U.regs 18 = s.regs 18 ∧
  U.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ U.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  U.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ U.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  U.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ U.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  U.mem.readLE (s.sp.toNat - 520) 8 = hdrV s p len 0 ∧ U.mem.readLE (s.sp.toNat - 528) 8 = hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ U.mem.readLE (s.sp.toNat - 480) 8 = len.toNat - 96 ∧
  U.mem.readLE (s.sp.toNat - 472) 8 = cp.toNat - inOff len ∧ U.mem.readLE (s.sp.toNat - 216) 8 = p.toNat + inOff len ∧
  U.mem.readLE (s.sp.toNat - 504) 8 = min (hdrV s p len 0) (len.toNat - 96) ∧
  U.mem.readLE (s.sp.toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 552) 8 = hdrV s p len 1 + hdrV s p len 0 ∧
  U.mem.readLE (s.sp.toNat - 192) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 184) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 176) 8 = 0 ∧
  hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024 ∧ ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) ∧
  32 < hdrV s p len 2 ∧
  (U.regs 0).toNat = B ∧ U.mem.readLE (s.sp.toNat - 544) 8 = nb ∧ U.mem.readLE (s.sp.toNat - 232) 8 = src ∧
  p.toNat ≤ src ∧ src ≤ p.toNat + len.toNat ∧
  B + hdrV s p len 2 ≤ 2 ^ 48 ∧ s.mem.accessible B (hdrV s p len 2) true = true ∧ Held R Lk B (hdrV s p len 2) ∧
  (B + hdrV s p len 2 ≤ s.sp.toNat - 624 - 4160 ∨ s.sp.toNat + 40 ≤ B) ∧
  InRanges B (hdrV s p len 2) R.rt ∧ LiveSep Lk [(B, B)] ∧
  (∀ j, j < hdrV s p len 2 → (U.mem.bytes (B + j)).toNat = 0) ∧
  len.toNat ≤ 96 + (hdrV s p len 0 + hdrV s p len 1) + nb ∧
  (0 < nb → src = p.toNat + 96 + (hdrV s p len 0 + hdrV s p len 1) ∧ src + nb = p.toNat + len.toNat ∧
    nb < hdrV s p len 2 ∧ (src + nb ≤ B ∨ B + blockSize (hdrV s p len 2) true ≤ src)) ∧
  Extracted.program.DataLoaded U.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → U.mem.readLE a n = s.mem.readLE a n) ∧
  U.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + 2 * dCost + allocCost 1024) ≤ bk ∧
  R.inv bk Lk (s.regs 28).toNat (view R.rt Lk U.mem) ∧ LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem U.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem U.mem L [] ∧ OpDone U.mem s p len Lk 0 ∧
  OpDone U.mem s p len Lk 1 ∧ OpsApart U.mem s 2 ∧
  ∃ L0 : List (Nat × Nat), Lk = L0 ++ [(B, B + blockSize (hdrV s p len 2) true)] ∧ LiveExt R L L0 ∧
    LiveSep L0 [(B, B + blockSize (hdrV s p len 2) true)] ∧ OpDone U.mem s p len L0 0 ∧ OpDone U.mem s p len L0 1

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

/-- A position at or past the end of the input reads as a padding zero. -/
theorem padByte_past {m : Memory} {p len j : Nat} (h : len ≤ j) : padByte m p len j = 0 := by
  unfold padByte; rw [if_neg (Nat.not_lt.2 h)]

end FvModexp.Arm64.Run
