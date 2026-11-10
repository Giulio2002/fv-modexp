import FvModexp.Proofs.Arm64.Top.RunDefs

/-!
# `Run` (arm64): the facts at the segment boundaries of the header phase

`RelH R b L c p len cp s ret k Lk bk S`: at a boundary after `k` length headers, the state `S` relative to the call state
`s`: Run's frame (`SP' = SP - 624`, `X29 = SP - 632`, the saved `X29`/`X30`, the four spilled arguments), the read-only
data, the input and receiver bytes unchanged, the runtime (`Lk`, `bk`), the frames, and the header `nat`s read so far
(`A`, `B`, `C` at `SP - 32`, `SP - 64`, `SP - 96`): value = EthLib's padded read of the length field, normalised, array
held in `Lk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- Where header `i`'s `nat` (`abs` of the stack `big.Int`) lives. -/
@[reducible] def hdrAt (s : State) (i : Nat) : Nat := s.sp.toNat - 32 - 32 * i

/-- Header `i` of the call data `(p, len)`: EthLib's `readNat data (32 i) 32`, as `padBE`. -/
@[reducible] def hdrV (s : State) (p len : BitVec 64) (i : Nat) : Nat := padBE s.mem p.toNat len.toNat (32 * i) 32

/-- Header `i` is read into the frame: value, normal form, and its array is a live object of `Lk`. -/
def HdrDone (m : Memory) (s : State) (p len : BitVec 64) (Lk : List (Nat × Nat)) (i : Nat) : Prop :=
  HdrOK m (hdrAt s i) (hdrV s p len i) ∧
    (0 < m.readLE (hdrAt s i + 16) 8 → InRanges (m.readLE (hdrAt s i) 8) (8 * m.readLE (hdrAt s i + 16) 8) Lk)

def RelH (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret k : Nat)
    (Lk : List (Nat × Nat)) (bk : Nat) (S : State) : Prop :=
  S.sp = s.sp - 624#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 632#64 ∧ S.regs 18 = s.regs 18 ∧
  S.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ S.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ S.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ S.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  (1 ≤ k → S.mem.readLE (s.sp.toNat - 488) 8 = min len.toNat 32 ∧
    S.mem.readLE (s.sp.toNat - 496) 8 = min len.toNat 32 + 32) ∧
  Extracted.program.DataLoaded S.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → S.mem.readLE a n = s.mem.readLE a n) ∧
  S.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - k * makeCost 4 ≤ bk ∧ R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem) ∧
  LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem S.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem S.mem L [] ∧
  (∀ i, i < k → HdrDone S.mem s p len Lk i)

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The call-data and receiver part of Run's precondition (both ISAs share its shape). -/
def InputOK (R : RtInv) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) : Prop :=
  s.mem.accessible c.toNat 3 false = true ∧ c.toNat + 3 ≤ 2 ^ 48 ∧ Held R L c.toNat 3 ∧
    Outside c.toNat 3 (win s stk 40) ∧
    p.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat ≤ cp.toNat ∧ cp.toNat < 2 ^ 48 ∧
    s.mem.accessible p.toNat len.toNat false = true ∧ Held R L p.toNat len.toNat ∧
    Outside p.toNat len.toNat (win s stk 40)

/-- The requests of the header phase (three `nat.make(4)` of the std `math/big` copy; small copies when the input is
shorter than the 96 header bytes). -/
def HdrOkR (R : RtInv) (b : Nat) (len : BitVec 64) : Prop :=
  R.ok (cA "runtime.makeslice") [SetBytesStd.wordT, 4, makeCap 4] ∧ 3 * makeCost 4 ≤ b ∧
    (len.toNat < 96 → ∀ d sr n, n ≤ 32 → R.ok (cA "runtime.memmove") [d, sr, n])

abbrev pcB1 : Nat := segAddr Extracted.program fn + 0xe4
abbrev pcB2 : Nat := segAddr Extracted.program fn + 0x19c
abbrev pcB3 : Nat := segAddr Extracted.program fn + 0x25c

end FvModexp.Arm64.Run
