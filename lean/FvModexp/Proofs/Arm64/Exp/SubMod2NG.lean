import FvModexp.Proofs.Arm64.Exp.SubMod2NDefs

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64): the GENERAL statement `PreG` / `PostG` / `EnsG` (agent infra; proof in progress)

`z.subMod2N(z, y, n)` for ANY capacity of `z` (the `append` loop's `growslice` path, nat.go:1748-1750) and empty-tolerant
inputs (`z` and/or `y` may be `nil` / empty: expNNEven passes `expNN` results, which can be `nil`, FINDING "[infra s30]").
Differences to `Pre`: no `W n ≤ zc`; every fact about `z`'s pointer is guarded by `0 < zc`, every fact about `y`'s
pointer by `0 < yl` (or `0 < yc` for the apartness); budget `costG n` (each `growslice` of the loop costs at most
`gA n`, at most `W n` of them). `PostG` = `Post` with `costG` + the old budget when `W n ≤ zc` (no growth: `ens` is
derived from `EnsG`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-- one `growslice` of the `append` loop (new length `≤ W n`, `nextslicecap ≤ 2·newLen`) -/
@[reducible] def gA (n : Nat) : Nat := allocCost (8 * (2 * W n + 2))

/-- the general budget -/
@[reducible] def costG (n : Nat) : Nat := cost n + W n * gA n

@[reducible] def PreG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
    Prop :=
  CallEnv R L s K A ∧ Serves R ∧ Outside NatAdd.wordT 16 R.rt ∧ NatOne R L s.mem op (win s K A) ∧
    (0 < zc → Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8) ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ zc < 2 ^ 40 ∧ zl ≤ 2 ^ 12 ∧ yl ≤ yc ∧ yc < 2 ^ 40 ∧ yl ≤ 2 ^ 12 ∧
    NatLive s.mem R L zp zc ∧ (0 < zc → Outside zp (8 * zc) (win s K A) ∧
      Apart zp (8 * zc) ((s.regs 28).toNat + 16) 8) ∧ NatNorm s.mem zp zl ∧
    (0 < yl → s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧ Held R L yp (8 * yl) ∧
      Outside yp (8 * yl) (win s K A)) ∧ NatNorm s.mem yp yl ∧
    (0 < zc → 0 < yc → Apart zp (8 * zc) yp (8 * yc)) ∧ zp < 2 ^ 64 ∧ yp < 2 ^ 64 ∧
    costG n ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48

@[reducible] def PostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s s' : State) : Prop :=
  ∃ p' l' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = l' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n ∧
    NatNorm s'.mem p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - costG n ≤ b' ∧ (W n ≤ zc → b - cost n ≤ b') ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s K A ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)] ∧ (W n + 1 ≤ zc → p' = zp ∧ c' = zc)

/-- **the general summary** (to be proved: generalised S3/S4A (growslice)/S4B/S4C on the current array `(p, c)`;
empty-tolerant `cmp` / `sub` premises — see NOTES-infra "Session 31") -/
def EnsG (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (PreG R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n)

end FvModexp.Arm64.SubMod2N
