import FvModexp.Proofs.Arm64.Exp.SubMod2NCall

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64): the GENERAL statement `PreG` / `PostG` / `EnsG` and its join points (agent infra)

`z.subMod2N(z, y, n)` for ANY capacity of `z` (the `append` loop's `growslice` path, nat.go:1748-1750) and empty-tolerant
inputs (`z` and/or `y` may be `nil` / empty: expNNEven passes `expNN` results, which can be `nil`, FINDING "[infra s30]").

`PreG` has the SAME 29 conjuncts as `Pre` (positions kept, so the segment proofs read them alike), weakened in place:
* slot 10 (`W n ≤ zc` in `Pre`) is `zp < 2^64 ∧ yp < 2^64` (register values; no capacity bound on `z`);
* the facts about `y`'s pointer (slots 20-23) are guarded by `0 < yl`, the apartness of `z` and `y` (slot 25) by
  `0 < zc ∧ 0 < yl`; `z`'s window / guard / `natOne` facts (slots 5, 6, 17, 18) stay: for `cap z = 0` they say that
  `z`'s pointer is not strictly inside those ranges (true for `nil` and for any runtime pointer), which the frame
  reasoning over `[(zp, zp + 8 zc)]` needs;
* slot 26: the budget `cost n`, and `costG n` when `cap z < W n` (each `growslice` of the loop costs at most `gA n`,
  at most `W n` of them; with `W n ≤ cap z` the loop never grows).
`PostG` = `Post` with `costG` + the old budget when `W n ≤ zc` (no growth).

`nat.sub` is called with operands that may be empty with an arbitrary pointer (`x'` in a nil `z`, `y' = y` nil): its
premise is `SubHypR0` (`SubPre0` = `NatSub.Pre` with the operand facts of RdIn0 shape, coordinator decision on
"[infra s30] FINDING"; divmc delivers it as a derived summary). `nat.cmp` already accepts empty operands (`CmpW.pre_of`).
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
    Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ (zp < 2 ^ 64 ∧ yp < 2 ^ 64) ∧ zc < 2 ^ 40 ∧ zl ≤ 2 ^ 12 ∧ yl ≤ yc ∧
    yc < 2 ^ 40 ∧ yl ≤ 2 ^ 12 ∧
    NatLive s.mem R L zp zc ∧ Outside zp (8 * zc) (win s K A) ∧
    Apart zp (8 * zc) ((s.regs 28).toNat + 16) 8 ∧ NatNorm s.mem zp zl ∧
    (0 < yl → s.mem.accessible yp (8 * yl) false = true) ∧ (0 < yl → yp + 8 * yl ≤ 2 ^ 48) ∧
    (0 < yl → Held R L yp (8 * yl)) ∧ (0 < yl → Outside yp (8 * yl) (win s K A)) ∧ NatNorm s.mem yp yl ∧
    (0 < zc → 0 < yl → Apart zp (8 * zc) yp (8 * yc)) ∧
    (cost n ≤ b ∧ (zc < W n → costG n ≤ b)) ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
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

/-! ## `nat.sub` with empty-tolerant operands -/

/-- `NatSub.Pre` with the operand facts in RdIn0 shape: pointer facts of `x` / `y` only when non-empty, `z`'s window
fact only when `0 < cap z` -/
def SubPre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4304 80 ∧ Outside NatSub.wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧
    xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4304 80)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (0 < yl.toNat → zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4304 80)) ∧
    NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧
    (0 < yl.toNat → s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
      Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s 4304 80)) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [NatSub.wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

/-- `SubHypR` with empty-tolerant operands (premise until divmc's derived `nat.sub` summary lands) -/
def SubHypR0 (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatSub.names).link impl) (segAddr Extracted.program NatSub.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (SubPre0 R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatSub.Post R b L zp zc xp xl yp yl s s' ∧
        (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
        (xl.toNat < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40))

/-- the old `NatSub.Pre` gives `SubPre0` -/
theorem subPre0_of_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : NatSub.Pre R b L zp zc xp xl xc yp yl yc s) : SubPre0 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun _ => a13,
    fun hz => ⟨(a14 hz).1, fun _ => (a14 hz).2.1, fun _ => (a14 hz).2.2⟩, fun _ => ⟨a15, a16, a17, a20⟩, a18, a19,
    fun _ => ⟨a21, a22, a23, a24⟩, a25, a26, a27⟩

/-! ## The goal and the join points -/

/-- what the function promises (general form), from a state `S` inside its frame (entry state `s`) -/
@[reducible] def GoalG (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat)
    (s S : State) : Prop :=
  ReachesRet (LibW.program.link impl) (s.regs 30) S (fun s' =>
    (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
      PostG R b L zp zl zc yp yl n s s')

/-- the current array `(p, c)` of `z` (after `z.sub`, the `append` loop): `z`'s own or a fresh runtime one -/
@[reducible] def CurA (R : RtInv) (L : List (Nat × Nat)) (zp zc p c : Nat) : Prop :=
  (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)

/-- **J1G** (`+0xfc`): `x' = x mod 2^n` in `z`'s array (`X0..X2 = z`, `X3..X5 = x'`, `X6..X8 = y`, `X9 = n`) -/
def J1G (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0xfc) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 zl → S.regs 2 = BitVec.ofNat 64 zc →
    S.regs 3 = BitVec.ofNat 64 zp → S.regs 4 = BitVec.ofNat 64 l1 → S.regs 5 = BitVec.ofNat 64 zc →
    S.regs 6 = BitVec.ofNat 64 yp → S.regs 7 = BitVec.ofNat 64 yl → S.regs 8 = BitVec.ofNat 64 yc →
    S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 1 S.mem L1 b1 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ zc →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J2G** (`+0x1c8`): `x'` as at `J1G` (`X3..X5`), `y' = y mod 2^n` (`X6..X8`: `y`'s or a fresh array; its pointer
facts only when non-empty); the locals `x'` at `SP - 16 / - 40 / - 32` stored -/
def J2G (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 p2 l2 c2 : Nat) (L2 : List (Nat × Nat)) (b2 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x1c8) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 3 = BitVec.ofNat 64 zp → S.regs 4 = BitVec.ofNat 64 l1 → S.regs 5 = BitVec.ofNat 64 zc →
    S.regs 6 = BitVec.ofNat 64 p2 → S.regs 7 = BitVec.ofNat 64 l2 → S.regs 8 = BitVec.ofNat 64 c2 →
    Fw s S.mem zp zl zc yp n → S.mem.readLE (s.sp.toNat - 16) 8 = zp → S.mem.readLE (s.sp.toNat - 40) 8 = l1 →
    S.mem.readLE (s.sp.toNat - 32) 8 = zc → Rt R b L s zp zc n 2 S.mem L2 b2 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ W n → l1 ≤ zc →
    natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n → NatNorm S.mem p2 l2 → l2 ≤ W n → l2 ≤ c2 → c2 < 2 ^ 40 →
    p2 < 2 ^ 64 →
    (0 < l2 → S.mem.accessible p2 (8 * l2) false = true ∧ p2 + 8 * l2 ≤ 2 ^ 48 ∧ Held R L2 p2 (8 * l2) ∧
      (p2 + 8 * l2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p2) ∧ (0 < zc → Apart zp (8 * zc) p2 (8 * l2))) →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J3G** (`+0x21c`, after `z = z.sub(y', x')` with `x' < y'`): `z = (p3, l3, c3)` (`X0..X2`) holds `y' - x'`, in
`z`'s array or a fresh one -/
def J3G (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (p3 l3 c3 : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x21c) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 p3 → S.regs 1 = BitVec.ofNat 64 l3 → S.regs 2 = BitVec.ofNat 64 c3 →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    NatLive S.mem R L3 p3 c3 → CurA R L zp zc p3 c3 → c3 < 2 ^ 40 → p3 < 2 ^ 64 → l3 ≤ c3 → (W n ≤ zc → p3 = zp ∧ c3 = zc) →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem p3 l3 = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → NatNorm S.mem p3 l3 → l3 ≤ W n →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J4G** (`+0x28c`): after `for len(z)*64 < n { z = append(z, 0) }`: `z = (p, ⌈n/64⌉, c)`, `g` growths so far
(the budget `b - g · gA n` is what the runtime facts are relative to) -/
def J4G (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (p c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x28c) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 p → S.regs 1 = BitVec.ofNat 64 (W n) → S.regs 2 = BitVec.ofNat 64 c →
    S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 →
    NatLive S.mem R L3 p c → CurA R L zp zc p c → c < 2 ^ 40 → p < 2 ^ 64 → W n ≤ c → g ≤ W n →
    (W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem p (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J5G** (`+0x2ac`): after `for i := range z { z[i] = ^z[i] }`: value `B^W - 1 - d` -/
def J5G (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (p c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x2ac) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 p → S.regs 1 = BitVec.ofNat 64 (W n) → S.regs 2 = BitVec.ofNat 64 c →
    S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 →
    NatLive S.mem R L3 p c → CurA R L zp zc p c → c < 2 ^ 40 → p < 2 ^ 64 → W n ≤ c → g ≤ W n →
    (W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem p (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) →
    GoalG impl R b L zp zl zc yp yl n s S

/-! ## `Pre` / `Post` as special cases -/

theorem cost_le_costG (n : Nat) : cost n ≤ costG n := Nat.le_add_right _ _

set_option maxRecDepth 20000 in
theorem Pre.toG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (h : Pre R b L op zp zl zc yp yl yc n s) : PreG R b L op zp zl zc yp yl yc n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, a28, a29⟩ := h
  have : 0 < zc := Nat.lt_of_lt_of_le (by unfold W; omega) a10
  have hz := (a16 this).2.2.2
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ⟨by omega, by omega⟩, a11, a12, a13, a14, a15, a16,
    a17, a18, a19, fun _ => a20, fun _ => a21, fun _ => a22, fun _ => a23, a24, fun _ _ => a25,
    ⟨a26, fun h => absurd a10 (by omega)⟩, a27, a28, a29⟩

theorem PostG.toPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n : Nat} {s s' : State}
    (hW : W n ≤ zc) (h : PostG R b L zp zl zc yp yl n s s') : Post R b L zp zl zc yp yl n s s' := by
  obtain ⟨p', l', c', e0, e1, e2, hv, hn, hlc, hc, L', b', hLE, -, hb, hinv, hlive, hor, hF, hLF, hre⟩ := h
  exact ⟨p', l', c', e0, e1, e2, hv, hn, hlc, hc, L', b', hLE, hb hW, hinv, hlive, hor, hF, hLF, hre⟩

/-- the general summary (proved in `SubMod2NGEns`) -/
def EnsG (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (PreG R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n)

end FvModexp.Arm64.SubMod2N
