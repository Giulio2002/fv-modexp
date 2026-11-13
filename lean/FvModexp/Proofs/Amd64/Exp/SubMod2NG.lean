import FvModexp.Proofs.Amd64.Exp.SubMod2NDefs
import FvModexp.Proofs.Amd64.Exp.LibW

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): the GENERAL statement `PreG` / `PostG` / `EnsG` (agent infra s47; twin of
`FvModexp.Arm64.SubMod2N.PreG` …, Arm64/Exp/SubMod2NG.lean)

`z.subMod2N(z, y, n)` for ANY capacity of `z` (the `append` loop's `growslice` path, nat.go:1748-1750) and empty-tolerant
inputs (`z` and/or `y` may be `nil` / empty). `PreG` has the SAME 28 conjuncts as the amd64 `Pre` (positions kept),
weakened in place exactly as on arm64:
* slot 10 (`W n ≤ zc`) is `zp < 2^64 ∧ yp < 2^64`;
* `y`'s pointer facts (slots 20-23) are guarded by `0 < yl`, the apartness of `z` and `y` (slot 25) by `0 < zc ∧ 0 < yl`;
* slot 26: the budget `cost n`, and `costG n` when `cap z < W n` (≤ `W n` growslices of at most `gA n` each);
* slot 28: the amd64 entry facts `Ent` (TLS apartness, return address, `n` at `[RSP + 8]`, `X15 = 0`, `DF = 0`).
`PostG` = the amd64 `Post` with `costG` + the old budget when `W n ≤ zc`. The summary `EnsG` is on amd64 `LibW` (as
arm64's; NESTED-PROGRAM RULE: it leaves out `expNNEven`/`expNN`). PROOF: TODO (port of the arm64 G chain
SubMod2NGL/GC/GAlloc/GS1…GS4Cb/GEns; plan in NOTES-infra "Session 47").
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

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
    NatLive s.mem R L zp zc ∧ Outside zp (8 * zc) (win s K A) ∧ Apart zp (8 * zc) ((s.regs 14).toNat + 16) 8 ∧
    NatNorm s.mem zp zl ∧
    (0 < yl → s.mem.accessible yp (8 * yl) false = true) ∧ (0 < yl → yp + 8 * yl ≤ 2 ^ 48) ∧
    (0 < yl → Held R L yp (8 * yl)) ∧ (0 < yl → Outside yp (8 * yl) (win s K A)) ∧ NatNorm s.mem yp yl ∧
    (0 < zc → 0 < yl → Apart zp (8 * zc) yp (8 * yc)) ∧
    (cost n ≤ b ∧ (zc < W n → costG n ≤ b)) ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ Ent s zp zc n

@[reducible] def PostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p' l' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = l' ∧ (s'.regs 1).toNat = c' ∧
    natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n ∧
    NatNorm s'.mem p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - costG n ≤ b' ∧ (W n ≤ zc → b - cost n ≤ b') ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s K A ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)] ∧ (W n + 1 ≤ zc → p' = zp ∧ c' = zc)

/-! ## `Pre` / `Post` as special cases -/

theorem cost_le_costG (n : Nat) : cost n ≤ costG n := Nat.le_add_right _ _

set_option maxRecDepth 20000 in
theorem Pre.toG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (h : Pre R b L op zp zl zc yp yl yc n s) : PreG R b L op zp zl zc yp yl yc n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, a28⟩ := h
  have : 0 < zc := Nat.lt_of_lt_of_le (by unfold W; omega) a10
  have hz := (a16 this).2.2.2
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ⟨by omega, by omega⟩, a11, a12, a13, a14, a15, a16,
    a17, a18, a19, fun _ => a20, fun _ => a21, fun _ => a22, fun _ => a23, a24, fun _ _ => a25,
    ⟨a26, fun h => absurd a10 (by omega)⟩, a27, a28⟩

theorem PostG.toPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n : Nat} {s s' : State}
    (hW : W n ≤ zc) (h : PostG R b L zp zl zc yp yl n s s') : Post R b L zp zl zc yp yl n s s' := by
  obtain ⟨f1, f2, p', l', c', e0, e1, e2, hv, hn, hlc, hc, L', b', hLE, -, hb, hinv, hlive, hor, hF, hLF, hre⟩ := h
  exact ⟨f1, f2, p', l', c', e0, e1, e2, hv, hn, hlc, hc, L', b', hLE, hb hW, hinv, hlive, hor, hF, hLF, hre⟩

/-- the general summary (to be proved by the amd64 port of the arm64 G chain) -/
def EnsG (impl : List Amd64.Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc]
      (PreG R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n)

end FvModexp.Amd64.SubMod2N
