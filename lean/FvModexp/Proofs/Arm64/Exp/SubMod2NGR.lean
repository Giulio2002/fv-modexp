import FvModexp.Proofs.Arm64.Exp.SubMod2NGEns
import FvModexp.Proofs.Arm64.Exp.RAx30

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64): the row-level statement WITHOUT a return-address conjunct (agent infra s49)

`PreG` ends with `X30 % 4 = 0 ∧ X30 < 2^48` (the return address; the proof needs it for the final `RET`); the
final-gate RA rule (BRIEF "RETURN-ADDRESS PIN GAP") forbids any constraint on `X30` beyond the framework ABI
predicates. `PreGR` = `PreG` without it; both facts are re-derived from the ABI (`CallSetup.lr` +
`RetAddr.aligned` / `RetAddr.user`) in `ensGR_of`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-- `PreG` without the `X30` conjuncts -/
@[reducible] def PreGR (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
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
    (cost n ≤ b ∧ (zc < W n → costG n ≤ b)) ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

theorem PreGR.toG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (h : PreGR R b L op zp zl zc yp yl yc n s) (h1 : (s.regs 30).toNat % 4 = 0) (h2 : (s.regs 30).toNat < 2 ^ 48) :
    PreG R b L op zp zl zc yp yl yc n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, h1, h2⟩

/-- the general summary on `PreGR` -/
def EnsGR (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (PreGR R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n)

/-- `EnsG` gives `EnsGR` (the `X30` facts from the ABI, `RAx30.ens_drop`) -/
theorem ensGR_of {impl : List Segment} {R : RtInv} (h : EnsG impl R) : EnsGR impl R :=
  fun b L op zp zl zc yp yl yc n =>
    RAx30.ens_drop (fun _ hp h1 h2 => hp.toG h1 h2) (h b L op zp zl zc yp yl yc n)

end FvModexp.Arm64.SubMod2N
