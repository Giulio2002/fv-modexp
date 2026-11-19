import FvModexp.Proofs.Amd64.Exp.SubMod2NGEns
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): the row-level statement WITHOUT a return-address conjunct (agent infra s49)

`PreG`'s `Ent` carries `[RSP] < 2^47` (the return address); the final-gate RA rule (BRIEF "RETURN-ADDRESS PIN GAP")
forbids any constraint on `[RSP]` beyond the framework ABI predicates. `PreGR` = `PreG` without it (`EntR`); the fact
is re-derived from the ABI (`CallSetup.ret` + `RetAddr.user`) in `ensGR`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-- `Ent` without the return-address bound -/
@[reducible] def EntR (s : State) (zp zc n : Nat) : Prop :=
  Apart zp (8 * zc) (s.fsBase.toNat - 8) 8 ∧ s.mem.readLE ((s.regs 4).toNat + 8) 8 = n ∧ s.xmm 15 = 0 ∧
    s.df = false

/-- `PreG` with `EntR` in place of `Ent` -/
@[reducible] def PreGR (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
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
    (cost n ≤ b ∧ (zc < W n → costG n ≤ b)) ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ EntR s zp zc n

theorem PreGR.toG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (h : PreGR R b L op zp zl zc yp yl yc n s) (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    PreG R b L op zp zl zc yp yl yc n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, e1, e2, e3, e4⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, e1, hr, e2, e3, e4⟩

/-- the general summary on `PreGR` -/
def EnsGR (impl : List Amd64.Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc]
      (PreGR R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n)

/-- `EnsG` gives `EnsGR`: the return-address bound comes from the ABI (`CallSetup.ret`, `RetAddr.user`) -/
theorem ensGR_of {impl : List Amd64.Segment} {R : RtInv} (h : EnsG impl R) : EnsGR impl R := by
  intro b L op zp zl zc yp yl yc n
  janus64_ensures_old [FvModexp.Amd64.SubMod2N.PreGR, FvModexp.Amd64.CallEnv, FvModexp.Amd64.SubMod2N.K, FvModexp.Amd64.SubMod2N.A, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.NatLive, FvModexp.Amd64.SubMod2N.EntR, FvModexp.Amd64.TlsOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet]
  intro ret hret s hs hpre
  exact (h b L op zp zl zc yp yl yc n).toOld ret hret s hs (hpre.toG (by rw [hs.ret]; exact hret.user))

end FvModexp.Amd64.SubMod2N
