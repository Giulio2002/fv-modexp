import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.Exp.SlowSqG
import FvModexp.Proofs.Amd64.NatQ.DivGDefsQ
import FvModexp.Proofs.Amd64.Exp.SlowQStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the interface between the upper loop (expmc) and the lower loop + exits (asm)
(agent expmc s81)

* `perBQ` — the per-body budget bound (box maxima of the level-free callee costs).
* `FQ` — the function's return post as a `Summary` post (`RSP + 8`, `RBP`/`R14`/`X15` kept, then `NHyp.CPostR0Q`
  with the exported window `stk = K + 0x1b8`, `above = 0x70`) — twin of arm64 `FQQ`.
* `LowQ` — the statement asm proves (twin of the arm64 tail of `bodyQ`: `exitUQ` + `lowerQ` + `segFinQ`): from the
  upper-loop exit (`KT1` at `j = w`, `t1`), with the remaining budget `B0 + perBQ · 64 (len y - 1)` and the model
  `outerLoop … (len y - 1) v 0 Zv = F`, the function returns with `FQ … F cst`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the per-body budget bound -/
@[reducible] def perBQ (sqC : Nat → Nat) (mlC dvC : Nat → Nat → Nat) (xl ml : Nat) : Nat :=
  Exp.supN sqC (max xl ml) + Exp.supN (fun n => mlC n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC n ml) (3 * max xl ml)

/-- the function's return post (a `Summary` post of `LibW.program.link impl`) -/
@[reducible] def FQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    NHyp.CPostR0Q R b L (K + 0x1b8) 0x70 zp zc st v (cst + stkR H s.mem st) (stkR H s'.mem st) s s'

/-- **the lower loop + exits** (asm), callee premises as in `loopU` -/
def LowQ (impl : List Amd64.Segment) (ns : List String) (dvC : Nat → Nat → Nat) : Prop :=
  ∀ {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {W1 W2 W3 H : Nat},
    SqrE0 impl R ns W1 → Q.DivRec.MulHypQE impl R ns W2 → DivHypLGQ impl R ns W3 0x70 dvC →
    7104 ≤ W1 → 21072 ≤ W2 → W1 ≤ K → W2 ≤ K → W3 ≤ K →
    EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s →
    NHyp.XFacts R L xp xl xc → 0 < xl → 0 < natVal s.mem mp ml →
    stLen s.mem st + 48 * max xl ml + 64 ≤ H →
    ∀ {B0 cst F : Nat}, b - (cst + stkR H s.mem st) ≤ B0 →
    ∀ (S : State) (L1 : List (Nat × Nat)) (b1 w : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat),
      KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 w w v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc →
      B0 + perBQ sqrCQ mulCQ dvC xl ml * (64 * (yl - 1)) + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 (yl - 1)
        v.toNat 0 Zv = F →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b H L K zp zc st F cst s)

end FvModexp.Amd64.ExpSlow
