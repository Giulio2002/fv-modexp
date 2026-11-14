import FvModexp.Proofs.Amd64.Exp.SlowPE
import FvModexp.Proofs.Amd64.Exp.SlowPM
import FvModexp.Proofs.Amd64.Exp.SlowPV
import FvModexp.Proofs.Amd64.Exp.SlowLoopU
import FvModexp.Proofs.Amd64.Exp.SlowLoopL
import FvModexp.Proofs.Amd64.Exp.SlowQStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64), Q-form: the whole function from the entry facts (agent expmc s82; twin of arm64
`Arm64/ExpQ/SlowFunQ.bodyQ`)

`segE` (prologue, `z.make`) → `segM` (`z.set(x)` memmove) → `segV` (`v`, `w`, model `outerLoop … (len y - 1) v w X`)
→ `loopU` (upper loop, `w` bodies) → asm's `afterU` (= `loopU`'s exit continuation: `t1x`, the lower loop, `ex`, RET).
Budget: `B0 = b − (cost + stkR H s.mem st)`; the stack capacity is unchanged through the prologue (`capW`, `segM`,
`segV`), so the loop starts with reserve `stkR H s.mem st`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.ExpSlow

theorem costQ_eq (sqC : Nat → Nat) (mlC dvC : Nat → Nat → Nat) (xl yl ml : Nat) :
    costQ sqC mlC dvC xl yl ml = makeCost xl + perBQ sqC mlC dvC xl ml * (64 * yl) := by
  unfold costQ perBQ; rw [Nat.mul_comm (64 * yl)]

/-- the loop-entry budget step (small context) -/
theorem ent_bud {b cst r0 mk P w yl b1 : Nat} (hcst : cst + r0 ≤ b) (hce : cst = mk + P * (64 * yl))
    (hb1 : b - mk ≤ b1) (hw : w ≤ 63) (hyl : 0 < yl) :
    b - (cst + r0) + P * (w + 64 * (yl - 1)) + r0 ≤ b1 := by
  have : P * (w + 64 * (yl - 1)) ≤ P * (64 * yl) := Nat.mul_le_mul_left _ (by omega)
  omega

end FvModexp.Amd64.Q.ExpSlow

namespace FvModexp.Amd64.ExpSlow

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNSlow` (amd64)**: entry `fnE` → RET with `FQS` (Q-form cost `costQ sqrCQ mulCQ dvC`) -/
theorem bodyQ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W1 W2 W3 H : Nat} {dvC : Nat → Nat → Nat}
    (hsq : SqrE0 impl R ns W1) (hW1K : W1 ≤ K) (hW1 : 7104 ≤ W1)
    (hml : Q.DivRec.MulHypQE impl R ns W2) (hW2K : W2 ≤ K) (hW2 : mulWX64 ≤ W2)
    (hdv : DivHypLGQ impl R ns W3 0x70 dvC) (hW3K : W3 ≤ K)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hx0 : 0 < natVal s.mem xp xl) (hM : 0 < natVal s.mem mp ml)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H)
    (hcst : Q.ExpSlow.costQ sqrCQ mulCQ dvC xl yl ml + stkR H s.mem st ≤ b)
    (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zc) (h7 : s.regs 7 = BitVec.ofNat 64 st)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl) (h9 : s.regs 9 = BitVec.ofNat 64 xc) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) s
      (FQS R b H L K zp zc st (Exp.expNNSlow (natVal s.mem xp xl) (natVal s.mem yp yl) (natVal s.mem mp ml))
        (Q.ExpSlow.costQ sqrCQ mulCQ dvC xl yl ml) s) := by
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hx0
    · exact h
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.1
  generalize hF : Exp.expNNSlow (natVal s.mem xp xl) (natVal s.mem yp yl) (natVal s.mem mp ml) = F
  generalize hC : Q.ExpSlow.costQ sqrCQ mulCQ dvC xl yl ml = cst at hcst ⊢
  generalize hPB : Q.ExpSlow.perBQ sqrCQ mulCQ dvC xl ml = P
  have hce : cst = makeCost xl + P * (64 * yl) := by rw [← hC, ← hPB, Q.ExpSlow.costQ_eq]
  generalize hr0 : stkR H s.mem st = r0 at hcst
  have hmb : makeCost xl ≤ b := by omega
  refine segE hmk hP hxl0 hmb hpc h0 h1 h7 h6 h8 h9 fun S1 L1 b1 pZ cZ hk1 hc1 hb1 => ?_
  refine segM hmv hmz hP hxl0 hk1 fun S2 hk2 hc2 => ?_
  refine segV hP hk2 fun S3 v w hc3 hk3 hm3 => ?_
  have hw63 := hk3.w63
  have e3 : stkR H S3.mem st = r0 := by rw [← hr0]; exact stkR_congr (hc3.trans (hc2.trans hc1))
  have hB0 : b - (cst + stkR H s.mem st) ≤ b - (cst + r0) := Nat.le_of_eq (by rw [hr0])
  refine loopU hap hns hnf hsq hml hdv hW1 (Nat.le_trans (by decide) hW2) hW1K hW2K hW3K hP hX hxl0 hM hH
    (w := w) (t := yl - 1) (n := 64 * (yl - 1)) (B0 := b - (cst + r0)) (F := F) ?_ w S3 L1 b1 0 v pZ xl cZ _
    0 0 0 0 0 0 0 0 0 hk3 (by omega) ?_ (by rw [hm3, hF])
  · intro S4 L4 b4 v4 z4 zl4 zc4 Zv4 zz4 zzl4 zzc4 r4 rl4 rc4 q4 ql4 qc4 hk4 hb4 hv4
    exact afterU hap hns hnf hsq hW1K hW1 hml hW2K hW2 hdv hW3K hP hX hxl0 hM hH hB0 hk4 hb4 hv4
  · show b - (cst + r0) + perBQ sqrCQ mulCQ dvC xl ml * (w + 64 * (yl - 1)) + stkR H S3.mem st ≤ b1
    rw [show perBQ sqrCQ mulCQ dvC xl ml = P from hPB, e3]
    exact Q.ExpSlow.ent_bud hcst hce hb1 hw63 hyl0

end

end FvModexp.Amd64.ExpSlow
