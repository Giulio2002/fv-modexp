import FvModexp.Proofs.Arm64.ExpQ.SlowL1Q
import FvModexp.Proofs.Arm64.ExpQ.SlowL2Q
import FvModexp.Proofs.Arm64.ExpQ.SlowL3Q
import FvModexp.Proofs.Arm64.ExpQ.SlowLoopUQ
import FvModexp.Proofs.Arm64.Exp.SlowLoopL

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowLoopL.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): the lower loop (`for j := 0; j < _W; j++`, word `i` = `w`) by induction on `64 - j` (agent expmc)

`loopL`: from `KT2` at `j` with the model invariant `outerLoop 1 (stepM X M) Y 64 t v (w - j) Zv = F` and the budget
`B0 + P · (w - j + n) ≤ b1` (`P` = the per-body bound `perB`), every path reaches the continuation `KX` at `T1` with
`j = w` (`KT2`, invariant at count 0, budget `B0 + P · n`). One body = U1 (`sqr`) → U2 (`mul` if bit 63) → U3
(`div`, back-edge), one model step (`step_val`, `outer_succ1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem loopLQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS aS kM aM kD aD : Nat} {sqC : Nat → Nat} {mlC dvC : Nat → Nat → Nat} {H : Nat}
    (hsq : SqrHypGQ impl R ns kS aS sqC) (hmu : MulHypGQ impl R ns kM aM mlC) (hdv : DivHypLGQ impl R ns kD aD dvC)
    (hkS : kS ≤ K) (haS : aS ≤ 120) (hkM : kM ≤ K) (haM : aM ≤ 120) (hkD : kD ≤ K) (haD : aD ≤ 120)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : SlowX R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H)
    {ret0 : BitVec 64} {Q : State → Prop} {w t n B0 F : Nat}
    (KX : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat),
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 64 w v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc →
      B0 + perBQ sqC mlC dvC xl ml * n + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 t v.toNat 0 Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q) :
    ∀ (c : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 j : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat),
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 j w v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc → 64 = j + c →
      B0 + perBQ sqC mlC dvC xl ml * (c + n) + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 t v.toNat c Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro c
  induction c with
  | zero =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk hw hb hv
    have e : j = 64 := by omega
    subst e
    exact KX S L1 b1 v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk (by simpa using hb) hv
  | succ c ih =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk hw hb hv
    have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hz := hk.zl128
    obtain ⟨P, hPd⟩ : ∃ P, P = perBQ sqC mlC dvC xl ml := ⟨_, rfl⟩
    rw [← hPd] at hb
    have hsq1 := Exp.le_supN sqC (max xl ml) zl hz
    have hb1 : B0 + P * (c + n) + P + stkR H S.mem st ≤ b1 := by
      rw [show c + 1 + n = (c + n) + 1 by omega, Nat.mul_succ] at hb; omega
    have hPs : Exp.supN sqC (max xl ml) + Exp.supN (fun n => mlC n xl) (2 * max xl ml) +
        Exp.supN (fun n => dvC n ml) (3 * max xl ml) = P := hPd.symm
    refine segL1Q hap hns hnf hsq hkS haS hP hk (by omega) hH (by omega) fun S1 L2 b2 p1 l1 c1 hk1 hb2 => ?_
    have hz1 := hk1.zl256
    have hml1 := Exp.le_supN (fun n => mlC n xl) (2 * max xl ml) l1 hz1
    refine segL2Q hap hns hnf hmu hkM haM hP hX hxl0 hk1 hH (by omega)
      fun S2 L3 b3 p2 l2 c2 zz2 zzl2 zzc2 hk2 hb3 => ?_
    have hz2 := hk2.zl384
    have hdv1 := Exp.le_supN (fun n => dvC n ml) (3 * max xl ml) l2 hz2
    have hb3' : B0 + P * (c + n) + Exp.supN (fun n => dvC n ml) (3 * max xl ml) + stkR H S2.mem st ≤ b3 := by
      split at hb3 <;> omega
    refine segL3Q hap hns hnf hdv hkD haD hP hM hk2 hH (by omega)
      fun S3 L4 b4 pq lq cq pr lr cr hk3 hb4 => ?_
    refine ih S3 L4 b4 (j + 1) (v + v) pr lr cr _ _ _ _ _ _ _ _ _ _ hk3 (by omega) ?_ ?_
    · rw [← hPd]; omega
    · rw [← hv, outer_succ1, dbl, ← step_val _ _ _ hM v]

end

end FvModexp.Arm64.Q.ExpSlow
