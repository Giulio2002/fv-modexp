import FvModexp.Proofs.Arm64.Exp.SlowU1
import FvModexp.Proofs.Arm64.Exp.SlowU2
import FvModexp.Proofs.Arm64.Exp.SlowU3
import FvModexp.Proofs.Arm64.Exp.SlowMod
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the upper loop (`for j := 0; j < w; j++`) by induction on `w - j` (agent expmc)

`loopU`: from `KT1` at `j` with the model invariant `outerLoop 1 (stepM X M) Y 64 t v (w - j) Zv = F` and the budget
`B0 + P · (w - j + n) ≤ b1` (`P` = the per-body bound `perB`), every path reaches the continuation `KX` at `T1` with
`j = w` (`KT1`, invariant at count 0, budget `B0 + P · n`). One body = U1 (`sqr`) → U2 (`mul` if bit 63) → U3
(`div`, back-edge), one model step (`step_val`, `outer_succ1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpEven (MulHypG)

/-- the per-body budget bound (box maxima over the lengths the loop can see) -/
@[reducible] def perB (sqC : Nat → Nat → Nat) (mlC dvC : Nat → Nat → Nat → Nat) (ℓ xl ml : Nat) : Nat :=
  Exp.supN (sqC ℓ) (max xl ml) + Exp.supN (fun n => mlC ℓ n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC ℓ n ml) (3 * max xl ml)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem loopU {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS aS kM aM kD aD : Nat} {sqC : Nat → Nat → Nat} {mlC dvC : Nat → Nat → Nat → Nat}
    (hsq : SqrHypG impl R ns kS aS sqC) (hmu : MulHypG impl R ns kM aM mlC) (hdv : DivHypLG impl R ns kD aD dvC)
    (hkS : kS ≤ K) (haS : aS ≤ 120) (hkM : kM ≤ K) (haM : aM ≤ 120) (hkD : kD ≤ K) (haD : aD ≤ 120)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : SlowX R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    {ret0 : BitVec 64} {Q : State → Prop} {w t n B0 F : Nat}
    (KX : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat),
      KT1 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 w w v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc →
      B0 + perB sqC mlC dvC (stLen s.mem st) xl ml * n ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 t v.toNat 0 Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q) :
    ∀ (c : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 j : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat),
      KT1 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 j w v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc → w = j + c →
      B0 + perB sqC mlC dvC (stLen s.mem st) xl ml * (c + n) ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 t v.toNat c Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro c
  induction c with
  | zero =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk hw hb hv
    have e : j = w := by omega
    subst e
    exact KX S L1 b1 v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk (by simpa using hb) hv
  | succ c ih =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk hw hb hv
    have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hz := hk.zl128
    obtain ⟨P, hPd⟩ : ∃ P, P = perB sqC mlC dvC (stLen s.mem st) xl ml := ⟨_, rfl⟩
    rw [← hPd] at hb
    have hsq1 := Exp.le_supN (sqC (stLen s.mem st)) (max xl ml) zl hz
    have hb1 : B0 + P * (c + n) + P ≤ b1 := by
      rw [show c + 1 + n = (c + n) + 1 by omega, Nat.mul_succ] at hb; omega
    have hPs : Exp.supN (sqC (stLen s.mem st)) (max xl ml) + Exp.supN (fun n => mlC (stLen s.mem st) n xl) (2 * max xl ml) +
        Exp.supN (fun n => dvC (stLen s.mem st) n ml) (3 * max xl ml) = P := hPd.symm
    refine segU1 hap hns hnf hsq hkS haS hP hk (by omega) (by omega) fun S1 L2 b2 p1 l1 c1 hk1 hb2 => ?_
    have hz1 := hk1.zl256
    have hml1 := Exp.le_supN (fun n => mlC (stLen s.mem st) n xl) (2 * max xl ml) l1 hz1
    refine segU2 hap hns hnf hmu hkM haM hP hX hxl0 hk1 (by omega)
      fun S2 L3 b3 p2 l2 c2 zz2 zzl2 zzc2 hk2 hb3 => ?_
    have hz2 := hk2.zl384
    have hdv1 := Exp.le_supN (fun n => dvC (stLen s.mem st) n ml) (3 * max xl ml) l2 hz2
    have hb3' : b1 - sqC (stLen s.mem st) zl - mlC (stLen s.mem st) l1 xl ≤ b3 := by
      split at hb3 <;> omega
    refine segU3 hap hns hnf hdv hkD haD hP hM hk2 (by omega)
      fun S3 L4 b4 pq lq cq pr lr cr hk3 hb4 => ?_
    refine ih S3 L4 b4 (j + 1) (v + v) pr lr cr _ _ _ _ _ _ _ _ _ _ hk3 (by omega) ?_ ?_
    · rw [← hPd]; omega
    · rw [← hv, outer_succ1, dbl, ← step_val _ _ _ hM v]

end

end FvModexp.Arm64.ExpSlow
