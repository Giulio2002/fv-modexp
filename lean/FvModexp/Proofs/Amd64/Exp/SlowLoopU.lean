import FvModexp.Proofs.Amd64.Exp.SlowU1
import FvModexp.Proofs.Amd64.Exp.SlowU2
import FvModexp.Proofs.Amd64.Exp.SlowUJ
import FvModexp.Proofs.Amd64.Exp.SlowQStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the upper loop `for j := 0; j < w; j++` (nat.go:749-764) by induction on `w - j`
(agent expmc s81; twin of arm64 `Q.ExpSlow.loopUQ`)

One body = U1 (`sqr`) + U2 (optional `mul`) + U3 (`div`) + the join; budget `perBQ` per body (the box maxima of
the level-free callee costs); model `Exp.outerLoop 1 (stepM X M) Y 64 t v c Zv` (`outer_succ1`, `dbl`, `step_val`).
The exit `KX` is `KT1` at `j = w` (asm's lower loop starts there).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the per-body budget bound -/
@[reducible] def perBQ (sqC : Nat → Nat) (mlC dvC : Nat → Nat → Nat) (xl ml : Nat) : Nat :=
  Exp.supN sqC (max xl ml) + Exp.supN (fun n => mlC n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC n ml) (3 * max xl ml)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem loopU {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W1 W2 W3 : Nat} {dvC : Nat → Nat → Nat} {H : Nat}
    (hsq : SqrE0 impl R ns W1) (hml : Q.DivRec.MulHypQE impl R ns W2) (hdv : DivHypLGQ impl R ns W3 0x70 dvC)
    (hW1 : 7104 ≤ W1) (hW2 : 21072 ≤ W2) (hK1 : W1 ≤ K) (hK2 : W2 ≤ K) (hK3 : W3 ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H)
    {ret0 : W64} {Q : State → Prop} {w t n B0 F : Nat}
    (KX : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat),
      KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 w w v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc →
      B0 + perBQ sqrCQ mulCQ dvC xl ml * n + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 t v.toNat 0 Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q) :
    ∀ (c : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 j : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat),
      KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 j w v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc → w = j + c →
      B0 + perBQ sqrCQ mulCQ dvC xl ml * (c + n) + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 t v.toNat c Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro c
  induction c with
  | zero =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc rr rl rc q ql qc hk hw hb hv
    have e : j = w := by omega
    subst e
    exact KX S L1 b1 v z zl zc' Zv zz zzl zzc rr rl rc q ql qc hk (by simpa using hb) hv
  | succ c ih =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc rr rl rc q ql qc hk hw hb hv
    have hz := hk.zlb
    obtain ⟨P, hPd⟩ : ∃ P, P = perBQ sqrCQ mulCQ dvC xl ml := ⟨_, rfl⟩
    rw [← hPd] at hb
    have hsq1 := Exp.le_supN sqrCQ (max xl ml) zl hz
    have hb1 : B0 + P * (c + n) + P + stkR H S.mem st ≤ b1 := by
      rw [show c + 1 + n = (c + n) + 1 by omega, Nat.mul_succ] at hb; omega
    have hPs : Exp.supN sqrCQ (max xl ml) + Exp.supN (fun n => mulCQ n xl) (2 * max xl ml) +
        Exp.supN (fun n => dvC n ml) (3 * max xl ml) = P := hPd.symm
    refine segU1 hap hns hnf hsq hK1 hW1 hP hk (by omega) hH (by omega) fun S1 L2 b2 p1 l1 c1 hk1 hb2 => ?_
    have hz1 := hk1.zlb
    have hml1 := Exp.le_supN (fun n => mulCQ n xl) (2 * max xl ml) l1 hz1
    refine segU2 hap hns hnf hml hK2 hW2 hP hX hxl0 hk1 hH (by omega)
      fun S2 L3 b3 p2 l2 c2 zz2 zzl2 zzc2 hk2 hb3 => ?_
    have hz2 := hk2.zlb
    have hdv1 := Exp.le_supN (fun n => dvC n ml) (3 * max xl ml) l2 hz2
    have hb3' : B0 + P * (c + n) + Exp.supN (fun n => dvC n ml) (3 * max xl ml) + stkR H S2.mem st ≤ b3 := by
      split at hb3 <;> omega
    refine segU3 hap hns hnf hdv hK3 hP hM hk2 hH (by omega)
      fun S3 L4 b4 pq lq cq pr lr cr hk3 hb4 => ?_
    refine segUJ hP hk3 fun S4 hk4 hcap => ?_
    refine ih S4 L4 b4 (j + 1) (v + v) pr lr cr _ _ _ _ _ _ _ _ _ _ hk4 (by omega) ?_ ?_
    · rw [stkR_congr hcap, ← hPd]; omega
    · rw [← hv, outer_succ1, dbl, ← step_val _ _ _ hM v]

end

end FvModexp.Amd64.ExpSlow
