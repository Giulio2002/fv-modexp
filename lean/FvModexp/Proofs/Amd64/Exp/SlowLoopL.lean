import FvModexp.Proofs.Amd64.Exp.SlowL1
import FvModexp.Proofs.Amd64.Exp.SlowL2
import FvModexp.Proofs.Amd64.Exp.SlowL3
import FvModexp.Proofs.Amd64.Exp.SlowLoopLR
import FvModexp.Proofs.Amd64.Exp.SlowFin
import FvModexp.Proofs.Amd64.Exp.SlowMod
import FvModexp.Proofs.Amd64.Exp.SlowPerB

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the lower loop (agent asm s75; twin of arm64 `SlowLoopLQ` + `SlowFunQ.lowerQ`)

* `segJ2`: the back-edge `KJ2` → `KT2` with `j + 1`, `v + v` (`runJ2`; the spills of `zz`, `q`).
* `loopL`: from `KT2` at bit `j` (word `i`) with the model invariant `outerLoop 1 (stepM X M) Y 64 i v (64 - j) Zv = F`
  and the budget `B0 + perBQ · (64 - j + n) + stkR ≤ b1`, every path reaches `KX` at `j = 64` (invariant at count 0,
  budget `B0 + perBQ · n`). One body = L1 (`sqr`) → L2 (`mul` if bit 63) → L3 (`div`) → J2.
* `lower`: from `KT2` at `j = 0` for word `i` (strong induction on `i`; `exitL` → next word or `KE` → `segFin`) to
  `RET` with `FQS … F cst s`.
* `afterU`: the upper loop's exit state (`KT1`, `j = w`, count 0) → `RET` (`exitUC` + `lower` / `segFin`) — expmc's
  `loopU` continuation `KX` is exactly this.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.Q.ExpSlow

/-- the final budget step (small context) -/
theorem finBudL {b c r r1 r2 B0 X b1 : Nat} (hB0 : b - (c + r) ≤ B0) (hb : B0 + X + r1 ≤ b1) (e : r2 = r1) :
    b - (c + r) + r2 ≤ b1 := by
  subst e; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the back-edge** `j2` → `t2` -/
theorem segJ2 {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 i j : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KJ2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i j v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (KT : ∀ S' : State, KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 i (j + 1) (v + v)
        z zl zc' Zv zz zzl zzc rr rl rc q ql qc → stCap S'.mem st = stCap S.mem st →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hk.jc.wc.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  obtain ⟨bzz, bzzc⟩ := hk.bb.bzz.lt64
  obtain ⟨bq, -⟩ := hk.bb.bq.lt64
  have hzzl := hk.bb.lzz
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  obtain ⟨-, -, -, -, -, -, -, -, -, e200, e208, e210, -⟩ := hk.jc.esl
  refine runJ2 ret0 Q sp j i xp xl st S.mem hacc (by omega) hK5 hk.jw hk.sb0 hk.sc0 e208 e210 e200 S hk.pc
    hk.jc.esp rfl ?_
  intro T t1 t4 tF trg wb0 w168 w70 w78 w150 r0 r10 r8 r1 r2 r13 r15 r9 r11 r3 r6 r7 t14 tfs tx tdf
  obtain ⟨hw, hdl, hln⟩ := WC.own hP hk.jc.wc tF trg (by
    intro x hx; simp only [wsJ2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have hFo : ∀ a k, (a + k ≤ sp + 0x70 ∨ sp + 0x170 ≤ a ∨ (sp + 0xb8 ≤ a ∧ a + k ≤ sp + 0x150) ∨
      (sp + 0x80 ≤ a ∧ a + k ≤ sp + 0xb0) ∨ (sp + 0x158 ≤ a ∧ a + k ≤ sp + 0x168)) → Outside a k (wsJ2 sp) := by
    intro a k ha; simp only [wsJ2, outside_cons, outside_nil, and_true]; omega
  have kF : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → T.mem.readLE a k = S.mem.readLE a k :=
    fun a k h1 _ => tF.readLE a k (hFo a k (Or.inr (Or.inl (by omega))))
  have tn : ∀ {x : BitVec 64} {n : Nat}, x = BitVec.ofNat 64 n → n < 2 ^ 64 → x.toNat = n := by
    intro x n h hn; rw [h, BitVec.toNat_ofNat]; omega
  refine KT T ⟨hk.jc.call (t4.trans hk.jc.esp.symm) t14 tfs tx tdf hw kF, hk.bb.own hdl hln, hk.iy,
    (tF.readLE _ _ (hFo _ _ (by omega))).trans hk.sc0, wb0, t1, hk.zlb, by have := hk.jw; omega,
    r0.trans hk.e0, r10.trans hk.e3, r8.trans hk.e1, w150.trans (tn hk.e8 bzz), w70.trans (tn hk.e6 (by omega)),
    w78.trans (tn hk.e7 bzzc), (tF.readLE _ _ (hFo _ _ (by omega))).trans hk.s160, r1.trans hk.e12,
    r2.trans hk.e13, w168.trans (tn hk.e15 bq), r13.trans hk.e9, r15.trans hk.e11, by rw [r9, hk.e2], r11, r3, r6,
    r7⟩ (tF.readLE _ _ (by simp only [wsJ2, outside_cons, outside_nil, and_true]; omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the lower loop's bit loop** (word `i`, bits `j … 63`) by induction on `64 - j` -/
theorem loopL {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W1 W2 W3 H : Nat} {dvC : Nat → Nat → Nat}
    (hsq : SqrE0 impl R ns W1) (hW1K : W1 ≤ K) (hW1 : 7104 ≤ W1)
    (hml : Q.DivRec.MulHypQE impl R ns W2) (hW2K : W2 ≤ K) (hW2 : mulWX64 ≤ W2)
    (hdv : DivHypLGQ impl R ns W3 0x70 dvC) (hW3K : W3 ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H)
    {ret0 : W64} {Q : State → Prop} {i n B0 F : Nat}
    (KX : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat),
      KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i 64 v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc →
      B0 + perBQ sqrCQ mulCQ dvC xl ml * n + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 i v.toNat 0 Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q) :
    ∀ (c : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 j : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat),
      KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i j v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc → 64 = j + c →
      B0 + perBQ sqrCQ mulCQ dvC xl ml * (c + n) + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 i v.toNat c Zv = F →
      ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro c
  induction c with
  | zero =>
    intro S L1 b1 j v z zl zc' Zv zz zzl zzc rr rl rc q ql qc hk hw hb hv
    have e : j = 64 := by omega
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
    refine segL1 hap hns hnf hsq hW1K hW1 hP hk (by omega) hH (by omega) fun S1 L2 b2 p1 l1 c1 hk1 hb2 => ?_
    have hz1 := hk1.zlb
    have hml1 := Exp.le_supN (fun n => mulCQ n xl) (2 * max xl ml) l1 hz1
    refine segL2 hap hns hnf hml hW2K hW2 hP hX hxl0 hk1 hH (by omega)
      fun S2 L3 b3 p2 l2 c2 zz2 zzl2 zzc2 hk2 hb3 => ?_
    have hz2 := hk2.zlb
    have hdv1 := Exp.le_supN (fun n => dvC n ml) (3 * max xl ml) l2 hz2
    have hb3' : B0 + P * (c + n) + Exp.supN (fun n => dvC n ml) (3 * max xl ml) + stkR H S2.mem st ≤ b3 := by
      split at hb3 <;> omega
    refine segL3 hap hns hnf hdv hW3K hP hM hk2 hH (by omega)
      fun S3 L4 b4 pq lq cq pr lr cr hk3 hb4 => ?_
    refine segJ2 hP hk3 fun S4 hk4 hc4 => ?_
    refine ih S4 L4 b4 (j + 1) (v + v) pr lr cr _ _ _ _ _ _ _ _ _ _ hk4 (by omega) ?_ ?_
    · rw [stkR_congr hc4, ← hPd]; omega
    · rw [← hv, outer_succ1, dbl, ← step_val _ _ _ hM v]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the lower loop** (word index `i`, from `j = 0`) to `RET` -/
theorem lower {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W1 W2 W3 H : Nat} {dvC : Nat → Nat → Nat}
    (hsq : SqrE0 impl R ns W1) (hW1K : W1 ≤ K) (hW1 : 7104 ≤ W1)
    (hml : Q.DivRec.MulHypQE impl R ns W2) (hW2K : W2 ≤ K) (hW2 : mulWX64 ≤ W2)
    (hdv : DivHypLGQ impl R ns W3 0x70 dvC) (hW3K : W3 ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H)
    {B0 cst F : Nat} (hB0 : b - (cst + stkR H s.mem st) ≤ B0) :
    ∀ (i : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat),
      KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i 0 v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc →
      B0 + perBQ sqrCQ mulCQ dvC xl ml * (64 * (i + 1)) + stkR H S.mem st ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 i v.toNat 64 Zv = F →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQS R b H L K zp zc st F cst s) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro S L1 b1 v z zl zc' Zv zz zzl zzc rr rl rc q ql qc hk hb hv
  refine loopL hap hns hnf hsq hW1K hW1 hml hW2K hW2 hdv hW3K hP hX hxl0 hM hH (i := i) (n := 64 * i)
    (B0 := B0) (F := F) ?_ 64 S L1 b1 0 v z zl zc' Zv zz zzl zzc rr rl rc q ql qc hk (by omega)
    (by rw [show 64 + 64 * i = 64 * (i + 1) by omega]; exact hb) hv
  intro S1 L2 b2 v1 z1 zl1 zc1 Zv1 zz1 zzl1 zzc1 rr1 rl1 rc1 q1 ql1 qc1 hk1 hb1 hv1
  refine exitL hP hk1 (fun S2 hi hke hc2 => ?_) (fun S2 i' v2 hi hv2 hk2 hc2 => ?_)
  · subst hi
    exact segFin hP hke (by rw [← hv1]; rfl) (finBudL hB0 hb1 (stkR_congr hc2))
  · subst hi
    refine ih i' (by omega) S2 L2 b2 v2 z1 zl1 zc1 Zv1 zz1 zzl1 zzc1 rr1 rl1 rc1 q1 ql1 qc1 hk2
      (by rw [stkR_congr hc2]; exact hb1) ?_
    rw [← hv1, hv2]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **after the upper loop**: `KT1` with `j = w` (expmc's `loopU` exit state, its invariant at count 0) → `RET`
with `FQS … F cst s` (`exitUC`; `len y = 1` → `segFin`, else `lower` for word `len y - 2`) -/
theorem afterU {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W1 W2 W3 H : Nat} {dvC : Nat → Nat → Nat}
    (hsq : SqrE0 impl R ns W1) (hW1K : W1 ≤ K) (hW1 : 7104 ≤ W1)
    (hml : Q.DivRec.MulHypQE impl R ns W2) (hW2K : W2 ≤ K) (hW2 : mulWX64 ≤ W2)
    (hdv : DivHypLGQ impl R ns W3 0x70 dvC) (hW3K : W3 ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H)
    {B0 cst F : Nat} (hB0 : b - (cst + stkR H s.mem st) ≤ B0)
    {S : State} {L1 : List (Nat × Nat)} {b1 w : Nat} {v : BitVec 64} {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 w w v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hb : B0 + perBQ sqrCQ mulCQ dvC xl ml * (64 * (yl - 1)) + stkR H S.mem st ≤ b1)
    (hv : Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 (yl - 1)
      v.toNat 0 Zv = F) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQS R b H L K zp zc st F cst s) := by
  refine exitUC hP hk (fun S5 hi hke hc5 => ?_) (fun S5 i v5 hi hv5 hk5 hc5 => ?_)
  · rw [hi] at hv
    exact segFin hP hke (by rw [← hv]; rfl) (finBudL hB0 hb (stkR_congr hc5))
  · refine lower hap hns hnf hsq hW1K hW1 hml hW2K hW2 hdv hW3K hP hX hxl0 hM hH hB0 i S5 L1 b1 v5 z zl zc' Zv zz
      zzl zzc rr rl rc q ql qc hk5 ?_ ?_
    · rw [← hi, stkR_congr hc5]; exact hb
    · rw [hi] at hv; rw [← hv, hv5]; rfl

end

end FvModexp.Amd64.ExpSlow
