import FvModexp.Proofs.Arm64.Exp.SlowPE
import FvModexp.Proofs.Arm64.Exp.SlowPM
import FvModexp.Proofs.Arm64.Exp.SlowLoopU
import FvModexp.Proofs.Arm64.Exp.SlowLoopL
import FvModexp.Proofs.Arm64.Exp.SlowXU
import FvModexp.Proofs.Arm64.Exp.SlowFin

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the whole function from the entry facts (agent expmc)

`lower`: the lower loop by strong induction on the word index (`loopL` → `exitL` → `KE` or the next word);
`body`: `segE` → `segM` → `segV` → `loopU` → `exitU` → (`KE` | `lower`) → `segFin`, every path reaching `RET` with
`FQ` and the value `Exp.expNNSlow x y m`. Budget: `B0 = b - cost`, `cost = makeCost (len x) + 64 · len y · perB`; the
upper loop runs `w ≤ 63` bodies, each lower word 64.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpEven (MulHypG)

theorem cost_eq (sqC : Nat → Nat → Nat) (mlC dvC : Nat → Nat → Nat → Nat) (ℓ xl yl ml : Nat) :
    cost sqC mlC dvC ℓ xl yl ml = makeCost xl + perB sqC mlC dvC ℓ xl ml * (64 * yl) := by
  unfold cost perB; rw [Nat.mul_comm (64 * yl)]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the lower loop** (word index `i`, from `j = 0`) -/
theorem lower {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS aS kM aM kD aD : Nat} {sqC : Nat → Nat → Nat} {mlC dvC : Nat → Nat → Nat → Nat}
    (hsq : SqrHypG impl R ns kS aS sqC) (hmu : MulHypG impl R ns kM aM mlC) (hdv : DivHypLG impl R ns kD aD dvC)
    (hkS : kS ≤ K) (haS : aS ≤ 120) (hkM : kM ≤ K) (haM : aM ≤ 120) (hkD : kD ≤ K) (haD : aD ≤ 120)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : SlowX R L xp xl xc) (hxl0 : 0 < xl) (hM : 0 < natVal s.mem mp ml)
    (h18 : s.regs 18 = r18) (h29 : s.regs 29 = BitVec.ofNat 64 r29) (hr4 : ret % 4 = 0) (hr48 : ret < 2 ^ 48)
    {B0 cst F : Nat} (hB0 : b - cst ≤ B0) :
    ∀ (i : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (v : BitVec 64)
      (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat),
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 0 i v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc →
      B0 + perB sqC mlC dvC (stLen s.mem st) xl ml * (64 * (i + 1)) ≤ b1 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 i v.toNat 64 Zv = F →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S (FQ R b L K zp zc st F cst s) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro S L1 b1 v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk hb hv
  refine loopL hap hns hnf hsq hmu hdv hkS haS hkM haM hkD haD hP hX hxl0 hM (w := i) (t := i) (n := 64 * i)
    (B0 := B0) (F := F) ?_ 64 S L1 b1 0 v z zl zc' Zv zz zzl zzc r rl rc q ql qc hk (by omega)
    (by rw [show 64 + 64 * i = 64 * (i + 1) by omega]; exact hb) hv
  intro S1 L2 b2 v1 z1 zl1 zc1 Zv1 zz1 zzl1 zzc1 r1 rl1 rc1 q1 ql1 qc1 hk1 hb1 hv1
  refine exitL hP hk1 (fun S2 hi hke => ?_) (fun S2 i' v2 hi hv2 hk2 => ?_)
  · subst hi
    exact segFin hP h18 h29 hr4 hr48 hke (by rw [← hv1]; rfl) (Nat.le_trans hB0 (Nat.le_trans (Nat.le_add_right _ _) hb1))
  · subst hi
    refine ih i' (by omega) S2 L2 b2 v2 z1 zl1 zc1 Zv1 zz1 zzl1 zzc1 r1 rl1 rc1 q1 ql1 qc1 hk2 hb1 ?_
    rw [← hv1, hv2]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNSlow` from the entry facts** (see the module doc) -/
theorem body {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS aS kM aM kD aD : Nat} {sqC : Nat → Nat → Nat} {mlC dvC : Nat → Nat → Nat → Nat}
    (hsq : SqrHypG impl R ns kS aS sqC) (hmu : MulHypG impl R ns kM aM mlC) (hdv : DivHypLG impl R ns kD aD dvC)
    (hkS : kS ≤ K) (haS : aS ≤ 120) (hkM : kM ≤ K) (haM : aM ≤ 120) (hkD : kD ≤ K) (haD : aD ≤ 120)
    (hmk : MakesliceLiveContract (LibW.program.link impl) mkA 4096 R)
    (hmv : MemmoveLive (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : SlowX R L xp xl xc) (hx0 : 0 < natVal s.mem xp xl) (hM : 0 < natVal s.mem mp ml)
    (hcst : cost sqC mlC dvC (stLen s.mem st) xl yl ml ≤ b)
    {zl : Nat} (hzl : zl < 2 ^ 64) (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 yl)
    (h9 : s.regs 9 = BitVec.ofNat 64 yc) (h10 : s.regs 10 = BitVec.ofNat 64 mp)
    (h11 : s.regs 11 = BitVec.ofNat 64 ml) (h12 : s.regs 12 = BitVec.ofNat 64 mc) :
    ReachesRet (LibW.program.link impl) (s.regs 30) s
      (FQ R b L K zp zc st (Exp.expNNSlow (natVal s.mem xp xl) (natVal s.mem yp yl) (natVal s.mem mp ml))
        (cost sqC mlC dvC (stLen s.mem st) xl yl ml) s) := by
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hx0
    · exact h
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have h30 : s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h29 : s.regs 29 = BitVec.ofNat 64 (s.regs 29).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  generalize hF : Exp.expNNSlow (natVal s.mem xp xl) (natVal s.mem yp yl) (natVal s.mem mp ml) = F
  generalize hC : cost sqC mlC dvC (stLen s.mem st) xl yl ml = cst at hcst ⊢
  generalize hPB : perB sqC mlC dvC (stLen s.mem st) xl ml = P
  have hce : cst = makeCost xl + P * (64 * yl) := by rw [← hC, ← hPB, cost_eq]
  rw [h30]
  have hmb : makeCost xl ≤ b := by omega
  refine segE hmk hP hzl hr48 hxl0 hmb hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h30 fun S1 L1 b1 z zc' hk1 hb1 => ?_
  refine segM hmv hP hxl0 hk1 fun S2 hk2 => ?_
  refine segV hP hk2 fun S3 v w hk3 hm3 => ?_
  have hw63 := hk3.w63
  have hPw : P * (w + 64 * (yl - 1)) + P * (64 - w) = P * (64 * yl) := by
    rw [← Nat.mul_add, show w + 64 * (yl - 1) + (64 - w) = 64 * yl by omega]
  refine loopU hap hns hnf hsq hmu hdv hkS haS hkM haM hkD haD hP hX hxl0 hM (w := w) (t := yl - 1)
    (n := 64 * (yl - 1)) (B0 := b - cst) (F := F) ?_ w S3 L1 b1 0 v z xl zc' _ 0 0 0 0 0 0 0 0 0 hk3 (by omega)
    (by
      rw [hPB]
      generalize P * (w + 64 * (yl - 1)) = A at hPw ⊢
      generalize P * (64 - w) = B' at hPw
      generalize P * (64 * yl) = C at hPw hce
      omega) (by rw [hm3, hF])
  intro S4 L4 b4 v4 z4 zl4 zc4 Zv4 zz4 zzl4 zzc4 r4 rl4 rc4 q4 ql4 qc4 hk4 hb4 hv4
  rw [hPB] at hb4
  refine exitU hP hk4 (fun S5 hi hke => ?_) (fun S5 i v5 hi hv5 hk5 => ?_)
  · rw [hi] at hv4
    exact segFin hP rfl h29 hr4 hr48 hke (by rw [← hv4]; rfl) (Nat.le_trans (Nat.le_add_right _ _) hb4)
  · refine lower hap hns hnf hsq hmu hdv hkS haS hkM haM hkD haD hP hX hxl0 hM rfl h29 hr4 hr48 (B0 := b - cst)
      (le_refl _) i S5 L4 b4 v5 z4 zl4 zc4 Zv4 zz4 zzl4 zzc4 r4 rl4 rc4 q4 ql4 qc4 hk5 ?_ ?_
    · rw [hPB, ← hi]; exact hb4
    · rw [hi] at hv4; rw [← hv4, hv5]; rfl

end

end FvModexp.Arm64.ExpSlow
