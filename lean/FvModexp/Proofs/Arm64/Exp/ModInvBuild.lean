import FvModexp.Proofs.Arm64.Exp.ModInvAfter

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the callee preconditions inside a round (agent infra)

From the entry `Pre` and the round facts `Mid` at memory `M`, at a callee state `S'` (`SP' = SP - 240`, `X28` the
entry's, memory `M`): the preconditions of `zz.sqr(stk, z)`, `zz.mul(stk, zz, x[:k])`, `zz.trunc(zz, e)`,
`z.lsh(z, 1)`, `z.subMod2N(z, zz, e)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

theorem sp_K (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) : 240 + kc ≤ s.sp.toNat := by
  have := hpre.1.2.1.2.1; simp only [K] at this; omega

theorem stLen_M {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) :
    stLen M st = stLen s.mem st := hrt.2.2.2.2.2.2.1

set_option maxRecDepth 20000 in
theorem sqrPre_at (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) (hl : l ≤ NW n + 1) {cst : Nat} (hb : cst ≤ b1) :
    SqrPre R b1 cst L1 stk above q ql qc st p l S' := by
  have hK := sp_K hpre
  have hsp' := sp'_eq hsp
  have hn := hpre.2.2.2.2.1
  have hsl := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hrt, hz, hzz, hap, hlc, hqlc, hnc, hqc⟩ := hmid
  have hlen := stLen_M hrt
  refine ⟨cenv_at hpre hrt hsp h28 hm hstk habove, hpre.2.1, by rw [hm]; exact globals_at hpre hrt hsp' hstk habove, hqlc,
    wrOut_own hzz hK hsp' h28 hm hstk habove, rdIn_own hz (by omega) hlc hK hsp' hm hstk habove,
    by simp only [NW] at hl; omega, Or.inr fun _ _ => by unfold Apart at hap ⊢; omega,
    stkIn_at hpre hrt hsp' h28 hm hstk habove, by rw [hm, hlen]; simp only [NW] at hl hsl ⊢; omega,
    by rw [hm]; exact hzz.2.2.2.2.2.2.2.1, by rw [hm]; exact stkApart_sub hz.2.2.2.2.2.2.2.1 (by omega), hb,
    by rw [h28, hm]; exact hrt.2.2.2.2.1⟩

set_option maxRecDepth 20000 in
theorem mulPre_at (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {k : Nat} (hk : k ≤ xl) (hqk : ql + k ≤ 2 * NW n + 2)
    {cst : Nat} (hb : cst ≤ b1) :
    MulPre R b1 cst L1 stk above q ql qc st q ql xp k S' := by
  have hK := sp_K hpre
  have hsp' := sp'_eq hsp
  have hn := hpre.2.2.2.2.1
  have hxl := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxh := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  have hsl := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsx := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hrt, -, hzz, -, -, hqlc, -, hqc⟩ := hmid
  have hlen := stLen_M hrt
  refine ⟨cenv_at hpre hrt hsp h28 hm hstk habove, hpre.2.1, by rw [hm]; exact globals_at hpre hrt hsp' hstk habove, hqlc,
    wrOut_own hzz hK hsp' h28 hm hstk habove, rdIn_own hzz hqc hqlc hK hsp' hm hstk habove,
    rdIn_x hpre hrt hk hsp' hm hstk habove, by simp only [NW] at hqk; omega, by omega, Or.inl rfl,
    Or.inr fun _ _ => ?_, stkIn_at hpre hrt hsp' h28 hm hstk habove,
    by rw [hm, hlen]; simp only [NW] at hqk hsl ⊢; omega,
    by rw [hm]; exact hzz.2.2.2.2.2.2.2.1, by rw [hm]; exact stkApart_sub hzz.2.2.2.2.2.2.2.1 (by omega),
    by rw [hm]; exact stkApart_sub (stkApart_rt hrt hsx hxh) (by omega), hb,
    by rw [h28, hm]; exact hrt.2.2.2.2.1⟩
  have := hzz.2.2.2.2.2.2.1
  unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
theorem truncPre_at (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) (hql : ql ≤ 2 ^ 16) {e : Nat} (he : e ≤ 2 ^ 20)
    (hb : makeCost (truncNeed ql e) ≤ b1) :
    TruncPre R b1 L1 stk above q ql qc q ql e S' := by
  have hK := sp_K hpre
  have hsp' := sp'_eq hsp
  obtain ⟨-, hrt, -, hzz, -, -, hqlc, -, hqc⟩ := hmid
  exact ⟨cenv_at hpre hrt hsp h28 hm hstk habove, hpre.2.1, hqlc, wrOut_own hzz hK hsp' h28 hm hstk habove,
    rdIn_own hzz hqc hqlc hK hsp' hm hstk habove, hql, he, Or.inl rfl, hb, by rw [h28, hm]; exact hrt.2.2.2.2.1⟩

set_option maxRecDepth 20000 in
theorem lshPre_at (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) (hl : l ≤ 2 ^ 12)
    (hb : makeCost (l + 1 / 64 + 1) ≤ b1) :
    LshPreA R b1 L1 stk above p l c p l 1 S' := by
  have hK := sp_K hpre
  have hsp' := sp'_eq hsp
  obtain ⟨-, hrt, hz, -, -, hlc, -, hnc, -⟩ := hmid
  exact ⟨cenv_at hpre hrt hsp h28 hm hstk habove, hpre.2.1, hlc, wrOut_own hz hK hsp' h28 hm hstk habove,
    rdIn_own hz (by omega) hlc hK hsp' hm hstk habove, by omega, Or.inl rfl, hb,
    by rw [h28, hm]; exact hrt.2.2.2.2.1⟩

end

end FvModexp.Arm64.ModInv
