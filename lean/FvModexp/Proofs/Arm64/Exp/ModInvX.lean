import FvModexp.Proofs.Arm64.Exp.ModInvBuild

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): divmc's extra `sqr` / `mul` facts inside a round (agent infra, s25)

For divmc's export shapes `SqrHypX` / `MulHypX` (Nat/SqrMulX): at a callee state `S'` (`SP' = SP - 240`, memory `M`
with the round facts `RtM`): `stkX_at` (the stack object, `StkX`), `opX_own` / `capIn_own` (an owned array), `opX_x` /
`capIn_x` (the operand `x`), `sqrX_at` / `mulX_at` (the whole extra conjunct). `wa_back` / `wa_new`: the owned-array
field `WA` (apart from the stack's whole array) through a callee.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

theorem px_of (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) : PX R L s zp zc st xp xl xc :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- the entry `z` is held at entry (`WrOut`) -/
theorem z_held (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) : Held R L zp (8 * zc) :=
  (hpre.2.2.2.2.2.2.2.2.1.2.1 hpre.2.2.2.2.2.2.2.1).2.1

/-- a range apart from the stack's whole array at `M` is apart from its free part (also when that part is empty) -/
theorem free_of_arr {M : Memory} {a k : Nat} (hlc : stLen M st ≤ stCap M st)
    (h : Apart a k (stW M st) (8 * stCap M st)) : Apart a k (frP M st) (frN M st) := by
  simp only [frP, frN]; unfold Apart at h ⊢; omega

/-- `OpX` of a range held at entry and apart from the entry free part / `gA` -/
theorem opX_held {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    {a k : Nat} (h : OpX s.mem st a k) (hh : Held R L a k) : OpX M st a k := by
  intro hk
  obtain ⟨h1, h2⟩ := h hk
  obtain ⟨-, -, -, -, -, hok, hlen, hor, -⟩ := hrt
  refine ⟨?_, h2⟩
  rcases hor with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
  · simp only [frP, frN] at h1 ⊢; rw [e0, e2, hlen]; exact h1
  · exact free_of_arr hok.2.2.2.2.2.1 (by have := fresh_apart hIn hAp hh; unfold Apart at this ⊢; omega)

/-- `OpX` of an owned array -/
theorem opX_own (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {p c : Nat} (ho : Own R kc L L1 s zp zc st xp xl M p c) :
    OpX M st p (8 * c) := by
  have hpx := px_of hpre
  have hzh := z_held hpre
  by_cases hz : p = zp ∧ c = zc
  · obtain ⟨rfl, rfl⟩ := hz; exact opX_held hrt hpx.2.2.2.2.2.2.2.1 hzh
  intro hk
  have hc : 0 < c := by omega
  obtain ⟨-, -, -, hor, -, -, -, -, hwa⟩ := ho
  rcases hor with h | ⟨hIn, -⟩
  · exact absurd h hz
  have hgA : Apart p (8 * c) RunIface.gA 32 := fresh_out hIn hpre.2.2.1.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hok, -, -, ain⟩ := hrt
  refine ⟨?_, hgA⟩
  rcases Nat.eq_zero_or_pos (stCap M st) with h0 | h0
  · have hw : stW M st = 0 := by
      refine ArrIn.cap0 ain hpx.2.2.2.2.2.1 h0
    have := hok.2.2.2.2.2.1
    simp only [frP, frN]; unfold Apart; omega
  · exact free_of_arr hok.2.2.2.2.2.1 (hwa hz hc h0)

/-- `CapIn` of an owned array -/
theorem capIn_own {L1 : List (Nat × Nat)} {M : Memory} {p c l : Nat}
    (ho : Own R kc L L1 s zp zc st xp xl M p c) (hc : 0 < c) (hl : l ≤ c) : CapIn R L1 p l c := by
  obtain ⟨h1, -, h3, -⟩ := ho
  obtain ⟨-, hh, -, hb⟩ := h3 hc
  exact ⟨hl, h1, hh, hb⟩

/-- `CapIn` / `OpX` of the operand `x[:k]` -/
theorem capIn_x (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {k : Nat} (hk : k ≤ xl) :
    CapIn R L1 xp k xc ∧ OpX M st xp (8 * k) := by
  have hrt' := hrt
  obtain ⟨-, -, -, hLE, -⟩ := hrt
  obtain ⟨c1, c2, c3, c4⟩ := (px_of hpre).2.2.2.2.2.2.1
  refine ⟨⟨by omega, c2, hLE.held c3, c4⟩, ?_⟩
  have hox := (px_of hpre).2.2.2.2.2.2.2.2
  intro h0
  have hxl : 0 < 8 * xl := by omega
  obtain ⟨o1, o2⟩ := hox hxl
  have hxh : Held R L xp (8 * xl) := c3.sub (Nat.le_refl _) (by omega)
  obtain ⟨o1', -⟩ := opX_held hrt' (a := xp) (k := 8 * xl) (fun _ => ⟨o1, o2⟩) hxh hxl
  unfold Apart at o1' o2 ⊢
  exact ⟨by omega, by omega⟩

theorem outside_00 : ∀ rs : List (Nat × Nat), Outside 0 0 rs
  | [] => trivial
  | (_, _) :: rs => ⟨Or.inl (Nat.zero_le _), outside_00 rs⟩

set_option maxRecDepth 20000 in
/-- divmc's `StkX` at a callee state -/
theorem stkX_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 240) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ kc) (habove : above ≤ 88) : StkX R L1 S' stk above st := by
  obtain ⟨x0, x1, x2, x3, x4, x5, -⟩ := px_of hpre
  have hsi := stkIn_at hpre hrt hsp h28 hm hstk habove
  have hgO : Outside RunIface.gA 32 R.rt := hpre.2.2.1.2.2.2.2.2.2.2.2.1
  have hsh : Held R L st 24 := (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1).2.1
  obtain ⟨-, -, -, -, -, hok, hlen, hor, ain⟩ := hrt
  have hlc := hok.2.2.2.2.2.1
  obtain ⟨-, -, -, hsa⟩ := hsi
  rw [hm, h28] at hsa
  simp only [StkX, hm, h28]
  rcases Nat.eq_zero_or_pos (stCap M st) with h0 | h0
  · have hw : stW M st = 0 := ArrIn.cap0 ain x5 h0
    have e1 : frP M st = 0 := by simp only [frP]; omega
    have e2 : frN M st = 0 := by simp only [frN]; omega
    rw [e1, e2]
    exact ⟨x0, x1, Or.inr (outside_00 _), outside_00 _, Or.inl (by omega), Or.inr (by omega), x2,
      Or.inl (by omega)⟩
  obtain ⟨a1, a2⟩ := hsa h0
  have hsub : ∀ ws : List (Nat × Nat), Outside (stW M st) (8 * stCap M st) ws → Outside (frP M st) (frN M st) ws :=
    fun ws h => h.of_sub (by simp only [frP]; omega) (by simp only [frP, frN]; omega)
  refine ⟨x0, x1, ((hok.2.2.2.2.1 h0).2.1).sub (by simp only [frP]; omega) (by simp only [frP, frN]; omega),
    hsub _ a1, by simp only [frP, frN]; unfold Apart at a2 ⊢; omega, ?_, x2, ?_⟩
  · rcases hor with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
    · simp only [frP, frN] at x3 ⊢; rw [e0, e2, hlen]; exact x3
    · have := fresh_apart hIn hAp hsh
      simp only [frP, frN]; unfold Apart at this ⊢; omega
  · rcases hor with ⟨e0, e2⟩ | ⟨hIn, -⟩
    · simp only [frP, frN] at x4 ⊢; rw [e0, e2, hlen]; exact x4
    · have := fresh_out hIn hgO
      simp only [frP, frN]; unfold Apart at this ⊢; omega

theorem opX_sub {M : Memory} {p n k : Nat} (h : OpX M st p n) (hk : k ≤ n) : OpX M st p k := by
  intro hk0
  obtain ⟨h1, h2⟩ := h (by omega)
  unfold Apart at h1 h2 ⊢; exact ⟨by omega, by omega⟩

set_option maxRecDepth 20000 in
/-- divmc's `SqrX` for `zz.sqr(stk, z)` inside a round (`zz = (q, qc)`, `z = (p, l, c)`) -/
theorem sqrX_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) :
    CapIn R L1 p l c ∧ SqrX R L1 S' stk above st q qc p l c := by
  have hK := sp_K hpre
  have hsp' := sp'_eq hsp
  obtain ⟨-, hrt, hz, hzz, hap, hlc, -, hnc, hqc⟩ := hmid
  have hc : 0 < c := by omega
  have hw := (wrOut_own hzz hK hsp' h28 hm hstk habove).2.2 hqc
  refine ⟨capIn_own hz hc hlc, stkX_at hpre hrt hsp' h28 hm hstk habove, hw.1, fun he => ?_, ?_, ?_⟩
  · subst he; unfold Apart at hap; omega
  · rw [hm]; exact opX_own hpre hrt hzz
  · rw [hm]; exact opX_sub (opX_own hpre hrt hz) (by omega)

set_option maxRecDepth 20000 in
/-- divmc's `MulX` for `zz.mul(stk, zz, x[:k])` inside a round -/
theorem mulX_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {k : Nat} (hk : k ≤ xl) :
    CapIn R L1 q ql qc ∧ CapIn R L1 xp k xc ∧ MulX R L1 S' stk above st q qc q ql qc xp k xc := by
  have hK := sp_K hpre
  have hsp' := sp'_eq hsp
  obtain ⟨-, hrt, -, hzz, -, -, hqlc, -, hqc⟩ := hmid
  have hw := (wrOut_own hzz hK hsp' h28 hm hstk habove).2.2 hqc
  have hxl : 0 < xl := hpre.2.2.2.2.2.2.2.2.2.1
  obtain ⟨cx, ox⟩ := capIn_x hpre hrt hk
  refine ⟨capIn_own hzz hqc hqlc, cx, stkX_at hpre hrt hsp' h28 hm hstk habove, hw.1, fun _ => rfl, fun he => ?_,
    ?_, ?_, ?_⟩
  · have := hzz.2.2.2.2.2.2.1; subst he; unfold Apart at this; omega
  · rw [hm]; exact opX_own hpre hrt hzz
  · rw [hm]; exact opX_sub (opX_own hpre hrt hzz) (by omega)
  · rw [hm]; exact ox

end

end FvModexp.Arm64.ModInv
