import FvModexp.Proofs.Arm64.Exp.EvJ11
import FvModexp.Proofs.Arm64.Exp.EvSmP
import FvModexp.Proofs.Arm64.Exp.EvNP

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `modularInverseModPowerOfTwo`'s precondition at `m1.modularInverseModPowerOfTwo(stk, m2, n)`
(agent infra)

`miPre`: `ModInv.PreL` (args `z = m1`, `stk`, `x = m2`, `n`) at the callee entry `S'` (`SP = sp`, window
`[sp - (240 + kc), sp + 72)`), from `EPre`, `WC` and the two located locals. Split into small lemmas (`miStk`: the
stack facts, `miOne`: `natOne`, `miOp`: a located local's `StkApart` / `OpX`) so no `omega` sees the whole context.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

theorem apart_shrinkL {a k b n k' : Nat} (h : Apart a k b n) (hk : k' ≤ k) : Apart a k' b n := by
  unfold Apart at h ⊢; omega

/-- a range outside the stack's writable ranges is `StkApart` -/
theorem stkApart_of_out {M : Memory} {st a k : Nat} (h : Outside a k (stkWs M st)) : StkApart M st a k := by
  intro _
  simp only [stkWs, outside_cons, outside_nil, and_true] at h
  refine ⟨by unfold Apart; omega, fun _ => by unfold Apart; omega⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a located local (a prefix `8 k'` of it): `StkApart` and `OpX` at the current memory -/
theorem miOp (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p l c v : Nat} (hq : LN R L s.mem st M L1 p l c v) (hc : 0 < c)
    {k' : Nat} (hk : k' ≤ 8 * c) : StkApart M st p k' ∧ OpX M st p k' := by
  have hloc := (hq.1.2.2 hc).1
  have hob := (hq.1.2.2 hc).2
  obtain ⟨-, w2, -, -⟩ := Loc.ap hP hloc
  have hogA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr := hob.free h.sok.2.2.2.2.2.1
  have hgA : Apart p (8 * c) RunIface.gA 32 := Loc.apart hloc hc hogA.1 (fun _ => hogA.2.2.2)
  simp only [free] at hfr
  refine ⟨fun _ => ⟨apart_shrinkL w2 hk, fun _ => apart_shrinkL hfr hk⟩, fun _ => ⟨?_, apart_shrinkL hgA hk⟩⟩
  simp only [frP, frN]; exact apart_shrinkL hfr hk

set_option maxRecDepth 20000 in
/-- the stack facts of `ModInv.Pre` (`PX`'s first six, and `gA` outside the stack's writable ranges) -/
theorem miStk (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    st ≠ 0 ∧ Apart st 24 StackNat.wbA 4 ∧ Apart st 24 RunIface.gA 32 ∧ Apart st 24 (frP M st) (frN M st) ∧
      Apart (frP M st) (frN M st) RunIface.gA 32 ∧ (stCap M st = 0 → stW M st = 0) ∧
      Outside RunIface.gA 32 (stkWs M st) := by
  have hst := nstk_of hP h (KN := 0) (by have := hP.1.2.2.2.2.2.2.2.1; omega)
  have hogA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst0 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 := hst.2.2.2.2.2.2.2.2.1
  have h2 := hst.2.2.2.2.2.2.2.2.2.1
  have h3 := hst.2.2.2.2.2.2.2.2.2.2
  have h4 := hogA.2.2.1
  simp only [W4En.free] at h2 h3
  refine ⟨hst0, h1, by unfold Apart at h4 ⊢; omega, h2, h3, hst.2.2.2.2.2.2.1, ?_⟩
  simp only [stkWs, outside_cons, outside_nil, and_true]
  unfold Apart at h3 h4
  omega

set_option maxRecDepth 20000 in
/-- `ModInv.OneIn` for `z = m1` at the callee `S'` (`SP = sp`) -/
theorem miOne (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {kc : Nat} (hK : 240 + kc ≤ K) (hkc : 4608 ≤ kc)
    {S' : State} (hsN : S'.sp.toNat = sp) (fm : S'.mem = M) {p l c v : Nat} (hq : LN R L s.mem st M L1 p l c v)
    (hc : 0 < c) : ModInv.OneIn R L1 S' kc p c st := by
  obtain ⟨op, hone, hsa, honeE, hsaE⟩ :=
    natOne_at hP h hsN (stk := 240 + kc) (above := 72) (lo := sp - 8) (hi := sp + 8) hK (by omega) (by omega)
      (by omega)
  obtain ⟨z5, z6, -, -⟩ := smZ hP hq (fun e => absurd e (by omega)) honeE hsaE (by omega)
  have hnw := hone.2.2.2.2.2.2.1
  rw [outside_append, outside_append] at hnw
  rw [← hsN] at hone
  have hone' := natOne_win (by omega) (by omega) hone
  subst fm
  exact ⟨op, hone', z5, z6, hsa, stkApart_of_out hnw.2.2⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`ModInv.PreL`** of `m1.modularInverseModPowerOfTwo(stk, m2, n)` at the callee entry `S'` (`SP = sp`) -/
theorem miPre (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {kc : Nat} (hK : 240 + kc ≤ K) (hkc : 4608 ≤ kc)
    {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {ra : Nat} (f30 : S'.regs 30 = BitVec.ofNat 64 ra) (hra : ra % 4 = 0 ∧ ra < 2 ^ 48)
    {p1 l1 c1 v1 q l2 c2 v2 n : Nat}
    (hm1 : LN R L s.mem st M L1 p1 l1 c1 v1) (hc1 : 0 < c1) (hp1 : p1 < 2 ^ 64)
    (hm2 : LN R L s.mem st M L1 q l2 c2 v2) (hl20 : 0 < l2) (hl2 : l2 ≤ 2 ^ 12) (hodd : v2 % 2 = 1)
    (hap : Apart q (8 * c2) p1 (8 * c1))
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2 ^ 15) (hs16 : ℓ + 8 * ModInv.NW n + 72 ≤ 2 ^ 16)
    (hb : ModInv.cost (sqC ℓ) (mlC ℓ) n ≤ b1) :
    ModInv.PreL R kc sqC mlC ℓ b1 L1 p1 l1 c1 st q l2 c2 n S' := by
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hr30 : (S'.regs 30).toNat = ra := by
    rw [f30, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hra.2; omega)
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.2.2.1
  have hc2 : 0 < c2 := Nat.lt_of_lt_of_le hl20 hm2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := 240 + kc) (above := 72) hK (by decide)
  have hgl := hw.globals hP (w := winA S' (240 + kc) 72) (fun a n ho => by
    simp only [winA, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  obtain ⟨x1, x2, x3, x4, x5, x6, x7⟩ := miStk hP hw
  have hogA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc1 := (hm1.1.2.2 hc1).1
  have hgA1 : Apart p1 (8 * c1) RunIface.gA 32 := Loc.apart hloc1 hc1 hogA.1 (fun _ => hogA.2.2.2)
  have hgo : Outside RunIface.gA 32 ([(p1, p1 + 8 * c1)] ++ stkWs M st) := by
    rw [outside_append]
    refine ⟨?_, x7⟩
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at hgA1; omega
  have hone := miOne hP hw hK hkc hsN fm hm1 hc1
  obtain ⟨o1a, o1b⟩ := miOp hP hw hm1 hc1 (Nat.le_refl _)
  obtain ⟨o2a, o2b⟩ := miOp hP hw hm2 hc2 (Nat.mul_le_mul_left 8 hm2.2.1)
  have hlv2 := hm2.1.2.1 hc2
  have hrd := LN.rd hP hm2 hc2 hsN fm (stk := 240 + kc) (above := 72) hK (by omega)
  have hwr := DL.wr hP hm1.1 hsN hgN fm (stk := 240 + kc) (above := 72) hK (by omega)
  have hsi := hw.stkIn hP hsN hgN fm (stk := 240 + kc) (above := 72) hK (by omega)
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  subst fm
  refine ⟨⟨hce, hsv, ⟨hgl, hgo⟩, hn1, hn2, hm1.2.1, hp1, hc1, hwr, hl20, hm2.2.1, hm2.1.1, hl2, hrd, hm2.2.2.2,
    by rw [hm2.2.2.1]; exact hodd, fun _ => hap.symm, hsi, by rw [hlen]; exact hs16, o1a, o2a, hb,
    by rw [hgN]; exact hw.inv, by rw [hr30]; exact hra.1, by rw [hr30]; exact hra.2, hwT,
    hone, x1, x2, x3, x4, x5, x6, ⟨hm2.2.1, hm2.1.1, hlv2.2.1, hlv2.2.2.2⟩, o1b, o2b⟩, hlen⟩

end

end FvModexp.Arm64.ExpEven
