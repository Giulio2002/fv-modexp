import FvModexp.Proofs.Amd64.Exp.EvJ11
import FvModexp.Proofs.Amd64.Exp.EvSmP
import FvModexp.Proofs.Amd64.Exp.EvNP

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `modularInverseModPowerOfTwo`'s precondition at `m1.modularInverseModPowerOfTwo(stk, m2, n)`
(asm s62; twin of infra's arm64 `EvMiP`)

`miPre`: `ModInv.PreQ` (args `z = m1`, `stk`, `x = m2`, `n`; reserve level `H = ℓ + D n`, real budget `b1`) at the
callee entry `S'` (`RSP = sp - 8`, window `[sp - 8 - (232 + kc), sp - 8 + 72)`). Split into small lemmas: `miStk`
(divmc's `Q.NatSqr.StkPre`), `miOp` (a located local's `StkSep`), `miOne` (`ModInv.OneIn`). amd64 `OneIn` asks
`StkSep st op 8`, whose `Apart op 8 gA 32` (natOne's word vs. the threshold globals; natOne is writable data, so not
fixed by `DataLoaded`) is not in `EPre`: it is the separate hypothesis `hopA` (entry form
`Apart (s.mem.readLE natOneA 8) 8 RunIface.gA 32`), threaded like `XC` up to `EvenSum`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

theorem outside_zero {rs : List (Nat × Nat)} : Outside 0 0 rs := by
  induction rs with
  | nil => simp only [outside_nil]
  | cons r rs ih => obtain ⟨lo, hi⟩ := r; simp only [outside_cons]; exact ⟨by omega, ih⟩

theorem apart_shrinkL {a k b n k' : Nat} (h : Apart a k b n) (hk : k' ≤ k) : Apart a k' b n := by
  unfold Apart at h ⊢; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a located local (a prefix `k'` of it): `StkSep` at the current memory -/
theorem miOp (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p l c v : Nat} (hq : LN R L s.mem st M L1 p l c v) (hc : 0 < c)
    {k' : Nat} (hk : k' ≤ 8 * c) : StkSep M st p k' := by
  have hloc := (hq.1.2.2 hc).1
  have hob := (hq.1.2.2 hc).2
  obtain ⟨-, w2, -, -⟩ := Loc.ap hP hloc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hogA, -⟩ := hP
  have hfr := hob.free h.sok.2.2.2.2.2.1
  have hgA : Apart p (8 * c) RunIface.gA 32 := Loc.apart hloc hc hogA.1 (fun _ => hogA.2.2.2)
  simp only at hfr
  refine ⟨(apart_shrinkL w2 hk).symm, ?_, apart_shrinkL hgA hk⟩
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; exact apart_shrinkL hfr hk

set_option maxRecDepth 20000 in
/-- **`StkPre`** at a callee entry `S'` (`RSP = sp - 8`, window `[sp - 8 - W, sp - 8 + 72)`, `W ≤ K`) -/
theorem miStk (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S' : State} (tsp : (S'.regs 4).toNat = sp - 8)
    (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs) (fm : S'.mem = M) {W : Nat} (hW : W ≤ K) :
    StkPre R L1 S' W 72 st := by
  have hk := hP.kf
  obtain ⟨hst0, -, hok, -, -, -, -, hc0, -, hstwb, hstf, hfgA, hftl⟩ := nstk_of hP h (KN := 0) (by omega)
  obtain ⟨hstw, hstg, hsttl, -, -, -, -⟩ := hP.stkF
  have har := arr_at hP h
  have hogA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlc := hok.2.2.2.2.2.1
  have hnl := hok.2.2.2.2.1
  subst fm
  simp only [StkPre, Q.BasicSqr.freeP, Q.BasicSqr.freeN, Q.NatSqr.guard, Q.NatSqr.tls, win, tsp, tg, tfs]
  simp only at hstf hfgA hftl
  unfold Apart at hstw
  refine ⟨by omega, hok, by simp only [outside_cons, outside_nil, and_true]; omega, hstg, fun hc => ?_, ?_, ?_,
    hstf, hstwb, ?_, (hogA.2.2.1).symm, hfgA, hsttl, fun hc => (har hc).2.2, hftl⟩
  · obtain ⟨a1, a2, -⟩ := har hc
    unfold Apart at a1
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, a2⟩
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [hc0 e, e]; unfold Apart; omega
    · have := (har e).2.1; unfold Apart at this ⊢; omega
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · simp only [outside_cons, outside_nil, and_true]; rw [hc0 e, e]; omega
    · have := (har e).1; unfold Apart at this
      simp only [outside_cons, outside_nil, and_true]; omega
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [hc0 e, e, show stLen S'.mem st = 0 by omega]; exact Or.inr outside_zero
    · exact (hnl e).2.1.sub (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- `ModInv.OneIn` for `z = m1` at the callee `S'` (`RSP = sp - 8`) -/
theorem miOne (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hopA : Apart (s.mem.readLE natOneA 8) 8 RunIface.gA 32)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {kc : Nat} (hK : 232 + kc ≤ K)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (fm : S'.mem = M) {p l c v : Nat}
    (hq : LN R L s.mem st M L1 p l c v) (hc : 0 < c) : ModInv.OneIn R L1 S' kc p c st := by
  have hk := hP.kf
  obtain ⟨op, hone, -, honeE, hsaE⟩ :=
    natOne_at hP h (stk := 232 + kc) (above := 72) (lo := sp) (hi := sp) hK (by omega) (by omega) (by omega)
  obtain ⟨z5, z6, -, -, -⟩ := smZ hP hq (fun e => absurd e (by omega)) honeE hsaE (by omega)
  have hop : Apart op 8 RunIface.gA 32 := by rw [← honeE.1]; exact hopA
  have hlc := h.sok.2.2.2.2.2.1
  have hnw := hone.2.2.2.2.2.2.1
  have how := hone.2.2.2.2.2.2.2.2.2.2
  rw [outside_append, outside_append] at hnw how
  have hone' : NatOne R L1 S'.mem op (win S' (ModInv.K kc) ModInv.A) := by
    simp only [win, tsp, fm, ModInv.K, ModInv.A]; exact natOne_win hone
  obtain ⟨-, w1, w2⟩ := how
  obtain ⟨-, n1, n2⟩ := hnw
  simp only [stkWs, outside_cons, outside_nil, and_true] at w2 n2
  subst fm
  refine ⟨op, hone', z5, z6, ⟨?_, ?_, hop⟩, ⟨?_, ?_, ?_⟩⟩
  · unfold Apart; omega
  · simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; unfold Apart; omega
  · unfold Apart; omega
  · simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; unfold Apart; omega
  · unfold Apart; decide

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`ModInv.PreQ`** of `m1.modularInverseModPowerOfTwo(stk, m2, n)` at the callee entry `S'` (`RSP = sp - 8`),
reserve level `ℓ + D n`, budget `b1` -/
theorem miPre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hopA : Apart (s.mem.readLE natOneA 8) 8 RunIface.gA 32) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {kc : Nat} (hK : 232 + kc ≤ K)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M) {p1 l1 c1 v1 q l2 c2 v2 n : Nat}
    (hm1 : LN R L s.mem st M L1 p1 l1 c1 v1) (hc1 : 0 < c1) (hp1 : p1 < 2 ^ 64)
    (hm2 : LN R L s.mem st M L1 q l2 c2 v2) (hl20 : 0 < l2) (hl2 : l2 ≤ 2 ^ 12) (hodd : v2 % 2 = 1)
    (hap : Apart q (8 * c2) p1 (8 * c1))
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2 ^ 15) (hs16 : ℓ + 8 * ModInv.NW n + 72 ≤ 2 ^ 16)
    (hb : ModInv.cost sqrC mulC l2 n + stkRes (ℓ + ModInv.D n) ≤ b1) :
    ModInv.PreQ R kc (ℓ + ModInv.D n) sqrC mulC b1 L1 p1 l1 c1 st q l2 c2 n S' := by
  have hk := hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.1
  have hadx : M.accessible Callees.adxAddr 1 false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.1
  have hc2 : 0 < c2 := Nat.lt_of_lt_of_le hl20 hm2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := 232 + kc) (above := 72) hK (by omega) (by omega)
  have hgl := hw.globals hP (w := win S' (ModInv.K kc) ModInv.A) (fun a n ho => by
    simp only [win, tsp, ModInv.K, ModInv.A, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hogA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc1 := (hm1.1.2.2 hc1).1
  have hgA1 : Apart p1 (8 * c1) RunIface.gA 32 := Loc.apart hloc1 hc1 hogA.1 (fun _ => hogA.2.2.2)
  have hgS : Outside RunIface.gA 32 (stkWs M st) := by
    have hf := free_apart hw hogA.1 hogA.2.2.2
    have h2 := hogA.2.2.1
    have := hw.sok.2.2.2.2.2.1
    simp only at hf
    simp only [stkWs, outside_cons, outside_nil, and_true]
    unfold Apart at hf h2; omega
  have hgo : Outside RunIface.gA 32 ([(p1, p1 + 8 * c1)] ++ stkWs M st) := by
    rw [outside_append]
    refine ⟨?_, hgS⟩
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at hgA1; omega
  have hone := miOne hP hopA hw hK tsp fm hm1 hc1
  have o1 := miOp hP hw hm1 hc1 (Nat.le_refl _)
  have o2 := miOp hP hw hm2 hc2 (Nat.mul_le_mul_left 8 hm2.2.1)
  have hlv2 := hm2.1.2.1 hc2
  have hrd := LN.rd hP hm2 hc2 tsp fm (stk := 232 + kc) (above := 72) hK (by omega)
  have hwr := DL.wr hP hm1.1 tsp tg tfs fm (stk := 232 + kc) (above := 72) hK (by omega)
  have hsk := miStk hP hw tsp tg tfs fm (W := 232 + kc) hK
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hsr := stkR_le (ℓ + ModInv.D n) S'.mem st
  subst fm
  exact ⟨hce, hsv, ⟨hgl, hgo⟩, hn1, hn2, hm1.2.1, hp1, hc1, hwr, hl20, hm2.2.1, hm2.1.1, hl2, hrd, hm2.2.2.2,
    by rw [hm2.2.2.1]; exact hodd, ⟨hlv2.2.1, hlv2.2.2.2⟩, hap.symm, hsk, by rw [hlen]; exact hs16, o1, o2,
    ⟨by rw [hlen]; exact Nat.le_refl _, by omega⟩, by rw [tg]; exact hw.inv, hwT, hadx, hone⟩

end

end FvModexp.Amd64.ExpEven
