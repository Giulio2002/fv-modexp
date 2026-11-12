import FvModexp.Proofs.Arm64.Exp.EvAdd
import FvModexp.Proofs.Arm64.Exp.EvTail

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `J15` → the tail → the function's post `FQ` (agent infra; pattern of `P2W2Fin`)

`FQ` = the ABI facts and `NHyp.CPostR` with the entry window `[SP - (K + 336), SP + 112)`. `finQ`: from `WC` at the
tail's memory, a `NatOF` result, `ResSep` and `TPost`. `vEven`: the result value is `X^Y mod M` (mathdiv's
`Exp.expNNEven_correct`). `segFin`: `J15` → `RET` with `FQ`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.ExpHyp

/-- the function's post (internal form) -/
@[reducible] def FQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    NHyp.CPostR R b L (K + 336) 112 zp zc st v cst s s'

/-- the value: `z + ((z1 - z) · m2⁻¹ mod 2^n) · m2 = X^Y mod M` -/
theorem vEven (s : State) (xp xl yp yl mp ml : Nat) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) :
    vZ2 s xp xl yp yl mp ml + vU s xp xl yp yl mp ml =
      natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml := by
  have h := Exp.expNNEven_correct (fun x y m => x ^ y % m) (natVal s.mem xp xl) (natVal s.mem yp yl)
    (natVal s.mem mp ml) hM hev (fun _ _ _ _ => rfl)
  rw [← h]
  rfl

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

theorem res_apartE (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) (hc : 0 < c) :
    Apart p (8 * c) (sp - K) (K + 448) ∧ Apart p (8 * c) st 24 := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
  · obtain ⟨⟨-, h2, h3, -⟩, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc
    exact ⟨h2, h3⟩
  · refine ⟨hin.apart hP.win_rt |>.symm, ?_⟩
    rcases hP.stk0.2.1 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart; omega
    · exact (hin.apart hO).symm

theorem res_bytesE (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) :
    ∀ i, i < 8 * c → Outside (p + i) 1 (TW sp st) := by
  intro i hi
  have hK := hP.1.2.2.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := res_apartE hP hr (by omega)
  unfold Apart at h1 h2
  simp only [TW, outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 20000 in
/-- **the function's post** from the tail (copy of `P2W2.finQ`) -/
theorem finQ (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p l c v cst : Nat} (hres : NatOF R L L1 M zp zc 1 p l c v) (hrs : ResSep s.mem M st p c) (hb : b - cst ≤ b1)
    {s' : State}
    (ht : TPost sp g st (stLen s.mem st) p l c (s.regs 18) (s.regs 29) M s') :
    FQ R b L K zp zc st v cst s s' := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, tF⟩ := ht
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp := hP.1.sp
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw : Apart st 24 (sp - K) (K + 448) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a n, (∀ i, i < n → Outside (a + i) 1 (TW sp st)) → s'.mem.readLE a n = M.readLE a n :=
    fun a n h => MemFrame.bytewise tF h
  have hhd : ∀ a n, st ≤ a → a + n ≤ st + 8 ∨ st + 16 ≤ a ∧ a + n ≤ st + 24 → s'.mem.readLE a n = M.readLE a n := by
    intro a n h1 h2
    refine tF.readLE a n ?_
    simp only [TW, outside_cons, outside_nil, and_true]; omega
  have e0 : stW s'.mem st = stW M st := hhd _ _ (Nat.le_refl _) (Or.inl (by omega))
  have e2 : stCap s'.mem st = stCap M st := hhd _ _ (by omega) (Or.inr ⟨by omega, by omega⟩)
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hres
  have hby := res_bytesE hP v6
  have hokM := hw.sok
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := hokM
  have hlen := hw.len
  have hlo := hw.lo
  refine ⟨t1.trans hP.1.1.symm, t2, t3.trans hP.1.2.1.symm, t4, p, l, c, t5, t6, t7, L1, b1, ?nat,
    ⟨hw.le, hb, ?inv⟩, ⟨⟨?sok, t8, ?kf⟩, hw.ain.congr e0 e2 fun _ hr => hr⟩, ?fr, ?lf,
    fun hc hn => by rw [e0, e2] at hn ⊢; exact hrs hc hn⟩
  case nat =>
    refine ⟨?_, ?_, v3, v4, fun hc => ?_, v6⟩
    · rw [← v1]; exact hrd _ _ fun i hi => hby i (by omega)
    · rcases v2 with h | h
      · exact Or.inl h
      · rcases Nat.eq_zero_or_pos l with h0 | hl0
        · exact Or.inl h0
        right
        rw [hrd _ _ fun i hi => by rw [Nat.add_assoc]; exact hby (8 * (l - 1) + i) (by omega)]; exact h
    · obtain ⟨q1, q2, q3, q4⟩ := v5 hc
      exact ⟨q1, q2, by rw [tF.accessible]; exact q3, q4⟩
  case inv =>
    rw [hP.1.g]
    refine Expmc.inv_frame tF (fun r hr => ?_) hw.inv
    simp only [TW, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inr (hout.of_sub (by omega) (by omega))
      | exact hh.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega))
  case sok =>
    refine ⟨h8, hh, by rw [tF.accessible]; exact hacc, h48, ?_,
      by show s'.mem.readLE (st + 8) 8 ≤ _; rw [t8, e2]; omega, by rw [e2]; exact hc40⟩
    rw [e0, e2]
    intro hc
    obtain ⟨q1, q2, q3, q4⟩ := hlive hc
    exact ⟨q1, q2, by rw [tF.accessible]; exact q3, q4⟩
  case kf =>
    rcases hw.kf with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨e0.trans a1, e2.trans a2⟩
    · exact Or.inr (by rw [e0, e2]; exact ⟨a1, a2⟩)
  case fr =>
    have hwin : winA s (K + 336) 112 = WN sp K := by
      simp only [winA, WN, hsp]
      rw [show sp + 336 - (K + 336) = sp - K by omega, show sp + 336 - 8 = sp + 328 by omega,
        show sp + 336 + 8 = sp + 344 by omega, show sp + 336 + 112 = sp + 448 by omega]
    rw [hwin, show stWs s.mem st = stkWs s.mem st from rfl, List.append_assoc, List.append_assoc,
      ← List.append_assoc (WN sp K)]
    refine hw.fr.trans tF fun a n ho => ⟨by rw [List.append_assoc]; exact ho, ?_⟩
    simp only [WN, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
    simp only [TW, outside_cons, outside_nil, and_true]
    omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [tF.readLE a n ?_, hw.lf.readLE a n hin ho]
    obtain ⟨r0, hr0, q1, q2⟩ := hin
    have := hLs r0 hr0
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at this ho
    simp only [TW, outside_cons, outside_nil, and_true]
    omega

set_option maxRecDepth 20000 in
/-- the tail's environment from `WC` and the slots -/
theorem tenv_of (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {ret n : Nat}
    (hsl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl yc mp ml mc (stLen s.mem st) n) (hr4 : ret % 4 = 0)
    (hr48 : ret < 2 ^ 48) : TEnv sp g st (stLen s.mem st) (s.regs 29) ret M := by
  have hgM : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := MemFrame.bytewise hw.fr hP.g_out
  have hstw : Apart st 24 (sp - K) (K + 448) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstg : Apart st 24 (g + 16) 8 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hsl
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := hw.sok
  have hlen := hw.len
  have hlo := hw.lo
  obtain ⟨⟨-, -, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc0, -, -, -, -⟩, -⟩ := hP
  simp only [outside_cons] at hgo
  unfold Apart at hstw hstg
  refine ⟨hal, by omega, hsp2, by rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega),
    hg1, by rw [hw.fr.accessible]; exact hg2, by rw [hgM]; omega, by unfold Apart; omega, a3, a4, a5, a6, h48, hacc,
    by show stLen s.mem st ≤ stCap M st; omega,
    by unfold Apart; omega, by unfold Apart; omega, a1, a2, hr4, hr48⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- **`J15` → `RET`** with the function's post (`cst`: the total cost, `b - cst ≤ rk`) -/
theorem segFin {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) (hr4 : ret % 4 = 0) (hr48 : ret < 2 ^ 48) {rk cst : Nat}
    (hcst : b - cst ≤ rk)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 l2 p l c : Nat}
    (h : J15 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 l1 l2 p l c) :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 ret) S
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml) cst s) := by
  have hc40 := h.res.2.2.2.1
  have hlc := h.res.2.2.1
  refine tailE hap _ S sp g st (stLen s.mem st) p l c ret (s.regs 18) (s.regs 29) S.mem h.pc h.jx.esp h.r0 h.r1 h.r2
    h.jx.e18 h.jx.e28 rfl h.p64 (by omega) (by omega) (tenv_of hP h.jx.wc h.jx.esl hr4 hr48) fun s' ht => ?_
  have hres := h.res
  rw [vEven s xp xl yp yl mp ml hM hev] at hres
  exact finQ hP h.jx.wc hres h.rs (by have := h.jx.bud; omega) ht

end

end FvModexp.Arm64.ExpEven
