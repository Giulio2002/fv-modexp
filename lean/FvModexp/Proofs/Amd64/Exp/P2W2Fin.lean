import FvModexp.Proofs.Amd64.Exp.P2W2Tl
import FvModexp.Proofs.Amd64.Exp.P2W2WC
import FvModexp.Proofs.Amd64.Exp.NHyp

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the function's post `FQ` from the tail (agent divmc s69; amd64 twin of agent
infra's `Arm64.P2W2Fin`)

`FQ` = the ABI facts (`RSP` popped, `RBP`, `R14`, `X15` kept) and `NHyp.CPostR` (window `[RSP - (K + 0x1d8), RSP + 0x60)`
= `[sp - 8 - K, sp + 0x230)`). `finQ`: from `WC` at the tail's memory `M`, a result nat in the `NatOF` form and
`TPost` (the closure restored `len = len₀`), the post holds. `tenv_of`: the tail's static facts `TEnv` from `EPre`,
`WC` and the frame slots `ESl` at `M`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open FvModexp.Amd64.ExpHyp

/-- the function's post -/
@[reducible] def FQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) : Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    NHyp.CPostR R b L (K + 0x1d8) 0x60 zp zc st v cst s s'

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

/-- a result nat (`NatOF`) with a non-empty array is apart from the window and the stack header -/
theorem res_apart (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) (hc : 0 < c) :
    Apart p (8 * c) (sp - 8 - K) (K + 0x238) ∧ Apart p (8 * c) st 24 := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, -, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  rcases hr with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
  · obtain ⟨⟨-, h2, h3, -⟩, -⟩ := hz hc
    exact ⟨h2, h3⟩
  · refine ⟨(hin.apart (by simpa using hrt)).symm, ?_⟩
    rcases k2 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart; omega
    · exact (hin.apart hO).symm

theorem res_bytes (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) :
    ∀ i, i < 8 * c → Outside (p + i) 1 (TW sp st) := by
  intro i hi
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := res_apart hP hr (by omega)
  unfold Apart at h1 h2
  simp only [TW, outside_cons, outside_nil, and_true]
  omega

theorem out_win {rt : List (Nat × Nat)} {m : Memory} {a n : Nat} (hK : 8 ≤ K) (hKs : K + 8 ≤ sp)
    (ho : Outside a n (rt ++ [(sp - 8 - K, sp + 0x230)] ++ [(zp, zp + 8 * zc)] ++ stWs m st)) :
    Outside a n (rt ++ WN sp K ++ ZS zp zc st m) ∧ Outside a n (TW sp st) := by
  simp only [outside_append] at ho ⊢
  refine ⟨⟨⟨ho.1.1.1, ?_⟩, ho.1.2, ho.2⟩, ?_⟩
  · have := ho.1.1.2
    simp only [WN, outside_cons, outside_nil, and_true] at this ⊢
    omega
  · have h1 := ho.1.1.2
    have h2 := ho.2
    simp only [TW, stWs, stkWs, outside_cons, outside_nil, and_true] at h1 h2 ⊢
    omega

set_option maxRecDepth 20000 in
/-- **the function's post** from the tail -/
theorem finQ (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p l c v cst : Nat} (hres : NatOF R L L1 M zp zc 1 p l c v) (hrs : ResSep s.mem M st p c) (hb : b - cst ≤ b1)
    {s' : State}
    (ht : TPost sp g st (stLen s.mem st) bp p l c s.fsBase M s') :
    FQ R b L K zp zc st v cst s s' := by
  obtain ⟨t4, t5, t14, tfs, tx15, tdf, t0, t3, t1, t8, tF⟩ := ht
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hsp48 : sp - 8 + 0x238 ≤ 2 ^ 48 := hP.cenv0.2.2.1
  have hs4 : s.regs 4 = BitVec.ofNat 64 (sp + 0x1d0) := hP.1.1
  have hs14 : s.regs 14 = BitVec.ofNat 64 g := hP.1.2.1
  have hx15 : s.xmm 15 = 0 := hP.1.2.2.2.1
  have hdf : s.df = false := hP.1.2.2.2.2.1
  have hg48 : g + 24 ≤ 2 ^ 48 := hP.cenv0.2.2.2.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -, -, -, -, -, -, -, -, hbp, -⟩ := hP'
  have hout : Outside (sp - 8 - K) (K + 0x238) R.rt := hP.win_rt
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
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
  have hby := res_bytes hP v6
  have hokM := hw.sok
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := hokM
  have hlen := hw.len
  have hlo := hw.lo
  have hg : (s.regs 14).toNat = g := by rw [hs14]; exact toNat_of (by omega)
  refine ⟨⟨?_, ?_, t14.trans hs14.symm, tx15.trans hx15.symm⟩, tfs, tdf.trans hdf.symm, p, l, c, t0, t3, t1, L1,
    b1 + stkR H s'.mem st, ?nat, ⟨hw.le, Nat.le_trans hb (Nat.le_add_right _ _), ?inv⟩,
    ⟨⟨?sok, t8, ?kf⟩, hw.ain.congr e0 e2 fun _ hr => hr⟩, ?fr, ?lf,
    fun hc hn => by rw [e0, e2] at hn ⊢; exact hrs hc hn⟩
  · rw [t4, hs4, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  · rw [t5, ← hbp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
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
    rw [hg, stkR_congr e2]
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
    have hwin : win s (K + 0x1d8) 0x60 = [(sp - 8 - K, sp + 0x230)] := by
      simp only [win, hs4, toNat_of (show sp + 0x1d0 < 2 ^ 64 by omega)]
      rw [show sp + 0x1d0 - (K + 0x1d8) = sp - 8 - K by omega, show sp + 0x1d0 + 0x60 = sp + 0x230 by omega]
    rw [hwin]
    exact hw.fr.trans tF fun a n ho => out_win (by omega) (by omega) ho
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [tF.readLE a n ?_, hw.lf.readLE a n hin ho]
    obtain ⟨r0, hr0, q1, q2⟩ := hin
    have := hLs r0 hr0
    simp only [stkWs, stWs, outside_append, outside_cons, outside_nil, and_true] at this ho
    simp only [TW, outside_cons, outside_nil, and_true]
    omega

/-- the tail's static facts from the entry facts, the context and the frame slots at the tail's memory -/
theorem tenv_of (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) : TEnv sp st (stLen s.mem st) bp r M := by
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -, -, -, -, -, -, -, -, -, -, hr47, -⟩ := hP'
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hal : sp % 8 = 0 := hP.1.2.2.2.2.2.1
  obtain ⟨-, hK0, hA0, hacc, -⟩ := hw.cenv hP
  obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := hsl
  obtain ⟨-, -, hsa, hs48, -, hlc, -⟩ := hw.sok
  have hlen := hw.len
  have hlo := hw.lo
  unfold Apart at hstw
  refine ⟨hal, by omega, by omega, M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega), a3, a4, a5, a6, hs48,
    hsa, by simp only [stLen, stCap] at hlen hlo hlc ⊢; omega, by unfold Apart; omega, a1, a2, hr47⟩

end

end FvModexp.Amd64.P2W2
