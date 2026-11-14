import FvModexp.Proofs.Amd64.Exp.EvAdd
import FvModexp.Proofs.Amd64.Exp.EvTail

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `J15` → the tail → the function's post `FQ` (asm s64; twin of infra's arm64 `EvFin`)

`FQ` = the Summary exit facts (`RSP + 8`, `RBP`, `R14`, `X15`) and `NHyp.CPostR` with the entry window
`[RSP - (K + 0x150), RSP + 0x70)` (`RSP = sp + 0x148`; it covers `WN sp K` and the tail's stack writes). `finQ`:
from `WC` at the tail's memory, a `NatOF` result, `ResSep` and `TPost`. `vEven`: the result value is `X^Y mod M`
(mathdiv's `Exp.expNNEven_correct`). `segFin`: `J15` → `RET` with `FQ`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.ExpHyp

/-- the function's post (internal form) -/
@[reducible] def FQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) : Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    NHyp.CPostR R b L (K + 0x150) 0x70 zp zc st v cst s s'

/-- the value: `z + ((z1 - z) · m2⁻¹ mod 2^n) · m2 = X^Y mod M` -/
theorem vEven (s : State) (xp xl yp yl mp ml : Nat) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) :
    vZ2 s xp xl yp yl mp ml + vU s xp xl yp yl mp ml =
      natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml := by
  have h := Exp.expNNEven_correct (fun x y m => x ^ y % m) (natVal s.mem xp xl) (natVal s.mem yp yl)
    (natVal s.mem mp ml) hM hev (fun _ _ _ _ => rfl)
  rw [← h]
  rfl

/-- the entry window of the post contains the function's own writes -/
theorem frm_fin {rt ws : List (Nat × Nat)} {m0 M m' : Memory} {sp K st : Nat} (hK : K + 8 ≤ sp) (hK8 : 8 ≤ K)
    (h1 : MemFrame m0 M (rt ++ WN sp K ++ ws)) (h2 : MemFrame M m' (TW sp st))
    (hz : ∀ a n, Outside a n ws → Outside a n [(st + 8, st + 16)]) :
    MemFrame m0 m' (rt ++ [(sp - 8 - K, sp + 0x1b8)] ++ ws) := by
  refine h1.trans h2 fun a n ho => ⟨?_, ?_⟩
  · simp only [WN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true] at ho
    have := hz a n ho.2
    simp only [outside_cons, outside_nil, and_true] at this
    simp only [TW, outside_cons, outside_nil, and_true]
    omega

theorem win_fin {s : State} {sp K : Nat} (h : (s.regs 4).toNat = sp + 0x148) (hK : K + 8 ≤ sp) :
    win s (K + 0x150) 0x70 = [(sp - 8 - K, sp + 0x1b8)] := by
  simp only [win, h]
  rw [show sp + 0x148 - (K + 0x150) = sp - 8 - K by omega, show sp + 0x148 + 0x70 = sp + 0x1b8 by omega]

theorem sp_fin {sp : Nat} (h : sp + 0x1b8 ≤ 2 ^ 48) :
    BitVec.ofNat 64 (sp + 0x150) = BitVec.ofNat 64 (sp + 0x148) + 8 := by
  bv_omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- the caller's `RBP` / the return address of the entry -/
theorem EPre.bpr (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    (s.regs 5).toNat = bp ∧ r < 2 ^ 47 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨h1, -, h2, -⟩, -⟩ := hP
  exact ⟨h1, h2⟩

theorem res_apartE (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) (hc : 0 < c) :
    Apart p (8 * c) (sp - 8 - K) (K + 0x1c0) ∧ Apart p (8 * c) st 24 := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
  · obtain ⟨⟨-, h2, h3, -⟩, -⟩ := hP.zF hc
    exact ⟨h2, h3⟩
  · refine ⟨hin.apart hP.win_rt |>.symm, ?_⟩
    rcases hP.stk0.2.1 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart; omega
    · exact (hin.apart hO).symm

theorem res_bytesE (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) :
    ∀ i, i < 8 * c → Outside (p + i) 1 (TW sp st) := by
  intro i hi
  have hk := hP.kf
  obtain ⟨h1, h2⟩ := res_apartE hP hr (by omega)
  unfold Apart at h1 h2
  simp only [TW, outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the function's post** from the tail -/
theorem finQ (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p l c v cst : Nat} (hres : NatOF R L L1 M zp zc 1 p l c v) (hrs : ResSep s.mem M st p c) (hb : b - cst ≤ b1)
    {s' : State} (ht : TPost sp g fs st (stLen s.mem st) bp p l c M s') :
    FQ R b L K zp zc st v cst s s' := by
  obtain ⟨t4, t5, t14, tfs, tx, tdf, t0, t3, t1, t8, tF⟩ := ht
  have hk := hP.kf
  have hE := hP.1
  have hbr := hP.bpr
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw := hP.stkF.1
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
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := hw.sok
  have hlen := hw.len
  have hlo := hw.lo
  have hsN : (s.regs 4).toNat = sp + 0x148 := hE.sp
  refine ⟨⟨by rw [t4, hE.1]; exact sp_fin hk.2.2.2.2, by rw [t5]; exact (bv_of_toNat hbr.1).symm,
    by rw [t14, hE.2.1], by rw [tx, hE.2.2.2.1]⟩,
    BitVec.eq_of_toNat_eq (by rw [tfs, hE.2.2.1]), by rw [tdf, hE.2.2.2.2.1], p, l, c, t0, t3, t1, L1, b1, ?nat,
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
    rw [hE.g]
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
    rw [win_fin hsN hk.2.2.1, show stWs s.mem st = stkWs s.mem st from rfl, List.append_assoc _ [(zp, zp + 8 * zc)]]
    refine frm_fin hk.2.2.1 (by omega) (by simpa only [ZS, List.append_assoc] using hw.fr) tF fun a n ho => ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [tF.readLE a n ?_, hw.lf.readLE a n hin ho]
    obtain ⟨r0, hr0, q1, q2⟩ := hin
    have := hLs r0 hr0
    simp only [outside_append, outside_cons, outside_nil, and_true] at this ho
    simp only [TW, outside_cons, outside_nil, and_true]
    omega

set_option maxRecDepth 20000 in
/-- the tail's environment from `WC` and the slots -/
theorem tenv_of (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {n : Nat}
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl yc mp ml mc (stLen s.mem st) n) :
    TEnv sp st (stLen s.mem st) bp r M := by
  have hk := hP.kf
  have hacc0 := hP.cenv0.2.2.2.1
  have hstw := hP.stkF.1
  have hbr := hP.bpr
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hsl
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := hw.sok
  have hlen := hw.len
  have hlo := hw.lo
  unfold Apart at hstw
  refine ⟨hk.2.2.2.1, by omega, hk.2.2.2.2,
    by rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc0 (by omega) (by omega),
    a3, a4, a5, a6, h48, hacc, by show stLen s.mem st ≤ stCap M st; omega, by unfold Apart; omega, a1, a2, hbr.2⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- **`J15` → `RET`** with the function's post (`cst`: the total cost, `b - cst ≤ rk`) -/
theorem segFin {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk cst : Nat} (hcst : b - cst ≤ rk)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 l2 p l c : Nat}
    (h : J15 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 l1 l2 p l c) :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 r) S
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml) cst s) := by
  have hc40 := h.res.2.2.2.1
  have hlc := h.res.2.2.1
  have hres := h.res
  rw [vEven s xp xl yp yl mp ml hM hev] at hres
  have hb : b - cst ≤ b1 := Nat.le_trans hcst h.jx.bud
  exact ReachesRet.mono (tailE hap S sp g fs st (stLen s.mem st) bp r p l c S.mem h.pc h.jx.esp h.jx.e14 h.jx.efs
    h.jx.ex15 h.jx.edf h.r0 h.r3 h.r1 rfl h.p64 (by omega) (by omega) (tenv_of hP h.jx.wc h.jx.esl))
    (fun s' ht => finQ hP h.jx.wc hres h.rs hb ht)

end

end FvModexp.Amd64.ExpEven
