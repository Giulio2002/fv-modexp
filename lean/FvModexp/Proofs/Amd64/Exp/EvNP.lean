import FvModexp.Proofs.Amd64.Exp.EvJ
import FvModexp.Proofs.Amd64.Exp.NDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `nat.expNN`'s precondition `NPre` at the two recursive calls (asm s59; twin of infra's
arm64 `EvNP`)

At a call `z.expNN(stk, x, y, mm, false)` with `RSP = sp - 8` after the `CALL` (callee `sp_N = sp - 0x4a0`, window
`[sp - 0x4a0 - KN, sp + 0x70)` inside ours), `x`, `y` the entry operands, `mm = (pm, lm, cm)` a live local nat and the
destination `z = (t, k, k)` a scratch destination apart from `mm`: `npre_of` builds `ExpN.NPre` from `EPre`, the
context `WC`, the locals, the stack arguments `y`, `mm` at `sp + 0 … sp + 0x28` and `x`'s capacity facts `XC`
(amd64 `nat.expNN` reads `x` up to its capacity; not part of `EPre`, threaded separately). The stack-size bounds, the
budgets and `KN` are the caller's hypotheses. `CEnv.down` (local here) moves the callee environment below `sp - 8`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `CEnv` at a lower `sp` (window `[sp - d - K', sp - d + A')` inside `[sp - K, sp + A)`) -/
theorem CEnv.down {R : RtInv} {L : List (Nat × Nat)} {g fs sp K A : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs sp K A M) {d K' A' : Nat} (hd : d % 8 = 0) (hds : d ≤ sp) (hK : K' + d ≤ K)
    (hA : A' ≤ A + d) : CallW.CEnv R L g fs (sp - d) K' A' M := by
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd0, hro, f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨by omega, by omega, by omega,
    M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega), hg1, hg2, by omega,
    hrt.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgrt, ?_, hd0, hro, f1, f2, f3, f4, f5,
    by unfold Apart at f6 ⊢; omega⟩
  intro r hr
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- `x`'s capacity range at the entry (`nat.expNN` reads `x` up to `cap x`) -/
@[reducible] def XC (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (m0 : Memory) (xp xc : Nat) : Prop :=
  OE R L sp K st m0 xp (8 * xc) ∧ m0.accessible xp (8 * xc) false = true ∧ xp + 8 * xc ≤ 2 ^ 48

theorem apart_shrink {a k b n n' : Nat} (h : Apart a k b n) (hn : n' ≤ n) : Apart a k b n' := by
  unfold Apart at h ⊢; omega

theorem wTy_eq : W4En.wTy = StackNat.wT := rfl

/-- `ExpOdd.OBud` is monotone in the budget -/
theorem OBud.mono {costF : Nat → Nat → Nat → Nat} {n costD xl ylen l b b' : Nat}
    (h : ExpOdd.OBud costF n costD xl ylen l b) (hb : b ≤ b') : ExpOdd.OBud costF n costD xl ylen l b' := by
  unfold ExpOdd.OBud at h ⊢
  by_cases hy : 1 < ylen
  · simp only [hy, ↓reduceIte] at h ⊢; exact ⟨W4En.XnB.mono h.1 (by omega), by omega⟩
  · simp only [hy, ↓reduceIte] at h ⊢; exact ⟨W2En.XnB.mono h.1 (by omega), by omega⟩

/-- the precondition budget of `nat.expNN` (the PATH MAX part) at level `l`, modulus length `lm`, `log2 m = n` -/
@[reducible] def NBudE (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (xl yl lm l n : Nat) : Nat :=
  makeCost 1 + max (costR l xl lm) (makeCost lm + max (costS l xl yl lm) (costP l xl yl n))

/-- `nat.expNN`'s stack bounds at level `l`, modulus length `lm`, `log2 m = n` -/
@[reducible] def NStkE (needR : Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat) (xl yl lm l n : Nat) : Prop :=
  l + 23 * lm + 3 ≤ 2 ^ 16 ∧ l + needR xl lm ≤ 2 ^ 16 ∧ l + needS xl yl lm ≤ 2 ^ 16 ∧ l + needP xl yl n ≤ 2 ^ 16

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- an entry object as `nat.expNN`'s `NE` (window `[sp - 0x4a0 - KN, sp + 0x70)`) -/
theorem ne_oe (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN : KN + 0x498 ≤ K) {a k : Nat}
    (hoe : OE R L sp K st s.mem a k) : ExpN.NE R L1 (sp - 0x4a0) KN st M a k := by
  have hk := hP.kf
  obtain ⟨o1, o2, o3, o4⟩ := hoe
  refine ⟨h.le.held o1, ?_, o3, free_apart h o1 o4⟩
  unfold Apart at o2 ⊢; omega

/-- a located local array (a part `[t, t + n)` of it) as `NE` -/
theorem ne_loc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN : KN + 0x498 ≤ K) {t k n : Nat}
    (hl : Loc R L s.mem st t k) (ho : Ob R L1 st M t k) (hn : n ≤ 8 * k) : ExpN.NE R L1 (sp - 0x4a0) KN st M t n := by
  have hk := hP.kf
  obtain ⟨w1, w2, -, -, -⟩ := Loc.ap hP hl
  have hf := ho.free h.sok.2.2.2.2.2.1
  refine ⟨ho.1.sub (Nat.le_refl _) (by omega), ?_, ?_, ?_⟩
  · unfold Apart at w1 ⊢; omega
  · unfold Apart at w2 ⊢; omega
  · simp only [Apart] at hf ⊢; omega

/-- a located array is outside a range that is held at the entry and outside the entry's stack ranges -/
theorem Loc.out {t k a n : Nat} (hl : Loc R L s.mem st t k) (hh : Held R L a n)
    (ho : Outside a n (stkWs s.mem st)) : Outside a n [(t, t + 8 * k)] := by
  simp only [stkWs, outside_cons, outside_nil, and_true] at ho ⊢
  rcases hl with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · omega
  · have := hfresh hh hap hin; unfold Apart at this; omega

set_option maxRecDepth 20000 in
/-- `natOne` at `M`, outside `nat.expNN`'s window, a located array `(t, k)` and the stack's writable ranges -/
theorem natOne_loc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN : KN + 0x498 ≤ K) {t k : Nat}
    (hl : Loc R L s.mem st t k) :
    ∃ op, EvenHyp.NatOne R L1 M op ([(sp - 0x4a0 - KN, sp - 0x4a0 + 0x510), (t, t + 8 * k)] ++ ExpHyp.stWs M st) ∧
      NHyp.StkApart M st op 8 := by
  have hk := hP.kf
  obtain ⟨op, ⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩, hsa, ⟨-, -, -, -, -, -, ewin, -, -, eh, ew⟩, -⟩ :=
    natOne_at hP h (stk := KN + 0x498) (above := 0x78) (lo := sp) (hi := sp) (by omega) (by omega) (by omega)
      (by omega)
  have tA : Outside EvenHyp.natOneA 24 [(t, t + 8 * k)] :=
    Loc.out hl (Or.inr nrt) (by rw [List.cons_append, List.cons_append, outside_cons, outside_cons] at ewin; exact ewin.2.2)
  have tO : Outside op 8 [(t, t + 8 * k)] :=
    Loc.out hl eh (by rw [List.cons_append, List.cons_append, outside_cons, outside_cons] at ew; exact ew.2.2)
  refine ⟨op, ⟨n0, n8, n16, nw, na, nrt, ?_, oa, o48, oh, ?_⟩, hsa⟩
  · simp only [ExpHyp.stWs, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at nwin tA ⊢
    omega
  · simp only [ExpHyp.stWs, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at ow tO ⊢
    omega

set_option maxRecDepth 20000 in
/-- `nat.expNN`'s call environment (`RSP = sp - 8`, window `[sp - 0x4a0 - KN, sp + 0x70)`) -/
theorem nenv_of (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S : State} (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) {KN : Nat} (hKN : 41640 ≤ KN) (hKN1 : KN + 0x498 ≤ K) (hKN2 : KN + 0x98 ≤ 2 ^ 20) :
    ExpN.NEnv R L1 g fs (sp - 0x4a0) KN S := by
  have hk := hP.kf
  have hce := h.cenv hP
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  subst hm
  have hd := CEnv.down hce (d := 0x498) (K' := KN) (A' := 0x510) (by decide) (by omega) (by omega) (by omega)
  rw [show sp - 8 - 0x498 = sp - 0x4a0 by omega] at hd
  exact ⟨by rw [hsp]; congr 1; omega, h14, hfs, hx15, hdf, hKN, hKN2, hd, hsv⟩

set_option maxRecDepth 20000 in
/-- the stack's array at `M` (kept or fresh) is apart from the window, the guard and the TLS words -/
theorem arr_at (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 8 - K) (K + 0x1c0) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧ Apart (stW M st) (8 * stCap M st) (fs - 8) 8 := by
  have hce := hP.cenv0
  have hout := hP.win_rt
  obtain ⟨-, -, -, harr, -⟩ := hP.stkF
  intro hc
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · rw [e2] at hc; rw [e1, e2]; exact harr hc
  · exact ⟨(hin.apart hout).symm, (hin.apart hce.2.2.2.2.2.2.2.2.2.1).symm,
      (hin.apart hce.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm⟩

set_option maxRecDepth 20000 in
/-- `nat.expNN`'s stack facts -/
theorem nstk_of (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN1 : KN + 0x498 ≤ K) :
    0 < st ∧ st < 2 ^ 48 ∧ StkOK M R L1 st ∧ Apart st 24 (sp - 0x4a0 - KN) (KN + 0x510) ∧ Apart st 24 (g + 16) 8 ∧
    Apart st 24 (fs - 8) 8 ∧
    (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 0x4a0 - KN) (KN + 0x510) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧ Apart (stW M st) (8 * stCap M st) (fs - 8) 8) ∧
    (stCap M st = 0 → stW M st = 0) ∧
    M.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
    Apart st 24 (W4En.free M st).1 (W4En.free M st).2 ∧
    Apart (W4En.free M st).1 (W4En.free M st).2 RunIface.gA 32 ∧
    Apart (W4En.free M st).1 (W4En.free M st).2 (fs - 8) 8 := by
  have hk := hP.kf
  have hce := hP.cenv0
  have hc0 := WC.cap0 hP h
  have har := arr_at hP h
  have hlc := h.sok.2.2.2.2.2.1
  have hsok := hP.stk0
  have hsF := free_apart h hsok.2.1 hP.stkF.2.2.2.2.2.2
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hogA, -, hstw, hstg, hstf, -, hwbacc,
    hstwb, -, hst0, -⟩ := hP'
  have hgF := (free_apart h hogA.1 hogA.2.2.2).symm
  refine ⟨Nat.pos_of_ne_zero hst0, by have := hsok.2.2.2.1; omega, h.sok, ?_, hstg, hstf, ?_, hc0,
    by rw [h.fr.accessible]; exact hwbacc, hstwb, hsF, hgF, ?_⟩
  · unfold Apart at hstw ⊢; omega
  · intro hc
    obtain ⟨a1, a2, a3⟩ := har hc
    exact ⟨by unfold Apart at a1 ⊢; omega, a2, a3⟩
  · show Apart (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) (fs - 8) 8
    rcases Nat.eq_zero_or_pos (stCap M st) with e | e
    · rw [e, hc0 e]; unfold Apart; omega
    · have := (har e).2.2; unfold Apart at this ⊢; omega

theorem rd4a0 {M : Memory} {sp o v : Nat} (hs : 0x4a0 ≤ sp) (h : M.readLE (sp + o) 8 = v) :
    M.readLE (sp - 0x4a0 + (0x4a0 + o)) 8 = v := by
  rw [show sp - 0x4a0 + (0x4a0 + o) = sp + o by omega]; exact h

set_option maxRecDepth 20000 in
/-- `ExpN.XG` at a call memory `M` (a `WC` point) from the entry's -/
theorem xg_at (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hXC : XC R L sp K st s.mem xp xc)
    (hXG : ExpN.XG s.mem st xp xl xc) : ExpN.XG M st xp xl xc := by
  have hk := hP.kf
  obtain ⟨op, ⟨n0, -⟩, -, ⟨e0, -⟩, -⟩ :=
    natOne_at hP h (stk := 0) (above := 0) (lo := sp) (hi := sp) (Nat.zero_le _) (by decide) (by omega) (by omega)
  obtain ⟨xa, xn, xd, xacc, xst, xfr⟩ := hXG
  exact ⟨xa, by rw [n0, ← e0]; exact xn, by rw [h.fr.accessible]; exact xd, by rw [h.fr.accessible]; exact xacc, xst,
    free_apart h hXC.1.1 xfr⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`ExpN.NPre` at a recursive call** (see the module doc) -/
theorem npre_of (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hXC : XC R L sp K st s.mem xp xc)
    (hXG : ExpN.XG s.mem st xp xl xc)
    (hX : NHyp.XFacts R L xp xl xc) {S : State} (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) {KN : Nat} (hKN : 41640 ≤ KN) (hKN1 : KN + 0x498 ≤ K) (hKN2 : KN + 0x98 ≤ 2 ^ 20)
    {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {pm lm cm v t k : Nat} (hmm : LN R L s.mem st M L1 pm lm cm v) (hl0 : 0 < lm) (hl128 : lm ≤ 128)
    (hd : DL R L s.mem st M L1 t k) (hk : 0 < k) (hap : Apart t (8 * k) pm (8 * cm))
    (hy0 : M.readLE sp 8 = yp) (hy1 : M.readLE (sp + 8) 8 = yl) (hy2 : M.readLE (sp + 0x10) 8 = yc)
    (hq0 : M.readLE (sp + 0x18) 8 = pm) (hq1 : M.readLE (sp + 0x20) 8 = lm) (hq2 : M.readLE (sp + 0x28) 8 = cm)
    (hs1 : stLen M st + 23 * lm + 3 ≤ 2 ^ 16) (hs2 : stLen M st + needR xl lm ≤ 2 ^ 16)
    (hs3 : stLen M st + needS xl yl lm ≤ 2 ^ 16)
    (hs4 : stLen M st + needP xl yl (Nat.log2 (natVal M pm lm)) ≤ 2 ^ 16)
    (hbud : makeCost 1 + max (costR (stLen M st) xl lm) (makeCost lm + max (costS (stLen M st) xl yl lm)
      (costP (stLen M st) xl yl (Nat.log2 (natVal M pm lm)))) ≤ b1)
    (hob : ExpOdd.OBud costF lm costD xl yl (stLen M st) (b1 - makeCost lm)) :
    ExpN.NPre R b1 L1 KN costF costD needR costR needS needP costS costP g fs (sp - 0x4a0) t k k st xp xl xc yp yl
      yc pm lm cm 0 S := by
  have hxg := xg_at hP h hXC hXG
  revert hs1 hs2 hs3 hs4 hbud hob
  have hk0 := hP.kf
  have h4a0 : 0x4a0 ≤ sp := by omega
  have y0 := rd4a0 (M := M) (v := yp) (o := 0) h4a0 (by rw [Nat.add_zero]; exact hy0)
  have y1 := rd4a0 (o := 8) h4a0 hy1
  have y2 := rd4a0 (o := 0x10) h4a0 hy2
  have q0 := rd4a0 (o := 0x18) h4a0 hq0
  have q1 := rd4a0 (o := 0x20) h4a0 hq1
  have q2 := rd4a0 (o := 0x28) h4a0 hq2
  have hsN : (S.regs 4).toNat = sp - 8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hgl := h.globals hP (w := [(sp - 0x4a0 - KN, sp - 0x4a0 + 0x510)]) (fun a n ho => by
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hne := nenv_of hP h hsp h14 hfs hx15 hdf hm hKN hKN1 hKN2
  have hstk := nstk_of hP h hKN1
  have hwT := hP.2.2.1
  obtain ⟨⟨c40, hlv, hlo⟩, hlc', -, hmN⟩ := hmm
  have hcm : 0 < cm := Nat.lt_of_lt_of_le hl0 hlc'
  obtain ⟨-, -, macc, m48⟩ := hlv hcm
  have h8 : 8 * lm ≤ 8 * cm := Nat.mul_le_mul_left 8 hlc'
  obtain ⟨rc40, rlv, rlo⟩ := hd
  obtain ⟨ral, -, racc, r48⟩ := rlv hk
  obtain ⟨rl, ro⟩ := rlo hk
  obtain ⟨op, hone, hsa⟩ := natOne_loc hP h hKN1 rl
  obtain ⟨rw1, -, rg, rf, -⟩ := Loc.ap hP rl
  have rwo : Outside t (8 * k) [(sp - 0x4a0 - KN, sp - 0x4a0 + 0x510)] := by
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at rw1; omega
  have hP' := hP
  obtain ⟨-, -, -, hadx, -, -, hoy, hay, hy48, hyN, -, hyl, hox, hax, hx48, hxN, hxl, -, -, -, -, hz,
    hogA, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, hyc, -, -, -⟩, -, -⟩ := hP'
  have hzy : 0 < zc → Apart zp (8 * zc) yp (8 * yl) := fun h0 => (hz h0).2.2.2.2.2.2.2.1
  have hzx : 0 < zc → Apart zp (8 * zc) xp (8 * xl) := fun h0 => (hz h0).2.2.2.2.2.2.1
  obtain ⟨-, yN, -, -⟩ := obj_at hP h hoy hay hy48 hyN (Nat.le_trans hyl (by decide)) hzy hsN hm (stk := 0)
    (above := 0) (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨-, xN, -, -⟩ := obj_at hP h hox hax hx48 hxN (Nat.le_trans hxl (by decide)) hzx hsN hm (stk := 0)
    (above := 0) (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨hxOE, hxacc, hx48c⟩ := hXC
  subst hm
  intro hs1 hs2 hs3 hs4 hbud hob
  exact ⟨hne, hgl, hwT, by rw [wTy_eq]; exact hwT, by rw [h.fr.accessible]; exact hadx, rfl,
    y0, y1, y2, q0, q1, q2,
    hl0, hl128, hlc', c40,
    ne_loc hP h hKN1 (hlo hcm).1 (hlo hcm).2 h8,
    Janus.Arm64.Memory.accessible_weaken _
      (Janus.Arm64.Memory.accessible_mono _ macc (Nat.le_refl _) (Nat.add_le_add_left h8 pm)),
    Nat.le_trans (Nat.add_le_add_left h8 pm) m48, hmN,
    ne_oe hP h hKN1 hoy, by rw [h.fr.accessible]; exact hay, hy48, yN, hyl, hyc,
    ne_oe hP h hKN1 hxOE, by rw [h.fr.accessible]; exact hxacc, hx48c, xN, hxl, hX.1.1, hX.1.2.1,
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right t _) r48) (by decide), Nat.le_refl _, rc40,
    ⟨fun _ => Or.inr (Or.inr ⟨ne_loc hP h hKN1 rl ro (Nat.le_refl _), racc, r48, ral, rlv, rg.symm, rf.symm,
      apart_shrink hap h8,
      Loc.apart rl hk hoy.1 (fun _ => hoy.2.2.2), Loc.apart rl hk hxOE.1 (fun _ => hxOE.2.2.2),
      Loc.apart rl hk hogA.1 (fun _ => hogA.2.2.2)⟩), rwo⟩,
    ne_oe hP h hKN1 hogA, ⟨op, hone, hsa⟩, hstk.1, hstk.2.1, hstk.2.2.1, hstk.2.2.2.1, hstk.2.2.2.2.1,
    hstk.2.2.2.2.2.1, hstk.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.2.2.1,
    hstk.2.2.2.2.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.2.2.2.2.2, hs1, hs2, hs3, hs4,
    hbud, hob, h.inv, hxg⟩

end

end FvModexp.Amd64.ExpEven
