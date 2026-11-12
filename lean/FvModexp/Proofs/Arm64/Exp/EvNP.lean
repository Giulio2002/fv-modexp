import FvModexp.Proofs.Arm64.Exp.EvJ
import FvModexp.Proofs.Arm64.Exp.EvPP
import FvModexp.Proofs.Arm64.Exp.NDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `nat.expNN`'s precondition `NPre` at the two recursive calls (agent infra)

At a call `z.expNN(stk, x, y, mm, false)` with `SP = sp` (callee `sp_N = sp - 1312`, window
`[sp - 1312 - KN, sp + 120)` inside ours), `x`, `y` the entry operands, `mm = (pm, lm, cm)` a live local nat and the
destination `z = (r, k, k)` a scratch destination apart from `mm`: `npre_of` builds `ExpN.NPre` from `EPre`, the context
`WC` and the locals; the stack-size bounds, the budget and `KN` are the caller's hypotheses.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp (natOneA)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- an entry object as `nat.expNN`'s `NE` (window `[sp - 1312 - KN, sp + 120)`) -/
theorem ne_oe (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN : KN + 1312 ≤ K) {a k : Nat}
    (hoe : OE R L sp K st s.mem a k) : ExpN.NE R L1 (sp - 1312) KN st M a k := by
  have hlc := h.sok.2.2.2.2.2.1
  have hf := obj_free hoe h.kf (by rw [h.len]; exact h.lo) hlc
  obtain ⟨o1, o2, o3, -⟩ := hoe
  refine ⟨h.le.held o1, ?_, o3, hf⟩
  unfold Apart at o2 ⊢; omega

/-- a located local array (a part `[t, t + n)` of it) as `NE` -/
theorem ne_loc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN : KN + 1312 ≤ K) {t k n : Nat}
    (hl : Loc R L s.mem st t k) (ho : Ob R L1 st M t k) (hn : n ≤ 8 * k) : ExpN.NE R L1 (sp - 1312) KN st M t n := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨w1, w2, -, -⟩ := Loc.ap hP hl
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
/-- `natOne` at `M`, outside `[lo, hi)` (inside the window), a located array `(t, k)` and the stack's writable ranges -/
theorem natOne_loc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {lo hi t k : Nat} (hlo : sp - K ≤ lo) (hhi : hi ≤ sp + 448)
    (hl : Loc R L s.mem st t k) :
    ∃ op, EvenHyp.NatOne R L1 M op ([(lo, hi), (t, t + 8 * k)] ++ stkWs M st) ∧ EvenHyp.StkApart M st op 8 := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hlc := h.lc0
  obtain ⟨op, hone, hsa⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hone' := hone
  obtain ⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩ := hone'
  have bA := out_bytes nwin
  have bO := out_bytes ow
  have hrd : ∀ j, j + 8 ≤ 24 → M.readLE (natOneA + j) 8 = s.mem.readLE (natOneA + j) 8 := fun j hj =>
    h.readB (Or.inr (nrt.of_sub (by omega) (by omega))) fun i hi => by
      have := bA (j + i) (by omega); rwa [← Nat.add_assoc] at this
  have hO : M.readLE op 8 = s.mem.readLE op 8 := h.readB oh bO
  have sA : Outside natOneA 24 (stkWs M st) :=
    stk_out h (Or.inr nrt) (by simp only [ZS, List.cons_append, List.nil_append, outside_cons, outside_append] at nwin ⊢; exact nwin.2)
  have sO : Outside op 8 (stkWs M st) :=
    stk_out h oh (by simp only [ZS, List.cons_append, List.nil_append, outside_cons, outside_append] at ow ⊢; exact ow.2)
  have tA : Outside natOneA 24 [(t, t + 8 * k)] :=
    Loc.out hl (Or.inr nrt) (by rw [List.cons_append, List.cons_append, outside_cons, outside_cons] at nwin; exact nwin.2.2)
  have tO : Outside op 8 [(t, t + 8 * k)] :=
    Loc.out hl oh (by rw [List.cons_append, List.cons_append, outside_cons, outside_cons] at ow; exact ow.2.2)
  refine ⟨op, ⟨by rw [show natOneA = natOneA + 0 from rfl, hrd 0 (by omega)]; exact n0, by rw [hrd 8 (by omega)]; exact n8,
    by rw [hrd 16 (by omega)]; exact n16, by rw [hO]; exact nw, by rw [h.fr.accessible]; exact na, nrt, ?_,
    by rw [h.fr.accessible]; exact oa, o48, h.le.held oh, ?_⟩, fun _ => ⟨?_, fun _ => ?_⟩⟩
  · simp only [outside_cons, outside_nil, and_true] at tA
    rw [List.cons_append, List.cons_append, outside_cons, outside_cons]
    refine ⟨?_, tA, sA⟩
    simp only [List.cons_append, outside_append, outside_cons, outside_nil, and_true] at nwin; omega
  · simp only [outside_cons, outside_nil, and_true] at tO
    rw [List.cons_append, List.cons_append, outside_cons, outside_cons]
    refine ⟨?_, tO, sO⟩
    simp only [List.cons_append, outside_append, outside_cons, outside_nil, and_true] at ow; omega
  · simp only [stkWs, outside_cons, outside_append] at sO; unfold Apart; omega
  · refine free_apart h oh ?_
    simp only [free, stkWs, List.cons_append, List.nil_append, outside_cons, outside_append, outside_nil, and_true] at ow ⊢
    unfold Apart; omega

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

theorem apart_shrink {a k b n n' : Nat} (h : Apart a k b n) (hn : n' ≤ n) : Apart a k b n' := by
  unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
/-- `nat.expNN`'s call environment (window `[sp - 1312 - KN, sp + 120)`) -/
theorem nenv_of (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S : State} (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (hm : S.mem = M) {KN : Nat} (hKN : 4304 ≤ KN) (hKN1 : KN + 1312 ≤ K) :
    ExpN.NEnv R L1 g (sp - 1312) KN S := by
  have hgM : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := MemFrame.bytewise h.fr hP.g_out
  have hws := hP.ws_acc
  have hout := hP.win_rt
  obtain ⟨⟨-, -, hg1, hg2, hg3, hgo, hal, -, hKsp, hsp2, hacc0, hLr, hLs, hd0, hsv⟩, -, -, hro, -⟩ := hP
  simp only [outside_cons] at hgo
  subst hm
  refine ⟨?_, h28, hg1, by rw [h.fr.accessible]; exact hg2, by rw [hgM]; omega, ⟨by omega, hgo.2⟩, by omega, hKN,
    by omega, by omega, by rw [h.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega),
    LiveSep.sub_win_rt hLr (by omega) (by omega) (by omega), ?_,
    dataLoaded_frame hd0 h.rg hro (by rw [← List.append_assoc]; exact h.fr) hws, hsv⟩
  · rw [hsp]; congr 1; omega
  · refine h.le.liveSep (LiveSep.sub_win hLs (by omega) (by omega)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- `nat.expNN`'s stack facts -/
theorem nstk_of (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {KN : Nat} (hKN1 : KN + 1312 ≤ K) :
    0 < st ∧ st < 2 ^ 48 ∧ StkOK M R L1 st ∧ Apart st 24 (sp - 1312 - KN) (KN + 1432) ∧ Apart st 24 (g + 16) 8 ∧
    (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 1312 - KN) (KN + 1432) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
    (stCap M st = 0 → stW M st = 0) ∧
    M.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
    Apart st 24 (W4En.free M st).1 (W4En.free M st).2 ∧
    Apart (W4En.free M st).1 (W4En.free M st).2 RunIface.gA 32 := by
  have hout := hP.win_rt
  have hc0 := WC.cap0 hP h
  have hsF := free_apart h hP.stk0.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨-, -, -, -, -, hgo, -, -, hK, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hogA, hsok, hstw, hstg, harr, hwbacc, hstwb, -, hst0, -⟩ := hP
  have hgF := (free_apart h hogA.1 hogA.2.2.2).symm
  simp only [outside_cons] at hgo
  refine ⟨Nat.pos_of_ne_zero hst0, by have := hsok.2.2.2.1; omega, h.sok, ?_, hstg, ?_, hc0,
    by rw [h.fr.accessible]; exact hwbacc, hstwb, hsF, hgF⟩
  · unfold Apart at hstw ⊢; omega
  · intro hc
    rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc; rw [e1, e2]
      obtain ⟨o1, o2⟩ := harr hc
      unfold Apart at o1 ⊢
      exact ⟨by omega, o2⟩
    · have a1 := hin.apart hout
      have a2 := hin.apart hgo.2
      unfold Apart at a1 a2 ⊢
      omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`ExpN.NPre` at a recursive call** (see the module doc) -/
theorem npre_of (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S : State} (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (hm : S.mem = M)
    {KN : Nat} (hKN : 4304 ≤ KN) (hKN1 : KN + 1312 ≤ K) (hKN2 : KN + 288 ≤ 2 ^ 20)
    {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {pm lm cm v r k : Nat} (hmm : LN R L s.mem st M L1 pm lm cm v) (hl0 : 0 < lm) (hl128 : lm ≤ 128)
    (hd : DL R L s.mem st M L1 r k) (hk : 0 < k) (hap : Apart r (8 * k) pm (8 * cm))
    (hs1 : stLen M st + StackNat.rnd (23 * lm) + StackNat.rnd (xl - lm + 1) + StackNat.rnd lm + 16 * xl +
      StackNat.rnd lm + 2 * StackNat.rnd (2 * lm) + 32 * lm + 80 ≤ 2 ^ 16)
    (hs2 : stLen M st + needR xl lm ≤ 2 ^ 16) (hs3 : stLen M st + needS xl yl lm ≤ 2 ^ 16)
    (hs4 : stLen M st + needP xl yl (Nat.log2 (natVal M pm lm)) ≤ 2 ^ 16)
    (hbud : makeCost 1 + makeCost lm + costR (stLen M st) xl lm + costS (stLen M st) xl yl lm +
      costP (stLen M st) xl yl (Nat.log2 (natVal M pm lm)) + ExpOdd.OBud costF lm xl yl (stLen M st) ≤ b1) :
    ExpN.NPre R b1 L1 KN costF needR costR needS needP costS costP g (sp - 1312) r k k st xp xl xc yp yl yc pm lm cm 0
      S := by
  have hsN : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgl := h.globals hP (w := [(sp - 1312 - KN, sp - 1312 + 1432)]) (fun a n ho => by
    have := hP.1.2.2.2.2.2.2.2.2.1
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)
  obtain ⟨op, hone, hsa⟩ := natOne_loc hP h (lo := sp - 1312 - KN) (hi := sp - 1312 + 1432)
    (by have := hP.1.2.2.2.2.2.2.2.2.1; omega) (by have := hP.1.2.2.2.2.2.2.2.2.1; omega) (hd.2.2 hk).1
  have hne := nenv_of hP h hsp h28 hm hKN hKN1
  have hstk := nstk_of hP h hKN1
  obtain ⟨⟨c40, hlv, hlo⟩, hlc', -, hmN⟩ := hmm
  have hcm : 0 < cm := Nat.lt_of_lt_of_le hl0 hlc'
  obtain ⟨-, -, macc, m48⟩ := hlv hcm
  have h8 : 8 * lm ≤ 8 * cm := Nat.mul_le_mul_left 8 hlc'
  obtain ⟨rc40, rlv, rlo⟩ := hd
  obtain ⟨ral, -, racc, r48⟩ := rlv hk
  obtain ⟨rl, ro⟩ := rlo hk
  obtain ⟨rw1, -, rg, -⟩ := Loc.ap hP rl
  have rwo : Outside r (8 * k) [(sp - 1312 - KN, sp - 1312 + 1432)] := by
    have := hP.1.2.2.2.2.2.2.2.2.1
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at rw1; omega
  have hP' := hP
  obtain ⟨-, -, -, hro, hwT, -, -, hoy, hay, hy48, hyN, -, hyl, hox, hax, hx48, hxN, hxl, hxp, hxc, -, -, hz,
    hogA, -, -, -, -, -, -, -, -, -, -, hmo, -⟩ := hP'
  have hzy : 0 < zc → Apart zp (8 * zc) yp (8 * yl) := fun h0 => (hz h0).2.2.2.2.2.2.1
  have hzx : 0 < zc → Apart zp (8 * zc) xp (8 * xl) := fun h0 => (hz h0).2.2.2.2.2.1
  subst hm
  obtain ⟨-, yN, -, -⟩ := obj_at hP h hoy hay hy48 hyN (Nat.le_trans hyl (by decide)) hzy hsN rfl (stk := 0)
    (above := 0) (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨-, xN, -, -⟩ := obj_at hP h hox hax hx48 hxN (Nat.le_trans hxl (by decide)) hzx hsN rfl (stk := 0)
    (above := 0) (Nat.zero_le _) (Nat.zero_le _)
  exact ⟨hne, hKN2, hgl, hro, hwT, rfl, hl0, hl128, hlc', c40,
    ne_loc hP h hKN1 (hlo hcm).1 (hlo hcm).2 h8,
    Memory.accessible_weaken _ (Memory.accessible_mono _ macc (Nat.le_refl _) (Nat.add_le_add_left h8 pm)),
    Nat.le_trans (Nat.add_le_add_left h8 pm) m48, hmN,
    ne_oe h hKN1 hoy, by rw [h.fr.accessible]; exact hay, hy48, yN, hyl, hmo.2.2.2.2.2.2.1,
    ne_oe h hKN1 hox, by rw [h.fr.accessible]; exact hax, hx48, xN, hxl, hxp, hxc,
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right r _) r48) (by decide), Nat.le_refl _, rc40,
    ⟨fun _ => Or.inr (Or.inr ⟨ne_loc hP h hKN1 rl ro (Nat.le_refl _), racc, r48, ral, rlv, rg.symm,
      apart_shrink hap h8,
      Loc.apart rl hk hoy.1 (fun _ => hoy.2.2.2), Loc.apart rl hk hox.1 (fun _ => hox.2.2.2),
      Loc.apart rl hk hogA.1 (fun _ => hogA.2.2.2)⟩), rwo⟩,
    ne_oe h hKN1 hogA, ⟨op, hone, hsa⟩, hstk.1, hstk.2.1, hstk.2.2.1, hstk.2.2.2.1, hstk.2.2.2.2.1,
    hstk.2.2.2.2.2.1, hstk.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.2.1, hstk.2.2.2.2.2.2.2.2.2.1,
    hstk.2.2.2.2.2.2.2.2.2.2, hs1, hs2, hs3, hs4, hbud, h.inv⟩

end

end FvModexp.Arm64.ExpEven
