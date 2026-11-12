import FvModexp.Proofs.Arm64.Exp.EvJ10
import FvModexp.Proofs.Arm64.Exp.EvPP

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `subMod2N`'s precondition `PreG` at `z1 = z1.subMod2N(z1, z2, n)` (agent infra)

`smZ`: the facts `PreG` asks of `z = z1` (window, guard word, `natOne`'s header and word), for a located `z1` or an
EMPTY one (`EL`: `nil` or an empty runtime slice). `natOne_win`: `natOne_at`'s callee form as `PreG`'s window form.
`smPre`: the whole `PreG` (args `z1, z1, z2, n`) at the callee entry (`SP = sp`, window `[sp - 4608, sp + 88)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

/-- `natOne_at`'s list (callee window split around the return slot `[sp - 8, sp + 8)`) gives the one-range window -/
theorem natOne_win {R : RtInv} {L : List (Nat × Nat)} {M : Memory} {op : Nat} {S : State} {stk above : Nat}
    {ws : List (Nat × Nat)} (h8 : 8 ≤ stk) (_h8' : 8 ≤ above)
    (h : NatOne R L M op (winA S stk above ++ ([(S.sp.toNat - 8, S.sp.toNat + 8)] ++ ws))) :
    NatOne R L M op (win S stk above) := by
  obtain ⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩ := h
  refine ⟨n0, n8, n16, nw, na, nrt, ?_, oa, o48, oh, ?_⟩
  · simp only [winA, win, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at nwin ⊢
    omega
  · simp only [winA, win, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at ow ⊢
    omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the facts of `z = z1` in `PreG` (slots 5, 6, 17, 18), located or empty -/
theorem smZ (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory} {L1 : List (Nat × Nat)}
    {pz lz cz v : Nat} (hz : LN R L s.mem st M L1 pz lz cz v) (he : EL R L pz cz) {op : Nat}
    (hone : NatOne R L s.mem op ([(sp - K, sp + 448), (zp, zp + 8 * zc)] ++ stkWs s.mem st))
    (hsa : StkApart s.mem st op 8) (hK : 4608 ≤ K) :
    Apart pz (8 * cz) natOneA 24 ∧ Apart pz (8 * cz) op 8 ∧ Outside pz (8 * cz) [(sp - 4608, sp + 88)] ∧
      Apart pz (8 * cz) (g + 16) 8 := by
  obtain ⟨-, -, -, -, -, nrt, nwin, -, -, oh, -⟩ := hone
  have hgo : Outside (g + 16) 8 ((sp - K, sp + 448) :: R.rt) := hP.1.2.2.2.2.2.1
  have hout := hP.win_rt
  rw [outside_cons] at hgo
  rcases Nat.eq_zero_or_pos cz with c0 | c0
  · subst c0
    have w := EL.out he hout
    unfold Apart at w
    refine ⟨EL.out he nrt, EL.apart he oh, ?_, EL.out he hgo.2⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  · have hloc := (hz.1.2.2 c0).1
    obtain ⟨w1, -, w3, -⟩ := Loc.ap hP hloc
    have hfA : stLen s.mem st < stCap s.mem st →
        Apart natOneA 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := by
      intro _
      simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at nwin
      unfold Apart; omega
    refine ⟨Loc.apart hloc c0 (Or.inr nrt) hfA, Loc.apart hloc c0 oh (hsa (by omega)).2, ?_, w3⟩
    unfold Apart at w1
    simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`PreG`** of `z1.subMod2N(z1, z2, n)` at the callee entry `S'` (`SP = sp`) -/
theorem smPre (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hK : 4608 ≤ K)
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {ra : Nat} (f30 : S'.regs 30 = BitVec.ofNat 64 ra) (hra : ra % 4 = 0 ∧ ra < 2 ^ 48)
    {pz lz cz v1 pw lw cw v2 n : Nat}
    (hz1 : LN R L s.mem st M L1 pz lz cz v1) (he : EL R L pz cz) (hpz : pz < 2 ^ 64)
    (hz2 : LN R L s.mem st M L1 pw lw cw v2) (hpw : pw < 2 ^ 64)
    (hwz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz))
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2 ^ 15) (hl1 : lz ≤ 2 ^ 12) (hl2 : lw ≤ 2 ^ 12)
    (hb : SubMod2N.costG n ≤ b1) :
    ∃ op, SubMod2N.PreG R b1 L1 op pz lz cz pw lw cw n S' := by
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hr30 : (S'.regs 30).toNat = ra := by
    rw [f30, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hra.2; omega)
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.2.2.1
  obtain ⟨op, hone, -, honeE, hsaE⟩ :=
    natOne_at hP hw hsN (stk := 4608) (above := 88) (lo := sp - 8) (hi := sp + 8) hK (by omega) (by omega) (by omega)
  rw [← hsN] at hone
  have hone' := natOne_win (by omega) (by omega) hone
  rw [← fm] at hone'
  obtain ⟨z5, z6, z17, z18⟩ := smZ hP hz1 he honeE hsaE hK
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := 4608) (above := 88) hK (Nat.le_refl _)
  obtain ⟨⟨c40, hlv, -⟩, hlc, -, hN1⟩ := hz1
  have w40 := hz2.1.1
  have hlc2 := hz2.2.1
  have hN2 := hz2.2.2.2
  have hrd : 0 < lw → ExpHyp.RdIn R L1 S' 4608 88 pw lw := fun h0 =>
    LN.rd hP hz2 (by omega) hsN fm hK (by omega)
  refine ⟨op, hce, hsv, hwT, hone', z5, z6, hn1, hn2, hlc, ⟨hpz, hpw⟩, c40, hl1, hlc2, w40, hl2,
    by rw [fm]; exact hlv, ?_, by rw [hgN]; exact z18, by rw [fm]; exact hN1,
    fun h0 => (hrd h0).2.1, fun h0 => (hrd h0).2.2.1, fun h0 => (hrd h0).2.2.2.1, fun h0 => (hrd h0).2.2.2.2,
    by rw [fm]; exact hN2, fun hz hy => (hwz (by omega) hz).symm,
    ⟨Nat.le_trans (SubMod2N.cost_le_costG n) hb, fun _ => hb⟩, by rw [hgN, fm]; exact hw.inv,
    by rw [hr30]; exact hra.1, by rw [hr30]; exact hra.2⟩
  simp only [win, hsN]; exact z17

end

end FvModexp.Arm64.ExpEven
