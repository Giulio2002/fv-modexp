import FvModexp.Proofs.Amd64.Exp.EvJ10

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `subMod2N`'s precondition `PreG` at `z1 = z1.subMod2N(z1, z2, n)` (asm s62; twin of
infra's arm64 `EvSmP`)

`smZ`: the facts `PreG` asks of `z = z1` (window, guard word, TLS slot, `natOne`'s header and word), for a located `z1`
or an EMPTY one (`EL`). `natOne_win`: `natOne_at`'s list form as `PreG`'s window form. `smPre`: the whole `PreG`
(args `z1, z1, z2, n`) at the callee entry (`RSP = sp - 8`, window `[sp - 8 - 4576, sp - 8 + 88)`, `n` at `[sp]`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp

/-- `NatOne` over a longer window list gives it over the first part -/
theorem natOne_win {R : RtInv} {L : List (Nat × Nat)} {M : Memory} {op : Nat} {w ws : List (Nat × Nat)}
    (h : NatOne R L M op (w ++ ws)) : NatOne R L M op w := by
  obtain ⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩ := h
  rw [outside_append] at nwin ow
  exact ⟨n0, n8, n16, nw, na, nrt, nwin.1, oa, o48, oh, ow.1⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the facts of `z = z1` in `PreG` (slots 5, 6, 17, 18 and `Ent`'s TLS apartness), located or empty -/
theorem smZ (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {pz lz cz v : Nat} (hz : LN R L s.mem st M L1 pz lz cz v) (he : EL R L pz cz) {op : Nat}
    (hone : NatOne R L s.mem op ([(sp - 8 - K, sp + wTop), (zp, zp + 8 * zc)] ++ stkWs s.mem st))
    (hsa : NHyp.StkApart s.mem st op 8) (hK : 4576 ≤ K) :
    Apart pz (8 * cz) natOneA 24 ∧ Apart pz (8 * cz) op 8 ∧ Outside pz (8 * cz) [(sp - 8 - 4576, sp - 8 + 88)] ∧
      Apart pz (8 * cz) (g + 16) 8 ∧ Apart pz (8 * cz) (fs - 8) 8 := by
  obtain ⟨-, -, -, -, -, nrt, nwin, -, -, oh, -⟩ := hone
  have hc := hP.cenv0
  have hgo : Outside (g + 16) 8 R.rt := hc.2.2.2.2.2.2.2.2.2.1
  have hfo : Outside (fs - 8) 8 R.rt := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  rcases Nat.eq_zero_or_pos cz with c0 | c0
  · subst c0
    have w := EL.out he hout
    unfold Apart at w
    refine ⟨EL.out he nrt, EL.apart he oh, ?_, EL.out he hgo, EL.out he hfo⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  · have hloc := (hz.1.2.2 c0).1
    obtain ⟨w1, -, w3, w4, -⟩ := Loc.ap hP hloc
    have hfA : stLen s.mem st < stCap s.mem st →
        Apart natOneA 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := by
      intro _
      simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at nwin
      unfold Apart; omega
    refine ⟨Loc.apart hloc c0 (Or.inr nrt) hfA, Loc.apart hloc c0 oh (hsa (by omega)).2, ?_, w3, w4⟩
    unfold Apart at w1
    simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`PreG`** of `z1.subMod2N(z1, z2, n)` at the callee entry `S'` (`RSP = sp - 8`) -/
theorem smPre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hK : 4576 ≤ K)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M) (fx : S'.xmm 15 = 0) (fd : S'.df = false) (frd : M.readLE (sp - 8) 8 < 2 ^ 47)
    {pz lz cz v1 pw lw cw v2 n : Nat} (fn : M.readLE sp 8 = n)
    (hz1 : LN R L s.mem st M L1 pz lz cz v1) (he : EL R L pz cz) (hpz : pz < 2 ^ 64)
    (hz2 : LN R L s.mem st M L1 pw lw cw v2) (hpw : pw < 2 ^ 64)
    (hwz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz))
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2 ^ 15) (hl1 : lz ≤ 2 ^ 12) (hl2 : lw ≤ 2 ^ 12)
    (hb : SubMod2N.costG n ≤ b1) :
    ∃ op, SubMod2N.PreG R b1 L1 op pz lz cz pw lw cw n S' := by
  have hk := hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.1
  obtain ⟨op, hone, -, honeE, hsaE⟩ :=
    natOne_at hP hw (stk := 4576) (above := 88) (lo := sp) (hi := sp) hK (by omega) (by omega) (by omega)
  have hone' : NatOne R L1 S'.mem op (win S' SubMod2N.K SubMod2N.A) := by
    simp only [win, tsp, fm, SubMod2N.K, SubMod2N.A]; exact natOne_win hone
  obtain ⟨z5, z6, z17, z18, zf⟩ := smZ hP hz1 he honeE hsaE hK
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := 4576) (above := 88) hK (by omega) (by omega)
  obtain ⟨⟨c40, hlv, -⟩, hlc, -, hN1⟩ := hz1
  have w40 := hz2.1.1
  have hlc2 := hz2.2.1
  have hN2 := hz2.2.2.2
  have hrd : 0 < lw → RdIn R L1 S' 4576 88 pw lw := fun h0 =>
    LN.rd hP hz2 (by omega) tsp fm hK (by omega)
  refine ⟨op, hce, hsv, hwT, hone', z5, z6, hn1, hn2, hlc, ⟨hpz, hpw⟩, c40, hl1, hlc2, w40, hl2,
    by rw [fm]; exact hlv, ?_, by rw [tg]; exact z18, by rw [fm]; exact hN1,
    fun h0 => (hrd h0).2.1, fun h0 => (hrd h0).2.2.1, fun h0 => (hrd h0).2.2.2.1, fun h0 => (hrd h0).2.2.2.2,
    by rw [fm]; exact hN2, fun hz hy => (hwz (by omega) hz).symm,
    ⟨Nat.le_trans (SubMod2N.cost_le_costG n) hb, fun _ => hb⟩, by rw [tg, fm]; exact hw.inv,
    by rw [tfs]; exact zf, by rw [tsp, fm]; exact frd, ?_, fx, fd⟩
  · simp only [win, tsp, SubMod2N.K, SubMod2N.A]; exact z17
  · rw [tsp, fm, show sp - 8 + 8 = sp by omega]; exact fn

end

end FvModexp.Amd64.ExpEven
