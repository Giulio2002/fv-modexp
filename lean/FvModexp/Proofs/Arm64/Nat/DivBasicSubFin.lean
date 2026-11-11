import FvModexp.Proofs.Arm64.Nat.DivBasicMul

/-!
# `divBasic` (arm64): the memory after `subVV` (pure)

`stS`: the stores between `+0x194` and the `CALL subVV.abi0` (`qhatv[n] = c`, `qhl`, `uc - j`, `&u[j]`, the ABI0
arguments); `finS`: everything the continuation needs about the memory `w` after the call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivBasic

@[reducible] def stS (M : Memory) (sp t vl j uc up c q : Nat) : Memory :=
  ((((((((((((M.writeLE (t + vl * 8) 8 c).writeLE (sp - 120) 8 q).writeLE
    (sp - 64) 8 (18446744073709551616 - j + uc)).writeLE (sp - 48) 8 (up + 8 * j)).writeLE
    (sp - 232) 8 (up + 8 * j)).writeLE (sp - 224) 8 q).writeLE (sp - 216) 8 (18446744073709551616 - j + uc)).writeLE
    (sp - 208) 8 (up + 8 * j)).writeLE (sp - 200) 8 q).writeLE (sp - 192) 8 (18446744073709551616 - j + uc)).writeLE
    (sp - 184) 8 t).writeLE (sp - 176) 8 q).writeLE (sp - 168) 8 (vl + 1)

structure SubOut (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M w : Memory) (j qhat c q Y : Nat) : Prop where
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 w
  jj : w.readLE (s.sp.toNat - 80) 8 = j
  qh : w.readLE (s.sp.toNat - 96) 8 = qhat
  ql : w.readLE (s.sp.toNat - 120) 8 = q
  uj : w.readLE (s.sp.toNat - 48) 8 = up + 8 * j
  cj : w.readLE (s.sp.toNat - 64) 8 = uc - j
  fr : MemFrame M w (scr s ++ [(t + 8 * vl, t + 8 * vl + 8), (up + 8 * j, up + 8 * j + 8 * q)])
  tc : w.readLE (t + 8 * vl) 8 = c
  ty : natVal w t q = Y

set_option maxHeartbeats 4000000 in
theorem finS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {M : Memory} (hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M) {j qhat c q : Nat}
    (hjj : M.readLE (s.sp.toNat - 80) 8 = j) (hqh : M.readLE (s.sp.toNat - 96) 8 = qhat)
    (hj : j + q ≤ ul) (hq : q = vl ∨ q = vl + 1) (hc : c < 2 ^ 64) (hjc : j ≤ uc) (huc : uc < 2 ^ 40)
    {w : Memory} (hFw : MemFrame (stS M s.sp.toNat t vl j uc up c q) w
      [(up + 8 * j, up + 8 * j + 8 * q), (s.sp.toNat - 160, s.sp.toNat - 152)]) :
    SubOut R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M w j qhat c q
      ((M.writeLE (t + vl * 8) 8 c).readLE t (8 * q)) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have ht48 := hl.t48; have hu48 := hl.u48
  have htw := hl.tw; have huw := hl.uw; have htu := hl.tu
  have hst : MemFrame M (stS M s.sp.toNat t vl j uc up c q) [(t + vl * 8, t + vl * 8 + 8),
      (s.sp.toNat - 232, s.sp.toNat - 160), (s.sp.toNat - 120, s.sp.toNat - 112), (s.sp.toNat - 64, s.sp.toNat - 56),
      (s.sp.toNat - 48, s.sp.toNat - 40)] := by
    unfold stS; janus_frame
  have hF0 := mfTrans hst hFw
  have hF : MemFrame M w (scr s ++ [(t + 8 * vl, t + 8 * vl + 8), (up + 8 * j, up + 8 * j + 8 * q)]) := by
    refine hF0.mono fun a n ho => ?_
    simp only [scr, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hF' : MemFrame M w (scr s ++ wsL qp ql up ul vl t) := by
    refine hF.mono fun a n ho => ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho
    refine ⟨h1, h2, h3, h4, h5, h6, by omega, by omega⟩
  have rw1 : ∀ a, (a + 8 ≤ up + 8 * j ∨ up + 8 * j + 8 * q ≤ a) → (a + 8 ≤ s.sp.toNat - 160 ∨ s.sp.toNat - 152 ≤ a) →
      w.readLE a 8 = (stS M s.sp.toNat t vl j uc up c q).readLE a 8 := fun a h1 h2 =>
    hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨Mem.frame hE hM hF', ?_, ?_, ?_, ?_, ?_, hF, ?_, ?_⟩
  · rw [hF0.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; omega)]; exact hjj
  · rw [hF0.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; omega)]; exact hqh
  · rw [rw1 _ (by omega) (by omega)]; unfold stS
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    omega
  · rw [rw1 _ (by omega) (by omega)]; unfold stS
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    omega
  · rw [rw1 _ (by omega) (by omega)]; unfold stS
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    omega
  · rw [rw1 _ (by omega) (by omega), show t + 8 * vl = t + vl * 8 by omega]; unfold stS
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    omega
  · simp only [natVal]
    rw [hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    unfold stS
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]

end FvModexp.Arm64.DivBasic
