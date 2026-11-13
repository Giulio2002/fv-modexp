import FvModexp.Proofs.Arm64.NatQ.DivBasicRel

set_option autoImplicit false
/-! (Q-form copy of Arm64/Nat/DivBasicAddFin.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): the memory after `addVV` in the add-back (pure)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivBasic
open FvModexp.Arm64.DivBasic
variable {H : Nat}

@[reducible] def stA (M : Memory) (sp vl j uc up vp vc : Nat) : Memory :=
  (((((((((M.writeLE (sp - 72) 8 (vl + j)).writeLE (sp - 232) 8 (up + 8 * j)).writeLE (sp - 224) 8 vl).writeLE
    (sp - 216) 8 (uc - j)).writeLE (sp - 208) 8 (up + 8 * j)).writeLE (sp - 200) 8 vl).writeLE
    (sp - 192) 8 (uc - j)).writeLE (sp - 184) 8 vp).writeLE (sp - 176) 8 vl).writeLE (sp - 168) 8 vc

structure AddOut (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M w : Memory) (j : Nat) : Prop where
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 w
  rd : ∀ a n, (a + n ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 152 ≤ a) → (a + n ≤ s.sp.toNat - 72 ∨ s.sp.toNat - 64 ≤ a) →
    (a + n ≤ up + 8 * j ∨ up + 8 * j + 8 * vl ≤ a) → w.readLE a n = M.readLE a n
  jn : w.readLE (s.sp.toNat - 72) 8 = vl + j
  fr : MemFrame M w (scr s ++ [(up + 8 * j, up + 8 * j + 8 * vl)])
  val : natVal w (up + 8 * j) vl + 2 ^ (64 * vl) * w.readLE (s.sp.toNat - 160) 8 =
    natVal M (up + 8 * j) vl + natVal s.mem vp vl

set_option maxHeartbeats 4000000 in
theorem finA {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b H L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {M : Memory} (hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M) {j : Nat}
    (hj : j + vl ≤ ul) {w : Memory}
    (hFw : MemFrame (stA M s.sp.toNat vl j uc up vp vc) w
      [(up + 8 * j, up + 8 * j + 8 * vl), (s.sp.toNat - 160, s.sp.toNat - 152)])
    (hv1 : natVal w (up + 8 * j) vl = (M.readLE (up + 8 * j) (8 * vl) + M.readLE vp (8 * vl)) % 2 ^ (64 * vl))
    (hv2 : w.readLE (s.sp.toNat - 160) 8 = (M.readLE (up + 8 * j) (8 * vl) + M.readLE vp (8 * vl)) / 2 ^ (64 * vl)) :
    AddOut R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M w j := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2' := hl.v2; have hu48 := hl.u48; have huw := hl.uw
  have hulc := hE.pre.ulc; have hucB := hE.pre.ucb
  have hst : MemFrame M (stA M s.sp.toNat vl j uc up vp vc) [(s.sp.toNat - 232, s.sp.toNat - 160),
      (s.sp.toNat - 72, s.sp.toNat - 64)] := by
    unfold stA; janus_frame
  have hF0 := mfTrans hst hFw
  have hF : MemFrame M w (scr s ++ [(up + 8 * j, up + 8 * j + 8 * vl)]) := by
    refine hF0.mono fun a n ho => ?_
    simp only [scr, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hF' : MemFrame M w (scr s ++ wsL qp ql up ul vl t) := by
    refine hF.mono fun a n ho => ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho
    refine ⟨h1, h2, h3, h4, h5, h6, by omega⟩
  refine ⟨Mem.frame hE hM hF', fun a n h1 h2 h3 => hF0.readLE _ _ (by
    simp only [outside_append, outside_cons, outside_nil, and_true]; omega), ?_, hF, ?_⟩
  · rw [hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; unfold stA
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    omega
  · have hv : M.readLE vp (8 * vl) = natVal s.mem vp vl := hM.vs _ _ (Nat.le_refl _) (Nat.le_refl _)
    rw [hv1, hv2, hv]
    exact Nat.mod_add_div _ _

set_option maxHeartbeats 4000000 in
theorem finB {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b H L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {M w : Memory} {j : Nat} (hf : AddOut R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M w j)
    (hj : j + (vl + 1) ≤ ul) (v : Nat) :
    Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 (w.writeLE (up + (vl + j) * 8) 8 v) ∧
      (w.writeLE (up + (vl + j) * 8) 8 v).readLE (s.sp.toNat - 80) 8 = M.readLE (s.sp.toNat - 80) 8 ∧
      MemFrame M (w.writeLE (up + (vl + j) * 8) 8 v) (scr s ++ [(up + 8 * j, up + 8 * j + 8 * (vl + 1))]) ∧
      natVal (w.writeLE (up + (vl + j) * 8) 8 v) (up + 8 * j) vl = natVal w (up + 8 * j) vl ∧
      (w.writeLE (up + (vl + j) * 8) 8 v).readLE (up + 8 * j + 8 * vl) 8 = v % 2 ^ 64 := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hu48 := hl.u48; have huw := hl.uw
  have hst : MemFrame w (w.writeLE (up + (vl + j) * 8) 8 v) [(up + 8 * j + 8 * vl, up + 8 * j + 8 * vl + 8)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      exact Memory.readLE_writeLE_of_disjoint _ _ (by omega),
     fun a n w' => by simp only [Memory.accessible_writeLE]⟩
  have hF := mfTrans hf.fr hst
  have hF2 : MemFrame M (w.writeLE (up + (vl + j) * 8) 8 v) (scr s ++ [(up + 8 * j, up + 8 * j + 8 * (vl + 1))]) := by
    refine hF.mono fun a n ho => ?_
    simp only [scr, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ho
    exact ⟨h1, h2, h3, h4, h5, h6, by omega, by omega⟩
  have hF' : MemFrame M (w.writeLE (up + (vl + j) * 8) 8 v) (scr s ++ wsL qp ql up ul vl t) := by
    refine hF2.mono fun a n ho => ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho
    exact ⟨h1, h2, h3, h4, h5, h6, by omega⟩
  refine ⟨Mem.frame hE hf.mem ?_, ?_, hF2, ?_, ?_⟩
  · -- `Mem` of `w` → the store into `u`
    refine hst.mono fun a n ho => ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho
    omega
  · rw [hst.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hf.rd _ _ (by omega) (by omega) (by omega)
  · simp only [natVal]; exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · rw [show up + 8 * j + 8 * vl = up + (vl + j) * 8 by omega, Memory.readLE_writeLE_self]

end FvModexp.Arm64.Q.DivBasic
