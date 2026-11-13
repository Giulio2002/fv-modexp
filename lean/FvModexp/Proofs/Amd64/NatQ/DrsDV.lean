import FvModexp.Proofs.Amd64.NatQ.DrsDefs
import FvModexp.Proofs.Amd64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Amd64.NatQ.DrsCE
import FvModexp.Proofs.Amd64.NatQ.DrsPathB

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsDV.lean; Q-form copy of Arm64/Nat/DrsDV.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), after the correction loop: the model of one wide-digit step (pure)

natdiv.go:844-853: `if qhatv.cmp(uu.norm()) > 0 { panic("impossible") }; c := subVV(uu[:len(qhatv)], uu[:len(qhatv)],
qhatv); if c > 0 { subVW(uu[len(qhatv):], uu[len(qhatv):], c) }; addTo(z[j-B:], qhat); j -= B; stk.restore(mark)`.

* `Cx.stF`: the model state at the loop exit (`E`); `blockM_eq`: `Mdl.blockM` (the model of the whole step, with the ideal
  recursion `recI` and product `mulI`) in terms of `stF` (the `uu` it refines is the memory's `uu`, via `drop_upd_of_le`).
* `Cx.BS`: `Mdl.blockStep` = the quotient / dividend after the step; `bstep`: `Mdl.blockStep_spec` instantiated from `Cr`
  and the loop invariant (`room`: the size facts from `DrsPreW`); `e_le` (the `panic("impossible")` is unreachable),
  `li_next` (the invariant at `j - B`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Mdl

theorem take_upd_of_le (z l : List Nat) (i k : Nat) (hk : k ≤ i) (hi : i ≤ z.length) :
    (upd z i l).take k = z.take k := by
  unfold upd
  rw [List.append_assoc, List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left hk]

theorem drop_upd_of_le (z l : List Nat) (i k : Nat) (hk : k ≤ i) (hi : i ≤ z.length) :
    (upd z i l).drop k = upd (z.drop k) (i - k) l := by
  unfold upd
  rw [List.append_assoc, List.drop_append_of_le_length (by simp; omega), List.drop_take, List.drop_drop,
    List.append_assoc]
  congr 3; omega

end FvModexp.Mdl

namespace FvModexp.Amd64.Q.DivRec


open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the model state at the exit of the correction loop -/
@[reducible] def Cx.stF (c : Cx) (s : State) (j : Nat) (U : List Nat) : Mdl.St :=
  Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U)

/-- `uu -= qhatv` (with the borrow into `uu[len(qhatv):]`) at the loop exit -/
@[reducible] def Cx.sT (c : Cx) (s : State) (j : Nat) (U : List Nat) : List Nat × Nat :=
  Mdl.subToC (c.stF s j U).w ((c.stF s j U).buf.take (c.P s j U).length)

/-- one step of the wide-digit loop (model): the quotient and the dividend after the iteration `j` -/
@[reducible] def Cx.BS (c : Cx) (s : State) (j : Nat) (Z U : List Nat) : List Nat × List Nat :=
  Mdl.blockStep Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) j Z U

theorem blockM_eq {c : Cx} {s : State} {j : Nat} {U : List Nat} (hB : 1 ≤ c.vl / 2) (hj : c.vl / 2 ≤ j)
    (hjU : j - 1 ≤ U.length) :
    Mdl.blockM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) j U =
      { q := (c.stF s j U).qhat, w := (c.sT s j U).1, c := (c.sT s j U).2,
        e := Mdl.cmpQ (c.P s j U).length (c.stF s j U) } := by
  have e : (c.U2 s j U).drop (j - c.vl / 2) = Mdl.upd (U.drop (j - c.vl / 2)) (c.vl / 2 - 1) (c.R s j U).2 := by
    simp only [Cx.U2]
    rw [Mdl.drop_upd_of_le _ _ _ _ (by omega) hjU, show j - 1 - (j - c.vl / 2) = c.vl / 2 - 1 by omega]
  simp only [Cx.stF, Cx.sT, Cx.st0, e]
  rfl

theorem topV {R : RtInv} {c : Cx} {s : State} (hcr : Cr R c s) : 2 ^ 63 ≤ Mdl.topLimb (c.V s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hv2, -, htop, -⟩ := hcr.pre
  unfold Mdl.topLimb
  rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega)]
  exact htop

/-- the size facts of the loop (from `DrsPreW`) -/
theorem room {R : RtInv} {c : Cx} {s : State} (hcr : Cr R c s) :
    c.u1 - c.vl ≤ c.ql ∧ natVal s.mem c.up c.u1 < Mdl.val (c.V s) * 2 ^ (64 * c.ql) ∧
      2 * natVal s.mem c.up c.u1 < 2 ^ (64 * (c.vl + c.ql)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hv2, -, htop, -, hU2, -⟩ := hcr.pre
  have hV := v_geB (M := s.mem) (vp := c.vp) (vl := c.vl) (by omega) htop
  have hvV : Mdl.val (c.V s) = natVal s.mem c.vp c.vl := Asm.val_limbs _ _ _
  have hU := hcr.hU
  have hroom := room_drsB (U := natVal s.mem c.up c.ul) (V := natVal s.mem c.vp c.vl) (ul := c.u1) (vl := c.vl)
    (ql := c.ql) (by omega) hV hU2 (by
      rcases Nat.eq_zero_or_pos c.u1 with h0 | h0
      · exact Or.inl h0
      rcases hcr.hN with h | h
      · exact Or.inl h
      · right; rw [← hU]; exact natVal_ge _ _ _ h0 h)
  have e : 2 ^ (64 * (c.vl + c.ql)) = 2 * (2 ^ (64 * (c.vl - 1)) * 2 ^ 63 * 2 ^ (64 * c.ql)) := by
    rw [show 64 * (c.vl + c.ql) = 1 + (64 * (c.vl - 1) + 63 + 64 * c.ql) by omega, Nat.pow_add, Nat.pow_add,
      Nat.pow_add, Nat.pow_one]
  have hlt : natVal s.mem c.up c.ul < natVal s.mem c.vp c.vl * 2 ^ (64 * c.ql) :=
    Nat.lt_of_lt_of_le (by rw [e] at hU2; omega) (Nat.mul_le_mul_right _ hV)
  refine ⟨by have := hcr.vu1; omega, by rw [hvV, hU]; exact hlt, by rw [hU]; exact hU2⟩

/-- `Mdl.blockStep_spec` for the iteration `j` -/
theorem bstep {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : c.vl / 2 < j) :
    (c.BS s j Z U).1.length = c.ql ∧ (c.BS s j Z U).2.length = c.u1 - c.vl + c.vl ∧
    Mdl.Wd (c.BS s j Z U).1 ∧ Mdl.Wd (c.BS s j Z U).2 ∧
    Mdl.val (c.BS s j Z U).2 + Mdl.val (c.V s) * Mdl.val (c.BS s j Z U).1 = natVal s.mem c.up c.u1 ∧
    Mdl.val (c.BS s j Z U).2 < Mdl.val (c.V s) * 2 ^ (64 * (j - c.vl / 2)) ∧
    (Mdl.blockM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) j U).c = 0 ∧
    (Mdl.blockM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) j U).e ≤ 0 ∧
    (Mdl.norm (Mdl.blockR Mdl.recI (c.V s) c.vl (c.vl / 2) j U).1).length + (c.vl / 2 - 1) ≤ 3 * c.vl ∧
    (Mdl.blockM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) j U).q.length ≤ c.ql - (j - c.vl / 2) := by
  obtain ⟨hz, hu, hzl, hul, hval, hbd, htail, hj⟩ := hli
  obtain ⟨r1, r2, r3⟩ := room hcr
  have h40 := hcr.h40
  exact Mdl.blockStep_spec Mdl.recI c.vl (Mdl.recI_ok _) Mdl.mulI Mdl.mulI_ok (c.V s) c.vl (c.vl / 2) j (c.u1 - c.vl)
    c.ql (natVal s.mem c.up c.u1) Z U (Asm.Wd_limbs _ _ _) (Asm.length_limbs _ _ _) (topV hcr) (by omega) (by omega)
    (by omega) hz hu hzl hul hval hbd htail hj hjB r1 r2 r3

/-- the `panic("impossible")` after the correction loop is unreachable -/
theorem e_le {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : c.vl / 2 < j) : Mdl.cmpQ (c.P s j U).length (c.stF s j U) ≤ 0 := by
  have h := (bstep hcr hli hjB).2.2.2.2.2.2.2.1
  have hul := hli.2.2.2.1
  have hvu := hcr.vu1
  have hjj := hli.2.2.2.2.2.2.2
  rw [blockM_eq (by have := hcr.h40; omega) (by omega) (by omega)] at h
  exact h

/-- the quotient and dividend after the step, in terms of the loop's model state -/
theorem bs_eq {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : c.vl / 2 < j) :
    (c.BS s j Z U).1 = Mdl.upd Z (j - c.vl / 2) (Mdl.addTo (Z.drop (j - c.vl / 2)) (c.stF s j U).qhat) ∧
    (c.BS s j Z U).2 = Mdl.upd U (j - c.vl / 2) (c.sT s j U).1 := by
  have hul := hli.2.2.2.1
  have hvu := hcr.vu1
  have hjj := hli.2.2.2.2.2.2.2
  have e := blockM_eq (c := c) (s := s) (j := j) (U := U) (by have := hcr.h40; omega) (by omega) (by omega)
  simp only [Cx.BS, Mdl.blockStep, e]
  constructor <;> first | trivial | rfl

/-- the quotient digit fits `z[j-B:]` -/
theorem q_fit {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : c.vl / 2 < j) : (c.stF s j U).qhat.length ≤ c.ql - (j - c.vl / 2) := by
  have h := (bstep hcr hli hjB).2.2.2.2.2.2.2.2.2
  have hul := hli.2.2.2.1
  have hvu := hcr.vu1
  have hjj := hli.2.2.2.2.2.2.2
  rw [blockM_eq (by have := hcr.h40; omega) (by omega) (by omega)] at h
  exact h

/-- the loop invariant after the step -/
theorem li_next {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : c.vl / 2 < j) : c.LI s (j - c.vl / 2) (c.BS s j Z U).1 (c.BS s j Z U).2 := by
  obtain ⟨s1, s2, s3, s4, s5, s6, -⟩ := bstep hcr hli hjB
  have hj := hli.2.2.2.2.2.2.2
  have hv := Asm.Wd_limbs s.mem c.vp c.vl
  have hvlt : Mdl.val (c.V s) < 2 ^ (64 * c.vl) := by
    have := Mdl.val_lt hv; rwa [Asm.length_limbs] at this
  refine ⟨s3, s4, s1, s2, s5, ?_, ?_, by omega⟩
  · exact Nat.lt_of_lt_of_le s6 (Nat.mul_le_mul_left _ (Mdl.pow_le_pow_64 (by omega)))
  · refine Mdl.zero_drop_of_lt s4 ?_
    have : Mdl.val (c.V s) * 2 ^ (64 * (j - c.vl / 2)) ≤ 2 ^ (64 * c.vl) * 2 ^ (64 * (j - c.vl / 2)) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hvlt)
    rw [← Mdl.pow64_add, Nat.add_comm] at this
    exact Nat.lt_of_lt_of_le s6 this

end FvModexp.Amd64.Q.DivRec
