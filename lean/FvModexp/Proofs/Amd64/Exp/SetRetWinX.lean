import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.SetRetWin

set_option autoImplicit false

/-!
# Frame lemmas for installing the return address: the exp-chain callee preconditions (amd64; top s54)

`SetRetWin` lifted to the shared parts of the `nat.expNN` callees' preconditions: the threshold globals (`globals`), the
stack header and its free part (`stHdr`, `stkOK`, `freeOf_eq`), the common entry facts `NHyp.CPre` (`cpre`), and the
`natOne` facts under their `∃ op` (`natOne`). Each is a composition of `rd` steps; no closer tactic runs on a large context.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.SetRetWin

theorem globals {R : RtInv} {s : State} {ret stk above : Nat} (hab : 8 ≤ above)
    (h : RunIface.Globals R s.mem (win s stk above)) : RunIface.Globals R (s.setRet ret).mem (win s stk above) := by
  obtain ⟨g1, g2, g3, g4, e1, e2, e3, a1, o1, o2, a2, o3, o4⟩ := h
  have hw : ∀ k, k + 8 ≤ 32 → (s.setRet ret).mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 :=
    fun k hk => rd hab (Outside.of_sub o2 (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e1, e2, e3, by rw [setRet_accessible]; exact a1, o1, o2, by rw [setRet_accessible]; exact a2, o3, o4⟩
  · rw [e1, hw 8 (by omega)]; rw [e1] at g1; exact g1
  · rw [e2, hw 16 (by omega)]; rw [e2] at g2; exact g2
  · rw [e3, hw 24 (by omega)]; rw [e3] at g3; exact g3
  · have := hw 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact g4

/-- the stack header `[st, st + 24)` outside the window: its three words survive -/
theorem stHdr {s : State} {ret stk above st : Nat} (hab : 8 ≤ above) (h : Outside st 24 (win s stk above)) :
    stW (s.setRet ret).mem st = stW s.mem st ∧ stLen (s.setRet ret).mem st = stLen s.mem st ∧
      stCap (s.setRet ret).mem st = stCap s.mem st :=
  ⟨rd hab (Outside.of_sub h (by omega) (by omega)), rd hab (Outside.of_sub h (by omega) (by omega)),
    rd hab (Outside.of_sub h (by omega) (by omega))⟩

theorem stkOK {s : State} {ret stk above st : Nat} {R : RtInv} {L : List (Nat × Nat)} (hab : 8 ≤ above)
    (ho : Outside st 24 (win s stk above)) (h : StkOK s.mem R L st) : StkOK (s.setRet ret).mem R L st := by
  obtain ⟨hw, hl, hc⟩ := stHdr (ret := ret) hab ho
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := h
  refine ⟨k1, k2, by rw [setRet_accessible]; exact k3, k4, ?_, ?_, ?_⟩
  · rw [hw, hc]; exact natLive.2 k5
  · rw [hl, hc]; exact k6
  · rw [hc]; exact k7

theorem freeOf_eq {s : State} {ret stk above st : Nat} (hab : 8 ≤ above) (h : Outside st 24 (win s stk above)) :
    NHyp.freeOf (s.setRet ret).mem st = NHyp.freeOf s.mem st := by
  obtain ⟨hw, hl, hc⟩ := stHdr (ret := ret) hab h
  simp only [NHyp.freeOf, hw, hl, hc]

theorem cpre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st : Nat} {ins : List (Nat × Nat)}
    {need cst : Nat} {s : State} {ret : Nat} (hab : 8 ≤ above)
    (h : NHyp.CPre R b L stk above zp zl zc st ins need cst s) :
    NHyp.CPre R b L stk above zp zl zc st ins need cst (s.setRet ret) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25⟩ := h
  obtain ⟨hw, hl, hc⟩ := stHdr (ret := ret) hab h10
  have hf := freeOf_eq (ret := ret) hab h10
  have hsl := CallEnv.slot h1 hab
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8, ?c9, ?c10, ?c11, ?c12, ?c13, ?c14, ?c15, ?c16, ?c17, ?c18, ?c19, ?c20,
    ?c21, ?c22, ?c23, ?c24, ?c25⟩
  case c1 => exact callEnv hab h1
  case c2 => exact h2
  case c3 => exact globals hab h3
  case c4 => exact h4
  case c5 => exact h5
  case c6 => exact h6
  case c9 => exact stkOK hab h10 h9
  case c10 => exact h10
  case c11 => exact h11
  case c15 => rw [setRet_accessible]; exact h15
  case c16 => exact h16
  case c19 => rw [hf]; exact h19
  case c20 => exact h20
  case c22 => exact h22
  case c23 => rw [setRet_accessible]; exact h23
  case c25 => rw [view_setRet hsl]; exact h25
  case c7 => exact ⟨h7.1, natLive.2 h7.2.1, h7.2.2⟩
  case c8 =>
    intro p n hm
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h8 p n hm
    refine ⟨⟨r1.1, by rw [setRet_accessible]; exact r1.2.1, r1.2.2⟩, r2, ?_, r4, by rw [hf]; exact r5, r6⟩
    rw [natNorm_setRet]; · exact r3
    have ho := r1.2.2.2.2
    simp only [win, outside_cons, outside_nil, and_true] at ho
    omega
  case c12 => rw [hc, hw]; exact h12
  case c13 => rw [hc, hw]; exact h13
  case c14 => rw [hl]; exact h14
  case c17 => rw [hf]; exact h17
  case c18 => rw [hf]; exact h18
  case c21 => rw [hf]; exact h21
  case c24 => rw [hc, hw]; exact h24

/-- the `natOne` facts of an exp-chain precondition (under their `∃ op`; window list `win ++ Z ++ stWs`) -/
theorem natOne {R : RtInv} {L : List (Nat × Nat)} {s : State} {ret stk above st : Nat} {Z : List (Nat × Nat)}
    (hab : 8 ≤ above) (h10 : Outside st 24 (win s stk above))
    (h : ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ Z ++ ExpHyp.stWs s.mem st) ∧ NHyp.StkApart s.mem st op 8) :
    (s.setRet ret).mem.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 ∧
    ∃ op, EvenHyp.NatOne R L (s.setRet ret).mem op (win (s.setRet ret) stk above ++ Z ++ ExpHyp.stWs (s.setRet ret).mem st) ∧
      NHyp.StkApart (s.setRet ret).mem st op 8 := by
  obtain ⟨op, ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩, hSA⟩ := h
  obtain ⟨hw, hl, hc⟩ := stHdr (ret := ret) hab h10
  have hws : ExpHyp.stWs (s.setRet ret).mem st = ExpHyp.stWs s.mem st := by
    simp only [ExpHyp.stWs, stkWs, hw, hl, hc]
  have n7w : Outside EvenHyp.natOneA 24 (win s stk above) := by
    simp only [outside_append] at n7; exact n7.1.1
  have n11w : Outside op 8 (win s stk above) := by
    simp only [outside_append] at n11; exact n11.1.1
  have hone : (s.setRet ret).mem.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 :=
    rd hab (Outside.of_sub n7w (Nat.le_refl _) (by omega))
  refine ⟨hone, op, ⟨?_, ?_, ?_, ?_, ?_, n6, ?_, ?_, n9, n10, ?_⟩, ?_⟩
  · exact hone.trans n1
  · exact (rd hab (Outside.of_sub n7w (by omega) (by omega))).trans n2
  · exact (rd hab (Outside.of_sub n7w (by omega) (by omega))).trans n3
  · exact (rd hab n11w).trans n4
  · rw [setRet_accessible]; exact n5
  · rw [hws]; exact n7
  · rw [setRet_accessible]; exact n8
  · rw [hws]; exact n11
  · simp only [NHyp.StkApart, hw, hl, hc]; exact hSA

/-- `globals` for a window list whose first range contains the slot -/
theorem globalsR {R : RtInv} {s : State} {ret lo hi : Nat} {rest : List (Nat × Nat)} (hlo : lo ≤ (s.regs 4).toNat)
    (hhi : (s.regs 4).toNat + 8 ≤ hi) (h : RunIface.Globals R s.mem ((lo, hi) :: rest)) :
    RunIface.Globals R (s.setRet ret).mem ((lo, hi) :: rest) := by
  obtain ⟨g1, g2, g3, g4, e1, e2, e3, a1, o1, o2, a2, o3, o4⟩ := h
  have hw : ∀ k, k + 8 ≤ 32 → (s.setRet ret).mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 :=
    fun k hk => rdO hlo hhi (Outside.of_sub o2 (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e1, e2, e3, by rw [setRet_accessible]; exact a1, o1, o2, by rw [setRet_accessible]; exact a2, o3, o4⟩
  · rw [e1, hw 8 (by omega)]; rw [e1] at g1; exact g1
  · rw [e2, hw 16 (by omega)]; rw [e2] at g2; exact g2
  · rw [e3, hw 24 (by omega)]; rw [e3] at g3; exact g3
  · have := hw 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact g4

/-- `NatOne` over a window list whose first range contains the slot (same list on both sides) -/
theorem natOneR {R : RtInv} {L : List (Nat × Nat)} {s : State} {ret lo hi op : Nat} {rest : List (Nat × Nat)}
    (hlo : lo ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ hi)
    (h : EvenHyp.NatOne R L s.mem op ((lo, hi) :: rest)) : EvenHyp.NatOne R L (s.setRet ret).mem op ((lo, hi) :: rest) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, n6, n7, ?_, n9, n10, n11⟩
  · exact (rdO hlo hhi (Outside.of_sub n7 (Nat.le_refl _) (by omega))).trans n1
  · exact (rdO hlo hhi (Outside.of_sub n7 (by omega) (by omega))).trans n2
  · exact (rdO hlo hhi (Outside.of_sub n7 (by omega) (by omega))).trans n3
  · exact (rdO hlo hhi n11).trans n4
  · rw [setRet_accessible]; exact n5
  · rw [setRet_accessible]; exact n8

/-- the stack header `[st, st + 24)` apart from a range containing the slot: its three words survive -/
theorem stHdrA {s : State} {ret lo k st : Nat} (hlo : lo ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ lo + k)
    (h : Apart st 24 lo k) :
    stW (s.setRet ret).mem st = stW s.mem st ∧ stLen (s.setRet ret).mem st = stLen s.mem st ∧
      stCap (s.setRet ret).mem st = stCap s.mem st := by
  unfold Apart at h
  exact ⟨rdR hlo hhi (by omega), rdR hlo hhi (by omega), rdR hlo hhi (by omega)⟩

end FvModexp.Amd64.SetRetWin
