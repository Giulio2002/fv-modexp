import FvModexp.Proofs.Amd64.Exp.P2DEPre
import FvModexp.Proofs.Amd64.Exp.SetRetWinX

set_option autoImplicit false

/-!
# `NHyp.P2PreS` (= `P2Hyp`'s precondition) survives installing the return address (amd64, Janus v0.4.0 `hinv` of `P2D.ens`; top s54)

`janus64_pre_setRet` over the whole precondition did not finish in 15 min (s53, every variant). Proved by hand from the
frame lemmas `SetRetWin` / `SetRetWinX`: the stack-argument words lie above `RSP + 8`; the stack header, the operands,
`natOne` and its limb and the globals lie outside the call window, which contains the return slot (`8 ≤ above`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.NHyp

open FvModexp.Amd64.SetRetWin

/-- `P2PreS` survives installing the return address -/
theorem p2pre_inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) (z zl zc st x xl xc lm : BitVec 64)
    (y yl yc : Nat) (hab : 8 ≤ above) (p : Janus.Amd64.Program) (e : Nat) (args : List W64) :
    Ensures.SetRetInv p e args (P2PreS R b L stk above need cost z zl zc st x xl xc lm y yl yc) := by
  intro s ret _ _ hp
  obtain ⟨hy, ⟨hC, hxv, hyv, hl1, hl2, hst, hO⟩, hxl, hxc, hX⟩ := hp
  have h10 : Outside st.toNat 24 (win s stk above) := hC.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hl, -⟩ := stHdr (ret := ret) hab h10
  have hf := freeOf_eq (ret := ret) hab h10
  have hrx := (hC.2.2.2.2.2.2.2.1 x.toNat xl.toNat (by simp)).1
  have hry := (hC.2.2.2.2.2.2.2.1 y yl (by simp)).1
  obtain ⟨hone, hO'⟩ := natOne (ret := ret) hab h10 hO
  obtain ⟨y1, y2, y3⟩ := hy
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hX
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, hl1, hl2, hst, hO'⟩, hxl, hxc, ⟨x1, ?_, ?_, ?_, x5, ?_⟩⟩
  · exact (readLE_setRet_of_disjoint (s := s) (ret := ret) (a := (s.regs 4).toNat + 0 + 8) (n := 8)
      (Or.inr (by omega))).trans y1
  · exact (readLE_setRet_of_disjoint (s := s) (ret := ret) (a := (s.regs 4).toNat + 0 + 16) (n := 8)
      (Or.inr (by omega))).trans y2
  · exact (readLE_setRet_of_disjoint (s := s) (ret := ret) (a := (s.regs 4).toNat + 0 + 24) (n := 8)
      (Or.inr (by omega))).trans y3
  · rw [hl]; exact cpre hab hC
  · show 0 < (s.setRet ret).mem.readLE x.toNat (8 * xl.toNat); rw [rd hab hrx.2.2.2.2]; exact hxv
  · show 0 < (s.setRet ret).mem.readLE y (8 * yl); rw [rd hab hry.2.2.2.2]; exact hyv
  · rw [hone]; exact x2
  · rw [setRet_accessible]; exact x3
  · rw [setRet_accessible]; exact x4
  · rw [hf]; exact x6

end FvModexp.Amd64.NHyp
