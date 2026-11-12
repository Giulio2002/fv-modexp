import FvModexp.Proofs.Arm64.Exp.NPow
import FvModexp.Proofs.Arm64.Exp.EvDefs
import FvModexp.Proofs.Common.NPowNot

/-!
# `nat.expNN` (arm64): `m.isPow2()` fails (nat.go:376-388, inlined at fn+0x578..0x5c0) → `expNNEven` entry

For a normalised even `m` that is not a power of two (`Expmc.notPow_step`): the loop skips the zero words, and at the
first non-zero word the test `i == len(m)-1 && x&(x-1) == 0` fails, so `logM, ok = 0, false` and
`z.expNNEven(stk, x, y, m)` is called (fn+0x5c4..0x5d8: `X1 = len z` (old `X11`), `X11 = n` (old `X1`), return
fn+0x618 = 1788100). On `LibNE` (the callee `expNNEven` is not in `LibN`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem powStepE (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Outcome → Prop) (mp n i : Nat) (M : Memory) (hmp : mp + 8 * n ≤ 2 ^ 48)
    (hma : M.accessible mp (8 * n) false = true) (hi : i < n)
    (hc : M.readLE (mp + 8 * i) 8 = 0 → i + 1 < n)
    (hc2 : M.readLE (mp + 8 * i) 8 ≠ 0 → i + 1 = n →
      (M.readLE (mp + 8 * i) 8 - 1) &&& M.readLE (mp + 8 * i) 8 ≠ 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 powH) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h13 : S.regs 13 = BitVec.ofNat 64 i) (hmem : S.mem = M)
    (KN : M.readLE (mp + 8 * i) 8 = 0 → ∀ S' : State, S'.pc = BitVec.ofNat 64 powH → S'.sp = S.sp →
      (∀ r, r ≠ 13 → r ≠ 15 → S'.regs r = S.regs r) → S'.regs 13 = BitVec.ofNat 64 (i + 1) → S'.mem = M →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q)
    (KE : M.readLE (mp + 8 * i) 8 ≠ 0 → ∀ S' : State, S'.pc = BitVec.ofNat 64 ExpEven.fnE → S'.sp = S.sp →
      (∀ r, r ≠ 1 → r ≠ 11 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 30 → S'.regs r = S.regs r) →
      S'.regs 1 = S.regs 11 → S'.regs 11 = S.regs 1 → S'.regs 30 = BitVec.ofNat 64 1788100 → S'.mem = M →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  have ha : M.accessible (mp + 8 * i) 8 false = true := Memory.accessible_mono _ hma (by omega) (by omega)
  have hn48 : n ≤ 2 ^ 45 := by omega
  have hlt : M.readLE (mp + i * 8) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  by_cases hw0 : M.readLE (mp + 8 * i) 8 = 0
  · have hw' : M.readLE (mp + i * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hw0
    have := hc hw0
    janus_run [hw'] until [powH, 1788008, 1788084]
    refine KN hw0 _ rfl rfl (fun r h1 h2 => ?_) ?_ rfl
    · simp only [setReg, if_neg h1, if_neg h2]
    all_goals first | (janus_simp; done) | skip
    all_goals simp (config := { decide := true }) only [setReg, ite_true, ite_false]
    all_goals apply BitVec.eq_of_toNat_eq
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    all_goals omega
  · have hw' : M.readLE (mp + i * 8) 8 ≠ 0 := by rw [Nat.mul_comm]; exact hw0
    by_cases hl : i + 1 = n
    · have hand : (M.readLE (mp + i * 8) 8 - 1) &&& M.readLE (mp + i * 8) 8 ≠ 0 := by
        rw [Nat.mul_comm]; exact hc2 hw0 hl
      subst hl
      janus_run [hw', hand] until [ExpEven.fnE, powH, 1788032]
      refine KE hw0 _ rfl rfl (fun r h1 h2 h3 h4 h5 h6 => ?_) ?_ ?_ ?_ rfl
      · simp only [setReg, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]
      all_goals first | (janus_simp; done) | rfl | skip
    · janus_run [hw'] until [ExpEven.fnE, powH, 1788032]
      refine KE hw0 _ rfl rfl (fun r h1 h2 h3 h4 h5 h6 => ?_) ?_ ?_ ?_ rfl
      · simp only [setReg, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]
      all_goals first | (janus_simp; done) | rfl | skip

/-- the whole failing `isPow2` loop from `i` (words `0..i-1` zero) to `expNNEven`'s entry -/
theorem powAllE (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Outcome → Prop) (mp n : Nat) (M : Memory) (sp0 : BitVec 64) (G : Nat → BitVec 64)
    (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true) (hn : 0 < n) (hN : NatNorm M mp n)
    (hnp : ¬∃ k, natVal M mp n = 2 ^ k)
    (h1 : G 1 = BitVec.ofNat 64 n) (h10 : G 10 = BitVec.ofNat 64 mp)
    (KE : ∀ S' : State, S'.pc = BitVec.ofNat 64 ExpEven.fnE → S'.sp = sp0 →
      (∀ r, r ≠ 1 → r ≠ 11 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 30 → S'.regs r = G r) →
      S'.regs 1 = G 11 → S'.regs 11 = G 1 → S'.regs 30 = BitVec.ofNat 64 1788100 → S'.mem = M →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q) :
    ∀ d i (S : State), n - 1 - i = d → i < n → (∀ j, j < i → M.readLE (mp + 8 * j) 8 = 0) →
      S.pc = BitVec.ofNat 64 powH → S.sp = sp0 →
      (∀ r, r ≠ 13 → r ≠ 15 → r ≠ 16 → S.regs r = G r) → S.regs 13 = BitVec.ofNat 64 i → S.mem = M →
      Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hz hpc hsp hG h13 hmem
    have hst := Expmc.notPow_step M mp n i hn hN hnp hz hi
    refine powStepE impl ret0 hret Q mp n i M hmp hma hi hst.1 hst.2 S hpc
      ((hG 1 (by decide) (by decide) (by decide)).trans h1) ((hG 10 (by decide) (by decide) (by decide)).trans h10)
      h13 hmem (fun h0 => absurd (hst.1 h0) (by omega)) (fun _ S' e1 e2 e3 e4 e5 e6 e7 => KE S' e1 (e2.trans hsp)
        (fun r a b c d f g => ?_) (e4.trans (hG 11 (by decide) (by decide) (by decide)))
        (e5.trans (hG 1 (by decide) (by decide) (by decide))) e6 e7)
    rw [e3 r a b c d f g, hG r c d f]
  | succ d ih =>
    intro i S hd hi hz hpc hsp hG h13 hmem
    have hst := Expmc.notPow_step M mp n i hn hN hnp hz hi
    refine powStepE impl ret0 hret Q mp n i M hmp hma hi hst.1 hst.2 S hpc
      ((hG 1 (by decide) (by decide) (by decide)).trans h1) ((hG 10 (by decide) (by decide) (by decide)).trans h10)
      h13 hmem (fun h0 S' e1 e2 e3 e4 e5 => ih (i + 1) S' (by omega) (hst.1 h0)
        (fun j hj => by rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl; exacts [hz j hj, h0])
        e1 (e2.trans hsp) (fun r a b c => (e3 r a b).trans (hG r a b c)) e4 e5)
      (fun _ S' e1 e2 e3 e4 e5 e6 e7 => KE S' e1 (e2.trans hsp)
        (fun r a b c d f g => by rw [e3 r a b c d f g, hG r c d f])
        (e4.trans (hG 11 (by decide) (by decide) (by decide)))
        (e5.trans (hG 1 (by decide) (by decide) (by decide))) e6 e7)

end FvModexp.Arm64.ExpN
