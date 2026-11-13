import FvModexp.Proofs.Amd64.NatQ.DrsDefs
import FvModexp.Proofs.Amd64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Amd64.NatQ.DrsDV

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsDG.lean)
# `divRecursiveStep` (amd64), end of a loop iteration: the state before `stk.restore(mark)` and the restore (pure)

* `G`: the state at `0x5f00ad` (after `addTo(z[j-B:], qhat)`): the environment at the stack length `l1 + rnd(3n)`, the
  array from `l1` on (`FL`), the fixed slots, `mark = l1`, and the quotient / dividend after the step (`Cx.BS`).
* `Ev.restore` / `Fp.restore`: the store `stk.free = stk.free[:mark]` (header length := `l1`) keeps `Ev` and gives back
  the free part at `l1`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the model after `uu -= qhatv` (with the borrow): `uu` holds the remainder of the step -/
@[reducible] def Cx.stG (c : Cx) (s : State) (j : Nat) (U : List Nat) : Mdl.St :=
  { c.stF s j U with w := (c.sT s j U).1 }

/-- the return address of `addTo(z[j-B:], qhat)` -/
abbrev rD6 : Nat := 0x5f00ad

/-- **the end of a loop iteration** (before `stk.restore(mark)`), quotient / dividend = `Cx.BS` -/
structure G (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s + StackNat.rnd (3 * c.vl))
  fl : FL R c s Lk S.mem
  sl : Sl c s S.mem
  sj : S.mem.readLE ((s.regs 4).toNat - 112) 8 = j - c.vl / 2
  mrk : S.mem.readLE ((s.regs 4).toNat - 160) 8 = c.l1 s
  vk : S.mem.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)
  utl : S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  zk : Asm.limbs S.mem c.qp c.ql = (c.BS s j Z U).1
  uk : Asm.limbs S.mem c.up c.u1 = (c.BS s j Z U).2
  li : c.LI s j Z U
  jB : c.vl / 2 < j
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + stkR c.Hq S.mem c.st ≤ bk

theorem hdr_rd {M : Memory} {st v : Nat} (hv : v < 2 ^ 64) :
    stW (M.writeLE (st + 8) 8 v) st = stW M st ∧ stCap (M.writeLE (st + 8) 8 v) st = stCap M st ∧
      stLen (M.writeLE (st + 8) 8 v) st = v := by
  refine ⟨Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), ?_⟩
  show (M.writeLE (st + 8) 8 v).readLE (st + 8) 8 = v
  rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; exact hv)

set_option maxHeartbeats 8000000 in
/-- `Ev` across the header store `len := v` (`v ≤ cap`) -/
theorem Ev.restore {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (h : Ev R c s Lk bk M) (v : Nat) (hv : v ≤ stCap M c.st) (hv64 : v < 2 ^ 64) :
    Ev R c s Lk bk (M.writeLE (c.st + 8) 8 v) := by
  obtain ⟨eW, eC, eL⟩ := hdr_rd (M := M) (st := c.st) hv64
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.sok
  have hheld : Held R Lk (c.st + 8) 8 := h2.sub (by omega) (by omega)
  refine ⟨h.ext, by rw [Janus.Arm64.Memory.regions_writeLE]; exact h.reg, by rw [view_writeLE_held hheld]; exact h.inv,
    h.fr.writeLE v (r := (c.st, c.st + 24)) (by simp [Cx.ws, stkWs]) (by show c.st ≤ c.st + 8; omega) (by show c.st + 8 + 8 ≤ c.st + 24; omega), ?_, ?_,
    by rw [eW, eC]; exact h.sarr, h.sarrL.congr eW eC fun _ h => h⟩
  · refine ⟨fun x k hin ho => ?_⟩
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h.lf.readLE x k hin (by simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true]; omega)
  · refine ⟨h1, h2, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact h3, h4, ?_, by rw [eL, eC]; exact hv,
      by rw [eC]; exact h7⟩
    rw [eW, eC]; intro hc; obtain ⟨q1, q2, q3, q4⟩ := h5 hc
    exact ⟨q1, q2, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact q3, q4⟩

/-- the free part at `l1` after the header store `len := l1` -/
theorem Fp.restore {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {M : Memory}
    (h : FL R c s Lk M) (hv64 : c.l1 s < 2 ^ 64) : Fp R c s Lk (M.writeLE (c.st + 8) 8 (c.l1 s)) (c.l1 s) := by
  obtain ⟨eW, eC, eL⟩ := hdr_rd (M := M) (st := c.st) hv64
  have h' : FL R c s Lk (M.writeLE (c.st + 8) 8 (c.l1 s)) := h.hdr eW eC
  exact ⟨eL, h'.h, h'.w, h'.g, h'.fs, h'.st, h'.gA, h'.q, h'.u, h'.v, h'.t0⟩

end FvModexp.Amd64.Q.DivRec
