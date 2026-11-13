import FvModexp.Proofs.Amd64.Nat.DivLargeDefs
import FvModexp.Proofs.Amd64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# `divRecursiveStep`'s statement (amd64), Q-form (TIGHT COSTS, top s38): `Q.DivLarge.DrsPreW` / `DrsPostW` / `DrsHypQ`

Amd64 twin of Arm64/NatQ/DrsIfaceQ.lean (asm s38) on the amd64 `DrsPreW` / `DrsPostW` / `DrsHyp` of
Amd64/Nat/DivLargeDefs.lean, with a reserve level `H` and a LEVEL-FREE consumption `cost` (e.g. `Q.drsCQ ul vl`):
the pre's cost slot is `(stLen + 12·vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b)` (the level twin of the `2 ^ 16` bound),
the post's `RtPost … cost` is `RtPostQ … (cost + stkR H s.mem st) (stkR H s'.mem st)`. Everything else verbatim
(`v` on the stack at `RSP + 8 … + 24` as Nat arguments, window `40960 / 96`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge

/-- The precondition of `divRecursiveStep` with the stack window `W` (register args `z = (qp, ql, qc)`, `st`, `u = (up, ul, uc)`, `depth` in `R10`; the stack args `v = (vp, vl, vc)` at `RSP + 8, + 16, + 24`); a plain conjunction (conjuncts in order: ce, sv, gl, qlc, qc40, ulc, uc40, vlc, vc40, v2, v9, vtop, q0, room, qa, ua, va, qu, qv, uv, sti, stl, sq, su, sv2, wbap, hf, fw, ga, cost, inv, vpS, vlS, vcS, tl; accessors `DrsPreW.<name>`). -/
def DrsPreW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost W : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  (CallEnv R L s W 96) ∧
  (Serves R) ∧
  (RunIface.Globals R s.mem (win s W 96)) ∧
  (ql ≤ qc) ∧
  (qc < 2 ^ 40) ∧
  (ul ≤ uc) ∧
  (uc < 2 ^ 40) ∧
  (vl ≤ vc) ∧
  (vc < 2 ^ 40) ∧
  (2 ≤ vl) ∧
  (vl ≤ 2 ^ 9 ∧ ql ≤ 2 ^ 9) ∧
  (2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) ∧
  (natVal s.mem qp ql = 0) ∧
  (2 * natVal s.mem up ul < 2 ^ (64 * (vl + ql))) ∧
  (s.mem.accessible qp (8 * ql) true = true ∧ qp + 8 * ql ≤ 2 ^ 48 ∧ Held R L qp (8 * ql) ∧ Outside qp (8 * ql) (win s W 96) ∧ Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8) ∧
  (s.mem.accessible up (8 * ul) true = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧ Outside up (8 * ul) (win s W 96) ∧ Apart up (8 * ul) ((s.regs 14).toNat + 16) 8) ∧
  (s.mem.accessible vp (8 * vl) false = true ∧ vp + 8 * vl ≤ 2 ^ 48 ∧ Held R L vp (8 * vl) ∧ Outside vp (8 * vl) (win s W 96) ∧ Apart vp (8 * vl) RunIface.gA 32 ∧ Held R L vp (8 * vc) ∧ vp + 8 * vc ≤ 2 ^ 48) ∧
  (Apart qp (8 * ql) up (8 * ul)) ∧
  (Apart qp (8 * ql) vp (8 * vl)) ∧
  (Apart up (8 * ul) vp (8 * vl)) ∧
  (StkIn R L s W 96 st) ∧
  (stLen s.mem st + 12 * vl + 64 ≤ 2 ^ 16 ∧ 0 < stCap s.mem st ∧ Apart vp (8 * vc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧ (st ≠ 0 ∧ up % 8 = 0 ∧ qp % 8 = 0)) ∧
  (Apart qp (8 * ql) st 24 ∧ Apart qp (8 * ql) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart st 24 StackNat.wbA 4) ∧
  (Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s W 96)) ∧
  (Apart qp (8 * ql) RunIface.gA 32 ∧ Apart up (8 * ul) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32) ∧
  (stLen s.mem st + 12 * vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b) ∧
  (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp) ∧
  (s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl) ∧
  (s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc) ∧
  (Apart qp (8 * ql) (s.fsBase.toNat - 8) 8 ∧ Apart up (8 * ul) (s.fsBase.toNat - 8) 8 ∧ Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8)

theorem DrsPreW.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : CallEnv R L s W 96 := h.1
theorem DrsPreW.sv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Serves R := h.2.1
theorem DrsPreW.gl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : RunIface.Globals R s.mem (win s W 96) := h.2.2.1
theorem DrsPreW.qlc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : ql ≤ qc := h.2.2.2.1
theorem DrsPreW.qc40 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : qc < 2 ^ 40 := h.2.2.2.2.1
theorem DrsPreW.ulc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : ul ≤ uc := h.2.2.2.2.2.1
theorem DrsPreW.uc40 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : uc < 2 ^ 40 := h.2.2.2.2.2.2.1
theorem DrsPreW.vlc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : vl ≤ vc := h.2.2.2.2.2.2.2.1
theorem DrsPreW.vc40 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : vc < 2 ^ 40 := h.2.2.2.2.2.2.2.2.1
theorem DrsPreW.v2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : 2 ≤ vl := h.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.v9 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : vl ≤ 2 ^ 9 ∧ ql ≤ 2 ^ 9 := h.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vtop {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.q0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : natVal s.mem qp ql = 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.room {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : 2 * natVal s.mem up ul < 2 ^ (64 * (vl + ql)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.qa {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : s.mem.accessible qp (8 * ql) true = true ∧ qp + 8 * ql ≤ 2 ^ 48 ∧ Held R L qp (8 * ql) ∧ Outside qp (8 * ql) (win s W 96) ∧ Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.ua {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : s.mem.accessible up (8 * ul) true = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧ Outside up (8 * ul) (win s W 96) ∧ Apart up (8 * ul) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.va {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : s.mem.accessible vp (8 * vl) false = true ∧ vp + 8 * vl ≤ 2 ^ 48 ∧ Held R L vp (8 * vl) ∧ Outside vp (8 * vl) (win s W 96) ∧ Apart vp (8 * vl) RunIface.gA 32 ∧ Held R L vp (8 * vc) ∧ vp + 8 * vc ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.qu {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.qv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.uv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart up (8 * ul) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.sti {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : StkIn R L s W 96 st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.stl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : stLen s.mem st + 12 * vl + 64 ≤ 2 ^ 16 ∧ 0 < stCap s.mem st ∧ Apart vp (8 * vc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧ (st ≠ 0 ∧ up % 8 = 0 ∧ qp % 8 = 0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.sq {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) st 24 ∧ Apart qp (8 * ql) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.su {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.sv2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.wbap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.hf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.fw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s W 96) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.ga {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) RunIface.gA 32 ∧ Apart up (8 * ul) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : stLen s.mem st + 12 * vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vpS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vlS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vcS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.tl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L H cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) (s.fsBase.toNat - 8) 8 ∧ Apart up (8 * ul) (s.fsBase.toNat - 8) 8 ∧ Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- the precondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  DrsPreW R b L H cost 40960 qp ql qc st up ul uc vp vl vc s

/-- the postcondition of `divRecursiveStep` with the stack window `W` (FS base and DF kept) -/
@[reducible] def DrsPostW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost W : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  natVal s'.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl ∧
  natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), RtPostQ R b (cost + stkR H s.mem st) (stkR H s'.mem st) L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
    MemFrame s.mem s'.mem (R.rt ++ win s W 96 ++ [(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st)

/-- the postcondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  DrsPostW R b L H cost 40960 qp ql st up ul vp vl s s'

/-- **`divRecursiveStep`'s `Ensures`, Q-form** (on the division library program; `v`'s words bound by the pre's stack slots) -/
def DrsHypQ (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc d : BitVec 64) (vp vl vc : Nat),
    Ensures ((Extracted.program.onlySegments drsNames).link impl) (segAddr Extracted.program drsFn)
      [qp, ql, qc, st, up, ul, uc, d]
      (fun s => DrsPre R b L H (dc ul.toNat vl) qp.toNat ql.toNat qc.toNat st.toNat up.toNat
        ul.toNat uc.toNat vp vl vc s)
      (fun s s' => DrsPost R b L H (dc ul.toNat vl) qp.toNat ql.toNat st.toNat up.toNat
        ul.toNat vp vl s s')

end FvModexp.Amd64.Q.DivLarge
