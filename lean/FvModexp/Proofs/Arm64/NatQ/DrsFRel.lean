import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsDV
import FvModexp.Proofs.Arm64.NatQ.DrsA2
import FvModexp.Proofs.Arm64.NatQ.DrsRecP
import FvModexp.Proofs.Common.DivRecFin

/-! (Q-form copy of Arm64/Nat/DrsFRel.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), the final block (natdiv.go:858-892): shared relations (pure)

After the wide-digit loop (`j ≤ B` at the head `0x1ba504`, `BLE` → `0x1ba92c`) the code is a second copy of the loop body
with `uu = u` and these differences: the recursive call divides `u[s:].norm()` (not `uu[s:B+n]`), there is no
`mark`/`restore` around `qhatv`, the correction loop never breaks (`Mdl.corr2`), the last borrow is checked
(`panic`), and the quotient is added by `addTo(z, qhat.norm())`; then the deferred `stk.restore(saved)` and the epilogue.

Model (`Mdl.finalBlock`, `Mdl.finM`, `Mdl.finR`, with the ideal `rec`/`mul`): `Cx.RF` (the recursive call), `Cx.qF`
(`qhat.norm()`), `Cx.PF` (`qhat·v[:s]`), `Cx.UF` (the dividend after the call), `Cx.sF0` (the correction loop's start),
`Cx.sFF` (its end).

Own slots of the final block (`SP'+X` = `s.sp - (400 - X)`): `128` = `s`, `296/104/304` = `u[s:]` (len/cap/ptr),
`280/288/376` = `v[s:]` (len/cap/ptr) — `BdF`; `200` = `len(qhat.norm())`; `320/144/160` = `qhatv` (ptr/len/cap);
`232` = `i`; `8..80` = `subVV.abi0` arguments/result.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

/-! ## the model -/

/-- the recursive call of the final block (model): `qhat`, `u[s:].norm()` after the call -/
@[reducible] def Cx.RF (c : Cx) (s : State) (U : List Nat) : List Nat × List Nat :=
  Mdl.finR Mdl.recI (c.V s) (c.vl / 2) U

/-- `qhat.norm()` after the recursive call (model) -/
@[reducible] def Cx.qF (c : Cx) (s : State) (U : List Nat) : List Nat := Mdl.norm (c.RF s U).1

/-- the product `qhat · v[:s]` (model) -/
@[reducible] def Cx.PF (c : Cx) (s : State) (U : List Nat) : List Nat :=
  Mdl.mulI (c.qF s U) ((c.V s).take (c.vl / 2 - 1))

/-- the dividend after the recursive call (model) -/
@[reducible] def Cx.UF (c : Cx) (s : State) (U : List Nat) : List Nat := Mdl.upd U (c.vl / 2 - 1) (c.RF s U).2

/-- the model state at the start of the final correction loop -/
@[reducible] def Cx.sF0 (c : Cx) (s : State) (U : List Nat) : Mdl.St :=
  ⟨c.qF s U, c.PF s U ++ List.replicate (3 * c.vl - (c.PF s U).length) 0, c.UF s U⟩

/-- the model state at the end of the final correction loop -/
@[reducible] def Cx.sFF (c : Cx) (s : State) (U : List Nat) : Mdl.St :=
  Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length 2 (c.sF0 s U)

/-! ## the own slots -/

/-- the slots of the final block written before the recursive call (`s`, `u[s:]`, `v[s:]`) and the facts kept
from the head (`Z` = the quotient at the head) -/
structure BdF (c : Cx) (s : State) (M : Memory) (Z : List Nat) : Prop where
  sl : Sl c s M
  ss : M.readLE (s.sp.toNat - 272) 8 = c.vl / 2 - 1
  ul : M.readLE (s.sp.toNat - 104) 8 = c.u1 - (c.vl / 2 - 1)
  uc : M.readLE (s.sp.toNat - 296) 8 = c.uc - (c.vl / 2 - 1)
  up : M.readLE (s.sp.toNat - 96) 8 = c.up + 8 * (c.vl / 2 - 1)
  vl : M.readLE (s.sp.toNat - 120) 8 = c.vl - (c.vl / 2 - 1)
  vc : M.readLE (s.sp.toNat - 112) 8 = c.vc - (c.vl / 2 - 1)
  vp : M.readLE (s.sp.toNat - 24) 8 = c.vp + 8 * (c.vl / 2 - 1)
  vk : M.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)
  utl : M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  zk : Asm.limbs M c.qp c.ql = Z

/-- `rs` avoids the final block's slots of `BdF` -/
@[reducible] def FOut (s : State) (rs : List (Nat × Nat)) : Prop :=
  Outside (s.sp.toNat - 296) 8 rs ∧ Outside (s.sp.toNat - 272) 8 rs ∧ Outside (s.sp.toNat - 120) 32 rs ∧
    Outside (s.sp.toNat - 24) 8 rs

theorem BdF.frame {c : Cx} {s : State} {M M' : Memory} {Z : List Nat} {rs : List (Nat × Nat)}
    (h : BdF c s M Z) (hF : MemFrame M M' rs) (ho : FixOut s rs) (hf : FOut s rs)
    (hv : M'.readLE c.vp (8 * c.vl) = M.readLE c.vp (8 * c.vl))
    (hu : M'.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)))
    (hz : M'.readLE c.qp (8 * c.ql) = M.readLE c.qp (8 * c.ql)) : BdF c s M' Z := by
  obtain ⟨i1, i2, i3, i4⟩ := hf
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N → M'.readLE x n = M.readLE x n :=
    fun hA h1 h2 => hF.readLE _ _ (hA.of_sub h1 h2)
  exact ⟨h.sl.frame hF ho, by rw [r i2 (by omega) (by omega)]; exact h.ss, by rw [r i3 (by omega) (by omega)]; exact h.ul,
    by rw [r i1 (by omega) (by omega)]; exact h.uc, by rw [r i3 (by omega) (by omega)]; exact h.up,
    by rw [r i3 (by omega) (by omega)]; exact h.vl, by rw [r i3 (by omega) (by omega)]; exact h.vc,
    by rw [r i4 (by omega) (by omega)]; exact h.vp,
    by rw [hv]; exact h.vk, by rw [hu]; exact h.utl, by rw [limbs_congr hz]; exact h.zk⟩

/-- a callee frame `R.rt ++ winA S k a ++ ws` (`S.sp = SP - 400`, `a ≤ 103`) avoids the final block's slots when `ws`
does -/
theorem fOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside (s.sp.toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - 400) (ha : a ≤ 103) (hws : FOut s ws) :
    FOut s (R.rt ++ winA S k a ++ ws) := by
  obtain ⟨w1, w2, w3, w4⟩ := hws
  have o : ∀ x n, s.sp.toNat - 408 ≤ x → x + n ≤ s.sp.toNat + 96 → Outside x n R.rt :=
    fun x n h1 h2 => hout.of_sub (by omega) (by omega)
  simp only [FOut, winA, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  exact ⟨⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w1⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w2⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w3⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w4⟩⟩

/-- ranges outside the own frame avoid the final block's slots -/
theorem fo504F {s : State} {rs : List (Nat × Nat)} (h : Outside (s.sp.toNat - 408) 504 rs) (h0 : 408 ≤ s.sp.toNat) :
    FOut s rs := by
  have o : ∀ x n, s.sp.toNat - 408 ≤ x → x + n ≤ s.sp.toNat + 96 → Outside x n rs :=
    fun x n h1 h2 => h.of_sub (by omega) (by omega)
  exact ⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega),
    o _ _ (by omega) (by omega)⟩

/-- an own store inside the frame and outside `[SP-296, SP-288)`, `[SP-272, SP-264)`, `[SP-120, SP-88)`,
`[SP-24, SP-16)` and the fixed slots keeps `BdF` -/
theorem BdF.own {c : Cx} {s : State} {M M' : Memory} {Z : List Nat} {rs : List (Nat × Nat)}
    (h : BdF c s M Z) (hF : MemFrame M M' rs) (ho : FixOut s rs) (hf : FOut s rs)
    (hin : ∀ x n, Outside x n (win s c.W 96) → Outside x n rs)
    (hvw : Outside c.vp (8 * c.vl) (win s c.W 96))
    (huw : Outside (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) (win s c.W 96))
    (hqw : Outside c.qp (8 * c.ql) (win s c.W 96)) : BdF c s M' Z :=
  h.frame hF ho hf (hF.readLE _ _ (hin _ _ hvw)) (hF.readLE _ _ (hin _ _ huw)) (hF.readLE _ _ (hin _ _ hqw))

/-! ## after `clear(qhat)` -/

/-- the return address of the final block's `clear(qhat)` -/
abbrev rF1 : Nat := 0x1ba938

/-- **after the final block's `clear(qhat)`** (`Z`/`U` = quotient/dividend at the head, `j ≤ B`) -/
structure AF1 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 rF1
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  sl : Sl c s S.mem
  vk : S.mem.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)
  utl : S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  zk : Asm.limbs S.mem c.qp c.ql = Z
  jB : j ≤ c.vl / 2
  li : c.LI s j Z U
  uk : Asm.limbs S.mem c.up c.u1 = U
  q0 : S.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0
  bud : c.lo s + c.K s + stkR c.Hq S.mem c.st ≤ bk

/-! ## after the recursive call -/

/-- the return address of the final block's recursive call -/
abbrev rF2 : Nat := 0x1baa04

/-- **after the final block's recursive call** -/
structure AF2 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 rF2
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  bd : BdF c s S.mem Z
  jB : j ≤ c.vl / 2
  li : c.LI s j Z U
  qk : Asm.limbs S.mem c.t0 (c.vl / 2 + 1) = (c.RF s U).1
  uk : Asm.limbs S.mem c.up c.u1 = c.UF s U
  bud : c.lo s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq S.mem c.st ≤ bk

end FvModexp.Arm64.Q.DivRec
