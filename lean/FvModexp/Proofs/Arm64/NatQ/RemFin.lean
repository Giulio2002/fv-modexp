import FvModexp.Proofs.Arm64.NatQ.RemCall

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/RemFin.lean, TIGHT COSTS, asm s38)
# `nat.rem` (arm64): after `div` — results stored, defer bit cleared, the deferred `stk.restore` closure, return

`0x1b9130`: `r` → `SP-72 … SP-56`, `MOVB ZR, SP-89`, `R26 = SP-40` (the closure), `CALL (R2)` (`deferwrap1`:
`len(stk.w) := len at entry`, `Restore`), `LDP`, epilogue, `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatRem
open FvModexp.Arm64.NatRem
variable {H : Nat}

set_option maxRecDepth 20000 in
/-- the deferred closure on `LibRem` (`Restore.sum`'s proof re-run) -/
theorem dsum (impl : List Segment) :
    Summary (LibRem.program.link impl) dfnA Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

/-- the writes after `div`'s return: the result slots, the defer bit, the closure's frame, `len(stk.w)` -/
@[reducible] def finW (s : State) (st : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - 89, s.sp.toNat - 88), (s.sp.toNat - 72, s.sp.toNat - 48), (s.sp.toNat - 232, s.sp.toNat - 216),
    (st + 8, st + 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem fin (impl : List Segment) (s U : State) (zp zl zc st up ul uc vp vl vc r rl rc : Nat)
    (hpc : U.pc = BitVec.ofNat 64 (callDiv + 4)) (hsp : U.sp = s.sp - 208#64) (h28 : U.regs 28 = s.regs 28)
    (h29 : U.regs 29 = s.sp - 216#64) (h18 : U.regs 18 = s.regs 18)
    (e3 : U.regs 3 = BitVec.ofNat 64 r) (e4 : U.regs 4 = BitVec.ofNat 64 rl) (e5 : U.regs 5 = BitVec.ofNat 64 rc)
    (hsl : Sl s zp zl zc st up ul uc vp vl vc U.mem)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : U.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : U.mem.readLE ((s.regs 28).toNat + 16) 8 + 41712 < s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb : 41712 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (hw : U.mem.accessible (s.sp.toNat - 41712) (41712 + 112) true = true)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 41712) (41712 + 112))
    (hstacc : U.mem.accessible st 24 true = true) (hst48 : st + 24 ≤ 2 ^ 48)
    (hsw : st + 24 ≤ s.sp.toNat - 41712 ∨ s.sp.toNat + 112 ≤ st)
    (hcap : stLen s.mem st ≤ stCap U.mem st) (hr : r < 2 ^ 64) (hrl : rl < 2 ^ 64) (hrc : rc < 2 ^ 64)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibRem.program.link impl) (s.regs 30) U (fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
      s'.regs 0 = BitVec.ofNat 64 r ∧ s'.regs 1 = BitVec.ofNat 64 rl ∧ s'.regs 2 = BitVec.ofNat 64 rc ∧
      MemFrame U.mem s'.mem (finW s st) ∧ s'.mem.readLE (st + 8) 8 = stLen s.mem st) := by
  have m1 := hsl.lr; have m2 := hsl.fp; have mdp := hsl.dp; have mdf : U.mem.readLE (s.sp.toNat - 40) 8 = 1806768 := hsl.dfn
  have f8 : U.mem.readLE (s.sp.toNat - 40 + 8) 8 = st := by
    rw [show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact hsl.dst
  have f16 : U.mem.readLE (s.sp.toNat - 40 + 16) 8 = stLen s.mem st := by
    rw [show s.sp.toNat - 40 + 16 = s.sp.toNat - 24 by omega]; exact hsl.dn
  have mcap : U.mem.readLE (st + 16) 8 = stCap U.mem st := rfl
  have hD : Summary (LibRem.program.link impl) 1806768 Restore.Pre Restore.Post := dsum impl
  unfold Apart at hga
  clear hsl
  janus_run [m1, m2, mdp, mdf, mcap, f8, f16, e3, e4, e5] calls [hD]
  rename_i hlen hFF _
  have e208 : (s.sp - 208#64).toNat = s.sp.toNat - 208 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  try simp only [e208] at hFF
  refine ⟨?_, hlen⟩
  refine MemFrame.trans (?A : MemFrame U.mem _ (finW s st)) hFF fun a n ho => ⟨ho, ?_⟩
  · unfold finW; janus_frame
  · simp only [finW, outside_cons, outside_nil, and_true] at ho ⊢; omega

end FvModexp.Arm64.Q.NatRem
