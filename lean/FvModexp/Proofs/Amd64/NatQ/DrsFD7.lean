import FvModexp.Proofs.Amd64.NatQ.DrsFD6
import FvModexp.Proofs.Amd64.NatQ.DrsFin
import FvModexp.Proofs.Amd64.Nat.Restore
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFD7.lean; run pattern of Amd64/NatQ/DivLargeT2.lean `t2c`)
# `divRecursiveStep` (amd64), final block: the deferred `stk.restore(stk.save())` and the return (natdiv.go:892)

* `dsumD`: the closure `nat.divRecursiveStep.deferwrap1` (`0x5f0800`) on `LibDrs` (`Restore`'s proof re-run, a copy of
  `NatQ/DivLargeCallees.dsum`).
* `d7F`: from `GF` (`0x5f0685`): `MOVB $0, 0x5f(SP)` (defer bit `r - 297`), `DX = [0x178(SP)] = r - 56` (the defer
  record), `R9 = [DX] = 0x5f0800`, `CALL R9` (`dsumD`: `len(stk.w) := len at entry`), `ADDQ $0x180, SP; POPQ BP; RET`
  → `Kept ∧ DrsPostW` (`postF`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the deferred closure of `divRecursiveStep` -/
abbrev dfnR : Nat := 0x5f0800

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure of `divRecursiveStep` (`Restore`'s proof on `LibDrs`) -/
theorem dsumD (impl : List Amd64.Segment) :
    Summary (LibDrs.program.link impl) dfnR Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

/-- the post of `divRecursiveStep` at the return -/
@[reducible] def QF (R : RtInv) (c : Cx) (s : State) : State → Prop := fun s' =>
  Kept s s' ∧ DrsPostW R c.b c.L c.Hq (drsCQ c.ul c.vl) c.W c.qp c.ql c.st c.up c.ul c.vp c.vl s s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the end of the big path**: `GF` → deferred `stk.restore` → return with `Kept ∧ DrsPostW` -/
theorem d7F (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (T : State) (hpc : T.rip = BitVec.ofNat 64 rFD6) (hG : GF R c s Lk bk T j Z U) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T (QF R c s) := by
  have hcr := hG.cr
  have hev := hG.ev
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw hal
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsti := hpre.sti
  have hst := hsti.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hst
  have hsp := hG.sp; have h5 := hG.r5; have h14 := hG.r14; have hfs := hG.fs; have hdf := hG.df
  have hx15 := hG.x15
  have hTacc : ∀ a n v, T.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hev.fr.accessible a n v
  have hwacc : T.mem.accessible ((s.regs 4).toNat - c.W) (c.W + 96) true = true := by rw [hTacc]; exact hw
  have hsacc : T.mem.accessible c.st 24 true = true := by rw [hTacc]; exact hsti.1.2.2.1
  have hst48 : c.st + 24 ≤ 2 ^ 48 := hsti.1.2.2.2.1
  have hsl := hG.sl
  have m1 := hsl.ra; have m2 := hsl.bp; have mdp := hsl.dp; have mdf := hsl.dfn
  have f8 : T.mem.readLE ((s.regs 4).toNat - 56 + 8) 8 = c.st := by
    rw [show (s.regs 4).toNat - 56 + 8 = (s.regs 4).toNat - 48 by omega]; exact hsl.dst
  have f16 : T.mem.readLE ((s.regs 4).toNat - 56 + 16) 8 = stLen s.mem c.st := by
    rw [show (s.regs 4).toNat - 56 + 16 = (s.regs 4).toNat - 40 by omega]; exact hsl.dn
  have hfl := hG.fp.len
  obtain ⟨-, -, -, -, -, o6, -⟩ := hev.sok
  have mcap : stLen s.mem c.st ≤ T.mem.readLE (c.st + 16) 8 := by
    simp only [Cx.l1] at hfl
    show stLen s.mem c.st ≤ stCap T.mem c.st
    omega
  have hra := hcr.ra47
  have hD : Summary (LibDrs.program.link impl) dfnR Restore.Pre Restore.Post := dsumD impl
  have hx0 := hcr.x15; have hdf0 := hcr.df
  clear hev hpre hcr hsti
  janus64_run [m1, m2, mdp, mdf, mcap, f8, f16, hfs] calls [hD]
  rename_i _ _ h5C h14C hx15C hfsC hdfC hlen hFF
  have hFE : MemFrame T.mem ((T.mem.writeLE ((s.regs 4).toNat - 297) 1 0).writeLE ((s.regs 4).toNat - 400) 8 6227608)
      [((s.regs 4).toNat - 297, (s.regs 4).toNat - 296), ((s.regs 4).toNat - 400, (s.regs 4).toNat - 392)] := by
    janus_frame
  have hWF : MemFrame T.mem _ (finWF s c.st) := hFE.trans hFF fun a n ho => by
    simp only [finWF, outside_cons, outside_nil, and_true] at ho
    simp only [outside_cons, outside_nil, and_true]; omega
  simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] at h5C h14C
  refine ⟨⟨?_, ?_, ?_, ?_⟩, postF hG hWF hlen _ rfl ?_ ?_⟩
  all_goals simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals first
    | exact h5C.trans h14
    | (rw [h14C, h14])
    | (rw [hx15C, hx15, hx0])
    | (rw [hfsC])
    | exact hdf0.symm
    | (rw [hdfC, hdf0])
    | rfl

end FvModexp.Amd64.Q.DivRec
