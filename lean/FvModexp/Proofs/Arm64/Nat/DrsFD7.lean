import FvModexp.Proofs.Arm64.Nat.DrsFG
import FvModexp.Proofs.Arm64.Nat.DrsSegD
import FvModexp.Proofs.Arm64.Nat.DrsFin
import FvModexp.Proofs.Arm64.Nat.Restore
/-!
# `divRecursiveStep` (arm64), final block: the deferred `stk.restore(stk.save())` and the return (natdiv.go:892)
* `dsumR`: the closure `nat.divRecursiveStep.deferwrap1` (`0x1bae20`) on `LibDrs` (`Restore.sum`'s proof re-run).
* `d7aF`: from `GF` (`0x1bacdc`): `MOVB ZR, 103(RSP)` (defer bit), `R26 = &closure` (`SP'+384`), `R6 = closure.fn`,
* `d7F`: `GF` → `d7aF` → `dsumR` (`len(stk.w) := len at entry`) → `epiF` → `Kept ∧ DrsPostW` (`postF`).
-/
set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)
/-- the deferred closure of `divRecursiveStep` -/
abbrev dfnR : Nat := 0x1bae20

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure (`Restore.sum`'s proof on `LibDrs`) -/
theorem dsumR (impl : List Segment) :
    Summary (LibDrs.program.link impl) dfnR Restore.Pre Restore.Post := by
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `0x1bacdc` to the closure's entry -/
theorem d7aF (impl : List Segment) (c : Cx) (s : State) (M : Memory) (Q : State → Prop)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 rFD6) (hm : S.mem = M) (hsp : S.sp = s.sp - 400#64)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 408#64) (h18 : S.regs 18 = s.regs 18)
    (hsp4 : 408 ≤ s.sp.toNat) (hsp48 : s.sp.toNat + 96 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : M.accessible (s.sp.toNat - 408) 504 true = true)
    (r1 : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 56) (r2 : M.readLE (s.sp.toNat - 56) 8 = 0x1bae20)
    (k : ∀ Y : State, Y.pc = BitVec.ofNat 64 dfnR → Y.regs 30 = BitVec.ofNat 64 0x1bacec →
      Y.regs 26 = BitVec.ofNat 64 (s.sp.toNat - 56) → Y.sp = s.sp - 400#64 → Y.regs 28 = s.regs 28 →
      Y.regs 29 = s.sp - 408#64 → Y.regs 18 = s.regs 18 →
      MemFrame M Y.mem [(s.sp.toNat - 297, s.sp.toNat - 296)] → Y.mem.regions = M.regions →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  janus_run [r1, r2] until [dfnR]
  refine k _ rfl rfl ?_ rfl ?_ ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  all_goals first | exact h28 | exact h29 | exact h18 | janus_frame | (simp; done) | rfl

/-- the post of `divRecursiveStep` at the return -/
@[reducible] def QF (R : RtInv) (c : Cx) (s : State) : State → Prop := fun s' =>
  Kept s s' ∧ DrsPostW R c.b c.L (drsC (stLen s.mem c.st) c.ul c.vl) c.W c.qp c.ql c.st c.up c.ul c.vp c.vl s s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the end of the big path**: `GF` → deferred `stk.restore` → return with `Kept ∧ DrsPostW` -/
theorem d7F (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (T : State) (hpc : T.pc = BitVec.ofNat 64 rFD6) (hG : GF R c s Lk bk T j Z U) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T (QF R c s) := by
  have hcr := hG.cr
  have hev := hG.ev
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, -, -, -, -, -, hsti, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hst := hsti.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hst
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hsl := hG.sl
  have hfl := hG.fp.len
  obtain ⟨-, -, -, -, -, o6, -⟩ := hev.sok
  refine d7aF impl c s T.mem _ T hpc rfl hG.sp hG.r28 hG.r29 hG.r18 (by omega) ha48 hal haccT hsl.dp hsl.dfn ?_
  intro Y hpcY h30Y h26Y hspY h28Y h29Y h18Y hFY hrgY
  have hspn : Y.sp.toNat = s.sp.toNat - 400 := by
    rw [hspY, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have rY : ∀ a n, (a + n ≤ s.sp.toNat - 297 ∨ s.sp.toNat - 296 ≤ a) → Y.mem.readLE a n = T.mem.readLE a n :=
    fun a n h => hFY.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have e26 : (Y.regs 26).toNat = s.sp.toNat - 56 := by rw [h26Y, BitVec.toNat_ofNat]; omega
  have hevY : Ev R c s Lk bk Y.mem := Ev.own hcr hev (hFY.mono fun a n ho => by
    simp only [fw, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hrgY
  have hceY : CallEnv R Lk Y 24 0 := Ev.callEnv hcr hevY hspn h28Y (by omega) (by omega)
  obtain ⟨⟨g1, g2, g3⟩, hstk, -⟩ := hceY
  have dst : Y.mem.readLE (s.sp.toNat - 56 + 8) 8 = c.st := by
    rw [rY _ _ (by omega), show s.sp.toNat - 56 + 8 = s.sp.toNat - 48 by omega]; exact hsl.dst
  have dn : Y.mem.readLE (s.sp.toNat - 56 + 16) 8 = stLen s.mem c.st := by
    rw [rY _ _ (by omega), show s.sp.toNat - 56 + 16 = s.sp.toNat - 40 by omega]; exact hsl.dn
  have hcapY : stLen s.mem c.st ≤ Y.mem.readLE (c.st + 16) 8 := by
    rw [rY _ _ (by omega)]
    have : stLen T.mem c.st ≤ stCap T.mem c.st := o6
    simp only [Cx.l1] at hfl
    show stLen s.mem c.st ≤ stCap T.mem c.st
    omega
  obtain ⟨-, -, o3, o4, -⟩ := hevY.sok
  have hYacc : ∀ a n w, Y.mem.accessible a n w = T.mem.accessible a n w := fun a n w => hFY.accessible a n w
  refine ReachesRet.call_regions (dsumR impl) hpcY ?pre (fun T2 hT2 hpost hrg2 => ?_)
  case pre =>
    unfold Restore.Pre
    refine ⟨⟨g1, g2, by omega⟩, hstk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h30Y]; decide
    · rw [h30Y]; decide
    · rw [e26]; omega
    · rw [e26, hYacc]
      exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ haccT (by omega) (by omega))
    · rw [e26, dst]; omega
    · rw [e26, dst]; exact o3
    · rw [e26, dst, dn]; exact hcapY
    · rw [e26, dst, hspn]; unfold Apart; omega
    · rw [e26, hspn]; unfold Apart; omega
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpost
  rw [e26, dst, dn] at p5
  rw [e26, dst, hspn] at p6
  have hWF : MemFrame T.mem T2.mem (finWF s c.st) := hFY.trans p6 fun a n ho => by
    simp only [finWF, outside_cons, outside_nil, and_true] at ho
    obtain ⟨o1, o2, o3⟩ := ho
    refine ⟨by simp only [outside_cons, outside_nil, and_true]; exact o1, ?_⟩
    simp only [outside_cons, outside_nil, and_true]
    exact ⟨by omega, o3⟩
  have r2 : ∀ a n, (a + n ≤ s.sp.toNat - 424 ∨ s.sp.toNat - 408 ≤ a) → (a + n ≤ s.sp.toNat - 297 ∨ s.sp.toNat - 296 ≤ a) →
      (a + n ≤ c.st + 8 ∨ c.st + 16 ≤ a) → T2.mem.readLE a n = T.mem.readLE a n := fun a n h1 h2 h3 =>
    hWF.readLE a n (by simp only [finWF, outside_cons, outside_nil, and_true]; omega)
  refine epiF impl s T2 (by rw [hT2, h30Y]) (p1.trans hspY) (p3.trans h28Y) (p2.trans h18Y)
    (by rw [r2 _ _ (by omega) (by omega) (by omega)]; exact hsl.lr)
    (by rw [r2 _ _ (by omega) (by omega) (by omega)]; exact hsl.fp)
    (by omega) (by omega) hal ?_ hcr.ra4 hcr.ra48 _ fun s' ⟨e1, e2, e3, e4, e5⟩ => ⟨⟨e1, e2, e3, e4⟩, ?_⟩
  · rw [hWF.accessible]; exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ haccT (by omega) (by omega))
  · exact postF hG hWF p5 s' e5

end FvModexp.Arm64.DivRec
