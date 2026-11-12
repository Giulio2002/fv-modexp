import FvModexp.Proofs.Arm64.Nat.DrsB3T
import FvModexp.Proofs.Arm64.Nat.DrsSN

/-!
# `divRecursiveStep` (arm64), loop body segment 3b: the `stk.nat(3n)` call (natdiv.go:829)

* `t3_post` (pure): `StackNat.PostL` of the call → `T3` (stack length `l1 + rnd(3n)`, `qhatv` at `stW + 8·l1`).
* `b3s`: from `N3` (`CALL (*stack).nat(3n)`, `0x1ba668`) → the call (`snSum`) → `CBZ R1` (`3n ≠ 0`), the three stores of
  `qhatv`, `LSL $3` → `CALL memclrNoHeapPointers` → `b3m` → `A3`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **segment 3b**: `N3` → `stk.nat(3n)` → `clear(qhatv)` → `A3` -/
theorem b3s (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (X : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hN : N3 R c s Lk bk X j Z U qn) (Q : State → Prop)
    (k : ∀ L' b' S', A3 R c s L' b' S' j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hN.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hN.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hst64 : c.st < 2 ^ 64 := by have := hN.ev.sok.2.2.2.1; omega
  have hn64 : 3 * c.vl < 2 ^ 64 := by omega
  have e30 : (BitVec.ofNat 64 r3n : BitVec 64).toNat = 0x1ba66c := by decide
  refine ReachesRet.call_regions (snSum impl hap R hgr hmc hwb bk Lk (BitVec.ofNat 64 c.st)
    (BitVec.ofNat 64 (3 * c.vl))) hN.pc ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [hN.r30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]; exact ⟨hN.r0, hN.r1, trivial⟩
  case pre =>
    rw [tNat hst64, tNat hn64]
    exact sn3_pre hcr hN.ev hN.fp hspn hN.r28 (by have := hN.bud; omega)
  rw [tNat hst64, tNat hn64] at hq
  obtain ⟨hr0, hr1, hr2, L', b', hT3⟩ := t3_post hN hspn hq hrg
  have hTpc : T.pc = BitVec.ofNat 64 r3n := by rw [hT, hN.r30]
  have hTsp : T.sp = s.sp - 400#64 := f1.trans hN.sp
  have h28 : T.regs 28 = s.regs 28 := f2.trans hN.r28
  have h29 : T.regs 29 = s.sp - 408#64 := f3.trans hN.r29
  have h18 : T.regs 18 = s.regs 18 := f4.trans hN.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn' : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hT3.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hl3 := lsl3_ofNat (3 * c.vl) (by omega)
  have hne : (BitVec.ofNat 64 (3 * c.vl) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hq48 : c.qv s T.mem < 2 ^ 64 := by
    have hl := hT3.fp.len; have hlc := hT3.ev.sok.2.2.2.2.2.1
    have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
    have hn : 0 < stCap T.mem c.st := by omega
    obtain ⟨-, -, -, h48⟩ := hT3.ev.sok.2.2.2.2.1 hn
    simp only [Cx.qv]; omega
  clear hq hT f1 f2 f3 f4 hrg
  janus_run [hl3, hne] until [cA "runtime.memclrNoHeapPointers"]
  refine b3m impl R hmc' c s L' b' T.mem j Z U qn hT3 Q (k L' b') _ rfl rfl ?_ ?_ ?_ ?_ ?_ rfl
    (by unfold is3; janus_frame) (by simp) ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact hr0
  · exact h28
  · exact h29
  · exact h18
  all_goals (try dsimp only)
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]

end FvModexp.Arm64.DivRec
