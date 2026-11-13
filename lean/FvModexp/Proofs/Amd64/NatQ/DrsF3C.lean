import FvModexp.Proofs.Amd64.NatQ.DrsF3S
import FvModexp.Proofs.Amd64.NatQ.DrsSN3
import FvModexp.Proofs.Amd64.NatQ.DrsSN

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF3.lean `f3s`; adapted from Amd64/NatQ/DrsB3C.lean)
# `divRecursiveStep` (amd64), final block segment 3b: `qhatv := stk.nat(3n)`, `clear(qhatv)` (natdiv.go:865-866)

`f3s`: from `NF3` (the entry of `(*stack).nat`, called at `0x5f0285`): the call (`snSum`, return `0x5f028a`), `TF3`
(`t3F_post`), `TESTQ BX, BX` (`3n ≠ 0`), `qhatv`'s slots, `CALL runtime.memclrNoHeapPointers` at `0x5f02b1` → `f3m`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
/-- the return site `0x5f028a` (after `CALL (*stack).nat(3n)`) is admissible for `(*stack).nat`'s program -/
theorem raF3 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) 0x5f028a := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := StackNat.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by decide) 0xa0a (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **final block segment 3b**: `NF3` → `stk.nat(3n)` → `clear(qhatv)` → `AF3` -/
theorem f3s (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (X : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hN : NF3 R c s Lk bk X j Z U qn) (Q : State → Prop)
    (k : ∀ L' b' S', AF3 R c s L' b' S' j Z U qn → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hN.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hN.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hst64 : c.st < 2 ^ 64 := by have := hN.ev.sok.2.2.2.1; omega
  have hn64 : 3 * c.vl < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (snSum impl hap R hgr hmc hwb c.Hq bk Lk) hN.pc ⟨?ra, hN.x15, hN.df, ?pre⟩
    fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_
  case ra => simp only [regSP]; rw [hspn, hN.ra]; exact raF3 impl hap
  case pre =>
    rw [hN.r0, hN.r3, tNat hst64, tNat hn64]
    exact sn3_pre hcr hN.ev hN.fp hspn hN.r14 hN.fs (by have := hN.bud; omega)
  rw [hN.r0, hN.r3, tNat hst64, tNat hn64] at hq
  have hfsT : T.fsBase = s.fsBase := hq.1.trans hN.fs
  have hdfT : T.df = false := hq.2.1.trans hN.df
  obtain ⟨hr0, hr3, hr1, L', b', hT3⟩ := t3F_post hN hspn hq hrg
  have hTpc : T.rip = BitVec.ofNat 64 rF3n := by rw [hT, retAddrOf, hspn, hN.ra]
  have hT4 : T.regs 4 = s.regs 4 - 392#64 := by rw [f4]; exact sp_ret400 hspn (by omega)
  have hT5 : T.regs 5 = s.regs 4 - 8#64 := f5.trans hN.r5
  have hT14 : T.regs 14 = s.regs 14 := f14.trans hN.r14
  have hT15 : T.xmm 15 = 0#128 := f15.trans hN.x15
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hT4, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hT3.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hl3 : BitVec.ofNat 64 (3 * c.vl) <<< 3 = BitVec.ofNat 64 (8 * (3 * c.vl)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hne : (BitVec.ofNat 64 (3 * c.vl) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hq48 : c.qv s T.mem < 2 ^ 64 := by
    have hl := hT3.fp.len; have hlc := hT3.ev.sok.2.2.2.2.2.1
    have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
    have hn : 0 < stCap T.mem c.st := by omega
    obtain ⟨-, -, -, h48⟩ := hT3.ev.sok.2.2.2.2.1 hn
    simp only [Cx.qv]; omega
  clear hq hT f4 f5 f14 f15 hrg
  janus64_run [hl3, hne, BitVec.msb_eq_decide] until [cA "runtime.memclrNoHeapPointers"]
  refine f3m impl R hmc' c s L' b' T.mem j Z U qn hT3 Q (k L' b') _ rfl ?sp ?r5 ?r14 hfsT rfl hT15 ?r0 ?r3
    (by unfold isF3c; janus_frame) (by janus64_simp) ?ra ?e1 ?e2 ?e3
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hT5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hT14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hr0
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e1 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e2 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e3 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
