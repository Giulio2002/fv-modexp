import FvModexp.Proofs.Arm64.Nat.MulLoopNat
import FvModexp.Proofs.Arm64.Nat.KSqrProD

/-!
# `nat.mul` (arm64), the chunk loop's prologue: the call `t := stk.nat(2n)` (`0x1bb0bc`) → the loop head, `k = 0`

`mNatSum`: `(*stack).nat` (`StackNat.sumL`) as a summary in `LibMul`; `lnat`: from `LP` the call, `lbOf`, the return
`0x1bb0c0` (`R3 = n`, `JMP 0x1bb204`) ⟹ `LH … 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (tN' stkNat_entry)

/-- `(*stack).nat` (`StackNat.sumL`) as a summary in `LibMul.program` -/
theorem mNatSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibMul.program.link impl) stkNatM
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [st, k] ∧ StackNat.Pre R b L 4208 24 st.toNat k.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        StackNat.PostL R b L 4208 24 st.toNat k.toNat s s') := by
  have hS := StackNat.sumL impl hap R hgr hmc hwb b L st k LibMul.names
    (FvModexp.Arm64.Callees.sub_of_all (by decide))
  rw [← LibMul.eq_only, stkNat_entry] at hS
  exact hS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`t := stk.nat(2n)`** from `LP` to the loop head with no chunk done -/
theorem lnat (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} {P : State}
    (h : LP R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P) {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' tp tl tc : Nat) (S : State),
      LH R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' 0 tp tl tc S →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ReachesRet (LibMul.program.link impl) ret P Q := by
  have hq0 := h.lq
  obtain ⟨hW, hWs, hal, ha48, -, -, -, hcap, hc40, -, hx12, hy12, -⟩ := hq0.lay
  have h40 := hq0.h40; have hlt := hq0.hlt
  have hst : st < 2 ^ 64 := by have := hq0.sok.2.2.2.1; omega
  have hn : 2 * yl < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (mNatSum impl hap R hgr hmc hwb bk Lk (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 (2 * yl))) h.pc ⟨?_, ⟨h.r0, h.r1, trivial⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · rw [h.r30, tN' (by omega)]; exact mul_ra hap (by decide) 148 (by decide)
  · rw [tN' hst, tN' hn]; exact lpNatPre h
  · obtain ⟨⟨k1, k2, k3, k4⟩, hq⟩ := hq
    rw [tN' hst, tN' hn] at hq
    obtain ⟨Lk', bk', hlb, htok, e0, e1, e2, hval⟩ := lbOf h hreg hq
    have hpc : s2.pc = BitVec.ofNat 64 0x1bb0c0 := by rw [hr, h.r30]
    have hsp : s2.sp = s.sp - 256#64 := by rw [k1, h.sp]
    have h28 : s2.regs 28 = s.regs 28 := by rw [k2, h.g]
    have h29 : s2.regs 29 = s.sp - 264#64 := by rw [k3, h.fp]
    have h18 : s2.regs 18 = s.regs 18 := by rw [k4, h.x18]
    have a328 := hlb.a328
    obtain ⟨⟨-, ⟨-, -, -, hw0⟩, -⟩, -⟩ := hlb.core.pre
    have hsacc : s2.mem.accessible (s.sp.toNat - 264) 352 true = true := by
      rw [hlb.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
    clear hw0 k1 k2 k3 k4 hr hq
    janus_run [a328] until [0x1bb204]
    refine hK Lk' bk' _ (2 * yl) (2 * yl) _
      ⟨by simpa using hlb, ?pc, ?sp, ?g, ?fp, ?x18, ?r0, ?r1, ?r2, ?r3, by omega, htok, hq0.px, hq0.py, ?val⟩
    case val => rw [Nat.zero_add, Nat.one_mul, Nat.min_eq_left (by omega)]; exact hval
    case r3 => janus_simp
    all_goals janus_simp

end FvModexp.Arm64.NatMul
