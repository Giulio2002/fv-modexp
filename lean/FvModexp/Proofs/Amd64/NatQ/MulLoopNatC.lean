import FvModexp.Proofs.Amd64.NatQ.MulLoopNat
import FvModexp.Proofs.Amd64.NatQ.MulBM

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopNatC.lean — TIGHT COSTS] `nat.mul` (amd64), the chunk loop's prologue: the call `t := stk.nat(2n)` (`0x5f0ba4`) → the loop head, `k = 0`

`mNatSum`: `(*stack).nat` (`StackNatX.sumQ`) as a summary in `LibMul`; `lnat`: from `LP` the call, `lbOf`, the return
`0x5f0ba9` (`DX = n` from `0x110(SP')`, `JMP 0x5f0d39`) ⟹ `LH … 0`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem stkNat_entryM : segAddr Extracted.program StackNat.fn = stkNatM := by decide

/-- `(*stack).nat` (`StackNatX.sumQ`) as a summary in `LibMul.program` -/
theorem mNatSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibMul.program.link impl) stkNatM
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [st, k] ∧ s.df = false ∧ StackNatX.PreQ R b L H 4192 24 st.toNat k.toNat s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        StackNatX.PostQ R b L H 4192 24 st.toNat k.toNat s s') := by
  have hS := StackNatX.sumQ impl hap R hgr hmc hwb H b L st k LibMul.names (IntAS.sub_of_all (by decide))
  rw [← LibMul.eq_only, stkNat_entryM] at hS
  exact hS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`t := stk.nat(2n)`** from `LP` to the loop head with no chunk done -/
theorem lnat (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} {P : State}
    (h : LP R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P) (hx150 : s.xmm 15 = 0#128)
    (hdf0 : s.df = false) {ret : W64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' tp tl tc : Nat) (S : State),
      LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' 0 tp tl tc S →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ReachesRet (LibMul.program.link impl) ret P Q := by
  have hq0 := h.lq
  obtain ⟨hW, hWs, hal, ha48, -, -, -, hcap, hc40, -, hx12, hy12, -⟩ := hq0.lay
  have h40 := hq0.h40; have hlt := hq0.hlt
  have hst : st < 2 ^ 64 := by have := hq0.sok.2.2.2.1; omega
  have hn : 2 * yl < 2 ^ 64 := by omega
  have tst : (BitVec.ofNat 64 st).toNat = st := by simp only [BitVec.toNat_ofNat]; omega
  have tn : (BitVec.ofNat 64 (2 * yl)).toNat = 2 * yl := by simp only [BitVec.toNat_ofNat]; omega
  have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 264 := by
    rw [h.sp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrd : P.mem.readLE (P.regs 4).toNat 8 = 0x5f0840 + 873 := by rw [hspP, h.ra]
  refine ReachesRet.call_regions (mNatSum impl hap R hgr hmc hwb H bk Lk (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 (2 * yl))) h.pc ⟨?_, h.x15.trans hx150, by simp [ArgsFrom64, argReg, intArgRegs, h.r0, h.r3],
      h.df.trans hdf0, ?_⟩ fun s2 hr hq hreg => ?_
  · simp only [regSP]; rw [hrd]; exact ra_mul hap (by decide) 873 (by decide)
  · rw [tst, tn]; exact lpNatPre h
  · obtain ⟨⟨k4, k5, k14, k15⟩, hq⟩ := hq
    rw [tst, tn] at hq
    obtain ⟨Lk', bk', hlb, htok, e0, e3, e1, efs, edf, hval⟩ := lbOf h hreg hq
    have hpc : s2.rip = BitVec.ofNat 64 0x5f0ba9 := by rw [hr, retAddrOf, hrd]
    have hsp : s2.regs 4 = s.regs 4 - 256#64 := by
      rw [k4, h.sp]; apply BitVec.eq_of_toNat_eq
      have e8 : (8 : BitVec 64).toNat = 8 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8]; omega
    have h14 : s2.regs 14 = s.regs 14 := by rw [k14, h.g]
    have h5 : s2.regs 5 = s.regs 4 - 8#64 := by rw [k5, h.bp]
    have hx : s2.xmm 15 = s.xmm 15 := by rw [k15, h.x15]
    have hfs : s2.fsBase = s.fsBase := by rw [efs, h.fs]
    have hdf : s2.df = s.df := by rw [edf, h.df]
    have y110 := hlb.y110
    obtain ⟨⟨-, ⟨-, -, hw0⟩, -⟩, -⟩ := hlb.core.pre
    simp only [regSP] at hw0
    have hsacc : s2.mem.accessible ((s.regs 4).toNat - 256) 344 true = true := by
      rw [hlb.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
    clear hw0 k4 k5 k14 k15 hr hq
    janus64_run [y110] until [0x5f0d39]
    refine hK Lk' bk' _ (2 * yl) (2 * yl) _
      ⟨by simpa using hlb, ?pc, ?sp, ?g, ?bp, ?fs, ?df, ?x15, ?r0, ?r3, ?r1, ?r2, by omega, htok, hq0.px, hq0.py,
        ?val⟩
    case val => rw [Nat.zero_add, Nat.one_mul, Nat.min_eq_left (by omega)]; exact hval
    case fs => exact hfs
    case df => exact h.df
    all_goals janus64_simp

end FvModexp.Amd64.Q.NatMul
