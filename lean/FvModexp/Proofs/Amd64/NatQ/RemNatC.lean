import FvModexp.Proofs.Amd64.NatQ.RemSN
import FvModexp.Proofs.Amd64.Nat.StackNatX
import FvModexp.Proofs.Amd64.Int.IntASCallH

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): `CALL (*stack).nat` (twin of the `natc` step of Arm64/NatQ/RemCall.lean; divmc s58)

From `AtNat s P` (`P` at the `CALL`, `RSP = r - 200`): the push, the callee (`StackNatX.sumQ` in `LibRem`, pre `sn_pre`),
and the return state `T` at `0x5edd9e` with `sn_of`'s facts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

open FvModexp.Amd64.NHyp (RemPreQ)

variable {H : Nat}

/-- the entry of `(*stack).nat` -/
abbrev stkNatR : Nat := 0x5e6480

theorem stkNat_entryR : segAddr Extracted.program StackNat.fn = stkNatR := by decide

set_option maxRecDepth 20000 in
/-- a return address inside `nat.rem` (segment `seg19`, base `0x5edca0`) -/
theorem rem_ra {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x229) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x5edca0 + i) := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg19) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5edca0 + i < 2 ^ 47; omega)
  rw [show Extracted.seg19.base = 0x5edca0 from rfl] at this; exact this

/-- `(*stack).nat` (`StackNatX.ensQ`) as a summary in `LibRem.program` -/
theorem remNatSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibRem.program.link impl) stkNatR
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [st, k] ∧ s.df = false ∧ StackNatX.PreQ R b L H 4192 24 st.toNat k.toNat s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        StackNatX.PostQ R b L H 4192 24 st.toNat k.toNat s s') := by
  have hS := StackNatX.sumQ impl hap R hgr hmc hwb H b L st k LibRem.names (IntAS.sub_of_all (by decide))
  rw [← LibRem.eq_only, stkNat_entryR] at hS
  exact hS

theorem tN64 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`CALL (*stack).nat`** from `AtNat s P`; the continuation gets the return state `T` (`RSP = r - 200`) -/
theorem natc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b c : Nat} {L : List (Nat × Nat)} {zp zl zc st up ul uc vp vl vc : Nat} {s P : State}
    (hpre : RemPreQ R b H L 41720 112 zp zl zc st up ul uc vp vl vc (need ul vl) (c + stkR H s.mem st) s)
    (hP : AtNat s P zp zl zc st up ul uc vl) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ T : State, T.rip = BitVec.ofNat 64 (callNat + 5) → T.regs 4 = s.regs 4 - 200#64 →
      T.regs 5 = s.regs 4 - 8#64 → T.regs 14 = s.regs 14 → T.xmm 15 = s.xmm 15 → T.fsBase = s.fsBase →
      T.df = s.df → T.mem.regions = s.mem.regions →
      T.regs 0 = BitVec.ofNat 64 (stW T.mem st + 8 * stLen s.mem st) →
      T.regs 3 = BitVec.ofNat 64 (kq ul vl) → T.regs 1 = BitVec.ofNat 64 (kq ul vl) →
      Sl s zp zl zc st up ul uc T.mem →
      ∀ (L1 : List (Nat × Nat)) (b1 : Nat), SN R b H L st (kq ul vl) s T.mem L1 b1 →
      ReachesRet (LibRem.program.link impl) ret T Q) :
    ReachesRet (LibRem.program.link impl) ret P Q := by
  have hpre' := hpre
  obtain ⟨-, hce, -, -, -, -, -, -, -, ⟨-, -, -, hst48, -⟩, -⟩ := hpre'
  obtain ⟨-, ⟨hb', -, hw⟩, hal, -⟩ := hce
  simp only [regSP] at hb' hw hal
  obtain ⟨hpc, hsp, h5, h14, hfs, hx15, hdf, h0, h3, hF, hreg, hsl⟩ := hP
  have hspN : (P.regs 4).toNat = (s.regs 4).toNat - 200 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hacc : P.mem.accessible ((s.regs 4).toNat - 41720) (41720 + 112) true = true := by
    rw [hF.accessible]; exact hw
  have hst : st < 2 ^ 64 := by omega
  have hkq : kq ul vl < 2 ^ 64 := by
    have := (hpre.2.2.2.2.2.2.2.2.1 up ul (by simp)).2.1; simp only [kq]; omega
  have h41 : 41720 ≤ (s.regs 4).toNat := by omega
  clear hw
  janus64_run until [stkNatR]
  have hM : ∀ S : State, S.mem = Janus.Arm64.Memory.writeLE P.mem ((s.regs 4).toNat - 208) 8 6217118 →
      S.regs 4 = s.regs 4 - 208#64 → S.regs 14 = s.regs 14 → S.fsBase = s.fsBase → S.df = false → S.xmm 15 = 0 →
      S.rip = BitVec.ofNat 64 stkNatR → S.regs 0 = BitVec.ofNat 64 st → S.regs 3 = BitVec.ofNat 64 (kq ul vl) → S.regs 5 = s.regs 4 - 8#64 →
      ReachesRet (LibRem.program.link impl) ret S Q := by
    intro S eM e4 e14 efs edf ex15 erip e0 e3 e5
    have hFp : MemFrame P.mem (Janus.Arm64.Memory.writeLE P.mem ((s.regs 4).toNat - 208) 8 6217118)
        [((s.regs 4).toNat - 208, (s.regs 4).toNat - 208 + 8)] := by janus_frame
    have hFS : MemFrame s.mem (Janus.Arm64.Memory.writeLE P.mem ((s.regs 4).toNat - 208) 8 6217118) (fw s) :=
      hF.trans hFp fun a n ho => ⟨ho, by simp only [fw, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
    have hregS : (Janus.Arm64.Memory.writeLE P.mem ((s.regs 4).toNat - 208) 8 6217118).regions = s.mem.regions := by
      rw [Janus.Arm64.Memory.regions_writeLE]; exact hreg
    have hspS : (s.regs 4 - 208#64).toNat = (s.regs 4).toNat - 208 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    have hslS := hsl.frame hFp (fun a n h1 h2 => by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)
    have hrd : (Janus.Arm64.Memory.writeLE P.mem ((s.regs 4).toNat - 208) 8 6217118).readLE
        ((s.regs 4).toNat - 208) 8 = 0x5edca0 + 0xfe := by janus64_simp
    rw [← eM] at hFS hregS hrd hslS
    have hspS' : (S.regs 4).toNat = (s.regs 4).toNat - 208 := by rw [e4]; exact hspS

    refine ReachesRet.call_regions (remNatSum impl hap R hgr hmc hwb H b L (BitVec.ofNat 64 st)
      (BitVec.ofNat 64 (kq ul vl))) erip ⟨?ra, ?x15, ?args, ?df, ?pre⟩ fun T hr hq hTreg => ?_
    case ra =>
      simp only [regSP]; rw [hspS', hrd]; exact rem_ra hap (by decide) 0xfe (by decide)
    case x15 => exact ex15
    case args => simp [ArgsFrom64, argReg, intArgRegs, e0, e3]
    case df => exact edf
    case pre =>
      rw [tN64 hst, tN64 hkq]
      exact sn_pre hpre hspS' e14 efs hFS hregS
    obtain ⟨⟨k4, k5, k14, k15⟩, hpost⟩ := hq
    rw [tN64 hst, tN64 hkq] at hpost
    obtain ⟨f1, f2, q0, q1, q2, hslT, L1, b1, hSN⟩ := sn_of hpre hspS' e14 hFS hregS hslS hTreg hpost
    refine hK T ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q0 q1 q2 hslT L1 b1 hSN
    · rw [hr, retAddrOf_eq, hspS', hrd]
    · rw [k4, e4]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hspS, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]; rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · rw [k5]; exact e5
    · rw [k14]; exact e14
    · rw [k15, ex15, hx150]; rfl
    · rw [f1]; exact efs
    · rw [f2, edf, hdf0]
    · rw [hTreg, hregS]
  exact hM _ rfl (by simp [setRegF]) (by simp [setRegF]; exact h14) hfs (by first | rfl | exact hdf.trans hdf0)
    (by show P.xmm 15 = 0; rw [hx15, hx150]; rfl) rfl (by simp [setRegF]; exact h0) (by simp [setRegF]; exact h3)
    (by simp [setRegF]; exact h5)

end FvModexp.Amd64.Q.NatRem
