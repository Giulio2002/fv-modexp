import FvModexp.Proofs.Arm64.Exp.CalleeInstP2Q
import FvModexp.Proofs.Arm64.Exp.P2Nf
import FvModexp.Proofs.Arm64.Exp.P2W4E

set_option autoImplicit false

/-!
# Row: `nat.expNNPowerOfTwoWindowSize4` (arm64) on the Run extraction (agent infra)

`correctness` = `P2W4.ens` with the PROVED callees of `CalleeInst` (`(*stack).nat`, `nat.sqr`, `nat.mul`, `nat.trunc`),
moved to `Extracted.program.link impl` (`Ensures.full`), window depth `K ≥ 208 + sqrWX`. Runtime premises: the live
`growslice`, `memclrNoHeapPointers`, `memmove`, `makeslice`, `newobject`, `gcWriteBarrier2` contracts.
`Witness.nonvacuous`: the shared witness memory `P2Wit` (`3^5 mod 2^8`, `z = nil`, the stack `{w, 0, 4}`), window
depth `K = 70800`, one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4Row

open FvModexp.Arm64.CalleeInstQ FvModexp.Arm64.P2WitQ

/-- **window-4 power-of-two** (arm64): `z.expNNPowerOfTwoWindowSize4(stk, x, y, logM)` returns `x^y mod 2^logM` for
odd `x`, `y > 0`, `2 ≤ logM ≤ 2^13` (`P2W4.Pre` / `Post`), for every runtime meeting the live allocation / copy /
clear / write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hK : 70800 ≤ K)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program P2W4.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 lm]
      (P2W4.Pre R b L K sqrCQ mulCQ zp zc st xp xl xc yp yl lm)
      (P2W4.Post R b L K sqrCQ mulCQ zp zc st xp xl yp yl lm) := by
  have hW := CalleeInst.sqrWX_eq
  exact Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.P2W4.Pre, FvModexp.Arm64.P2W4.EPre, FvModexp.natVal, FvModexp.stLen, FvModexp.Arm64.P2W4.EEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.StackNat.wT, FvModexp.Arm64.P2W4.OE, FvModexp.NatNorm, FvModexp.Arm64.RunIface.gA, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.StackNat.wbA, FvModexp.Arm64.P2W4.free, FvModexp.Arm64.EvenHyp.NatOne, FvModexp.stkWs, FvModexp.Arm64.EvenHyp.StkApart, FvModexp.stkR, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.Arm64.EvenHyp.natOneA, FvModexp.stkRes, FvModexp.potK]) hap (P2W4.ens hap sub nf4 nfP hgr hmc hmv hmk hno hwb (kcP := NatSqr.sqrWX) (by omega)
    (sn hap hgr hmc hwb) (by omega) (by omega) (sq hap hgr hmc hmv hmk hwb) (Nat.le_refl _) (by omega) sqm
    (mu hap hgr hmc hmv hmk hwb) (by rw [CalleeInst.mulWX_eq]; omega) (by omega) mum (tr hap hmv hmk) (by omega) (by omega)
    b L K (by omega) zp zl zc st xp xl xc yp yl yc lm)

end FvModexp.Arm64.P2W4Row

namespace FvModexp.Arm64.P2W4Row.Witness

open Janus.Contracts.Toy FvModexp.Arm64.AsmWit FvModexp.Arm64.ExpWit FvModexp.Arm64.P2W4 FvModexp.Arm64.EvenHyp

set_option maxRecDepth 100000

abbrev KW : Nat := 70800

def args : List (BitVec 64) :=
  [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1, 8]

abbrev s0 : State := mkS (segAddr Extracted.program P2W4.fn) args

theorem sp0 : s0.sp.toNat - 752 = SP0 - 752 := by decide
theorem g0 : (s0.regs 28).toNat = G0 := by decide

/-- (divmc s42) the effective budget: `BW` less the unheld stack reserve of the call -/
abbrev BWQ : Nat := BW - stkR (P2W4.HW 0 8) mem0 ST

theorem bwq : BWQ + stkR (P2W4.HW 0 8) mem0 ST = BW := Nat.sub_add_cancel (by decide +kernel)

theorem bud : P2W4.cost sqrCQ mulCQ 0 1 8 ≤ BWQ := by decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies window-4's precondition (`3^5 mod 2^8`) at window depth `70800` -/
theorem pre : P2W4.Pre R BWQ [] KW sqrCQ mulCQ 0 0 ST XP 1 1 YP 1 8 s0 := by
  have hm : s0.mem = mem0 := rfl
  unfold P2W4.Pre
  rw [hm, stLen0]
  unfold EPre EEnv
  rw [g0, sp0]
  simp only [hm, stW0, stLen0, stCap0]
  refine ⟨?_, by decide +kernel, by decide +kernel, bud⟩
  repeat' apply And.intro
  all_goals first
    | decide
    | exact accWin _ _ (by decide) (by decide)
    | exact dataLoaded _ _
    | exact WStubs.serves []
    | exact roOut
    | exact inv1 _
    | (rw [bwq]; exact inv1 _)
    | trivial
    | (intros; trivial)
    | exact ⟨OP, one0 [] _ (by simp only [stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append, outside_cons,
          outside_nil, and_true]; decide)
        (by simp only [stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append, outside_cons, outside_nil,
          and_true]; decide), sa0⟩
    | (intro h; exact absurd h (by decide))
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [LiveSep, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        rt_eq, outside_cons, outside_nil, and_true, SP0, HEAP, HEND, HSIZE, BUMP, WBUF]; omega)
    | (intro r hr; simp at hr; done)
    | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [rt_eq]
       simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart, free, gA_eq, wbA_eq, stW0, stLen0, stCap0]; decide)
    | (simp only [OE, Apart, free, InRanges, gA_eq, rt_eq, outside_cons, outside_nil, and_true, stW0, stLen0, stCap0];
        decide +kernel)
    | (decide +kernel)
    | (rw [acc0]; decide +kernel)
    | (simp only [NatNorm]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, InRanges, stW0, stLen0, stCap0, outside_cons, outside_nil, and_true, rt_eq,
        acc0]; decide +kernel)
    | skip

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, window depth `70800`, the call `z.expNNPowerOfTwoWindowSize4(stk, 3, 5, 8)` with
`z = nil` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    70800 ≤ K ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program P2W4.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 lm] s ∧
    P2W4.Pre R b L K sqrCQ mulCQ zp zc st xp xl xc yp yl lm s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ P2W4.Post R b L K sqrCQ mulCQ zp zc st xp xl yp yl lm (s.setRet ret) s' :=
  ⟨WStubs.impl, R, BWQ, [], KW, 0, 0, 0, ST, XP, 1, 1, YP, 1, 1, 8, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, Nat.le_refl _, hret,
    setup _ args (by decide), pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) BWQ [] KW (Nat.le_refl _)
      0 0 0 ST XP 1 1 YP 1 1 8 s0 (setup _ args (by decide)) pre RET hret⟩

end FvModexp.Arm64.P2W4Row.Witness
