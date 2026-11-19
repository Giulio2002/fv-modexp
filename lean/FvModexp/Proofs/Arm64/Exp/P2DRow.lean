import FvModexp.Proofs.Arm64.Exp.P2Wit
import FvModexp.Proofs.Arm64.Exp.CalleeInstP2Q

set_option autoImplicit false

/-!
# Row: `nat.expNNPowerOfTwo` (arm64) on the Run extraction (agent infra)

`correctness` = `P2D.ens` (`NHyp2.P2HypC`: any `x > 0`, the odd part through the windows, the even part by
`rsh` / recursive call / `lsh`) with the PROVED callees of `CalleeInst` (`(*stack).nat`, `nat.sqr`, `nat.mul`,
`nat.trunc`, `nat.rsh`, `nat.lsh`) and the two window summaries, moved to `Extracted.program.link impl`
(`Ensures.full`); window `[SP - stk, SP + 112)` for `71776 ≤ stk ≤ 2^20 + 576`. Runtime premises: the live
`growslice`, `memclrNoHeapPointers`, `memmove`, `makeslice`, `newobject`, `gcWriteBarrier2` contracts.
`Witness.nonvacuous`: the shared witness memory `P2Wit` (`3^5 mod 2^8`, `z = nil`, the stack `{w, 0, 4}`),
`stk = 71776`, one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2DRow

open FvModexp.Arm64.CalleeInstQ FvModexp.Arm64.P2WitQ FvModexp.Arm64.NHyp FvModexp.Arm64.ExpHyp

/-- the precondition (= `NHyp2.P2HypC`'s, stack need `2^13`, budget `P2D.cP sqrCQ mulCQ`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (z zl zc st x xl xc y yl lm : Nat)
    (s : State) : Prop :=
  (CPre R b L stk 112 z zl zc st [(x, xl), (y, yl)] (P2D.needP xl yl lm) (P2D.cP sqrCQ mulCQ (stLen s.mem st) xl yl lm) s ∧
    0 < natVal s.mem x xl ∧ 0 < natVal s.mem y yl ∧ 1 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk 112 ++ [(z, z + 8 * zc)] ++ stWs s.mem st) ∧
      EvenHyp.StkApart s.mem st op 8) ∧ xl ≤ xc ∧ xc < 2 ^ 40

/-- the postcondition: `CPostR` with the value `x^y mod 2^logM` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (z zc st x xl y yl lm : Nat)
    (s s' : State) : Prop :=
  CPostR R b L stk 112 z zc st (natVal s.mem x xl ^ natVal s.mem y yl % 2 ^ lm)
    (P2D.cP sqrCQ mulCQ (stLen s.mem st) xl yl lm) s s'

/-- **`nat.expNNPowerOfTwo`** (arm64): `z.expNNPowerOfTwo(stk, x, y, logM)` returns `x^y mod 2^logM` for every
`x > 0`, `y > 0`, `1 ≤ logM ≤ 2^13` (`Pre` / `Post`), for every runtime meeting the live allocation / copy / clear /
write-barrier contracts. -/
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
    (stk : Nat) (hk1 : 71776 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 576)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc lm : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program NHyp.fnP2)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, lm]
      (Pre R b L stk z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat lm.toNat)
      (Post R b L stk z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat lm.toNat) := by
  have hW := CalleeInst.sqrWX_eq
  exact Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.P2DRow.Pre, FvModexp.Arm64.NHyp.CPre, FvModexp.stLen, FvModexp.natVal, FvModexp.Arm64.EvenHyp.NatOne, FvModexp.Arm64.win, FvModexp.Arm64.ExpHyp.stWs, FvModexp.Arm64.EvenHyp.StkApart, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.StackNat.wT, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, FvModexp.Arm64.NHyp.freeOf, FvModexp.Arm64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.StackNat.wbA, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.EvenHyp.natOneA, FvModexp.stkWs, FvModexp.Asm.top, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]) hap (P2D.ens hap sub nf2 nf4 nfP nfD hgr hmc hmv hmk hno hwb (kcP := NatSqr.sqrWX) (by omega)
    (sn hap hgr hmc hwb) (by omega) (by omega) (sq hap hgr hmc hmv hmk hwb) (Nat.le_refl _) (by omega) sqm
    (mu hap hgr hmc hmv hmk hwb) (by rw [CalleeInst.mulWX_eq]; omega) (by omega) mum (tr hap hmv hmk) (by omega) (by omega)
    (rh hap hmv hmk) (by omega) (lh hap hmc hmv hmk) (by omega) stk (by omega) hk2 (by omega) (by omega)
    b L z zl zc st x xl xc y yl yc lm)

end FvModexp.Arm64.P2DRow

namespace FvModexp.Arm64.P2DRow.Witness

open Janus.Contracts.Toy FvModexp.Arm64.AsmWit FvModexp.Arm64.ExpWit FvModexp.Arm64.EvenHyp FvModexp.Arm64.NHyp
open FvModexp.Arm64.ExpHyp

set_option maxRecDepth 100000

abbrev KW : Nat := 71776

def args : List (BitVec 64) :=
  [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1, 8]

abbrev s0 : State := mkS (segAddr Extracted.program NHyp.fnP2) args

theorem g0 : (s0.regs 28).toNat = G0 := by decide

theorem bud : P2D.cP sqrCQ mulCQ 0 1 1 8 ≤ BW := by decide +kernel

/-- the two inputs `x = [3]`, `y = [5]` are readable, held, outside the window, apart from the stack -/
theorem insOK : ∀ p n, (p, n) ∈ [(XP, 1), (YP, 1)] → RdIn R [] s0 KW 112 p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s0.mem p n ∧
    Apart p (8 * n) ST 24 ∧ Apart p (8 * n) (freeOf s0.mem ST).1 (freeOf s0.mem ST).2 ∧
    (0 < 0 → Apart 0 (8 * 0) p (8 * n)) := by
  have hm : s0.mem = mem0 := rfl
  intro p n hpn
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpn
  simp only [RdIn, freeOf, win, hm, stW0, stLen0, stCap0, mkS_sp]
  rcases hpn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨⟨by decide, by rw [acc0]; decide +kernel, by decide,
      Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide),
      by simp only [outside_cons, outside_nil, and_true]; decide⟩, by decide, by simp only [NatNorm]; decide +kernel,
      by simp only [Apart]; decide, by simp only [Apart]; decide, fun h => absurd h (by decide)⟩

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`3^5 mod 2^8`) at `stk = 71776` -/
theorem pre : Pre R BW [] KW 0 0 0 ST XP 1 1 YP 1 8 s0 := by
  have hm : s0.mem = mem0 := rfl
  unfold Pre CPre
  rw [hm, stLen0]
  simp only [win, WrOut, RdIn, freeOf, g0, mkS_sp, stW0, stLen0, stCap0]
  refine ⟨⟨?_, by decide +kernel, by decide +kernel, by decide, by decide, by decide, ?_⟩, by decide, by decide⟩
  · repeat' apply And.intro
    all_goals first
      | decide
      | exact accWin _ _ (by decide) (by decide)
      | exact dataLoaded _ _
      | exact WStubs.serves []
      | exact roOut
      | exact inv1 _
      | (intro h; exact absurd h (by decide))
      | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [LiveSep, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, rt_eq, outside_cons, outside_nil, and_true, SP0, HEAP, HEND, HSIZE, BUMP, WBUF]; omega)
      | (intro r hr; simp at hr; done)
      | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [rt_eq]
         simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | trivial
      | (intros; trivial)
      | (simp only [Apart, gA_eq, wbA_eq]; decide)
      | (simp only [GuardOK, StackOK, acc0]; decide +kernel)
      | (decide +kernel)
      | (rw [acc0]; decide +kernel)
      | (simp only [StkOK, NatLive, Held, InRanges, outside_cons, outside_nil, and_true, rt_eq, acc0, stW0, stLen0,
          stCap0]; decide +kernel)
      | exact insOK
      | (intro _; exact ⟨by simp only [outside_cons, outside_nil, and_true]; decide +kernel,
          by simp only [Apart]; decide⟩)
      | (simp only [Globals, RunIface.Globals, gA_eq, wbA_eq]; decide +kernel)
      | skip
  · exact ⟨OP, one0 [] _ (by simp only [stWs, stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append,
      outside_cons, outside_nil, and_true]; decide)
      (by simp only [stWs, stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true]; decide), sa0⟩

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, `stk = 71776`, the call `z.expNNPowerOfTwo(stk, 3, 5, 8)` with `z = nil` and the stack
`{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (stk b : Nat) (L : List (Nat × Nat))
    (z zl zc st x xl xc y yl yc lm : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    71776 ≤ stk ∧ stk ≤ 2 ^ 20 + 576 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program NHyp.fnP2)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, lm] s ∧
    Pre R b L stk z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat lm.toNat s ∧
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
      ABIReturn (s.setRet ret) s' ∧ Post R b L stk z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat lm.toNat (s.setRet ret) s' :=
  ⟨WStubs.impl, R, KW, BW, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1, 8,
    RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, Nat.le_refl _, by decide, hret,
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
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) KW (Nat.le_refl _) (by decide)
      BW [] 0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 (BitVec.ofNat 64 YP) 1 1 8 s0
      (setup _ args (by decide)) pre RET hret⟩

end FvModexp.Arm64.P2DRow.Witness
