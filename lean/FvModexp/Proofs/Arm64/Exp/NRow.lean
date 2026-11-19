import FvModexp.Proofs.Arm64.Exp.IExpClE
import FvModexp.Proofs.Arm64.NatQ.RemC
import FvModexp.Proofs.Arm64.Exp.EvenNHyp
import FvModexp.Proofs.Arm64.Witness.StubsMvz
import FvModexp.Proofs.Arm64.Int.ModRowW

set_option autoImplicit false

/-!
# Row: `nat.expNN` (arm64), `slow = false`, `m` odd or a power of two, on the Run extraction (agent infra, s60)

`correctness` = expmc's `ExpN.ens_noEven` (window 70720) lifted to the whole program (`Ensures.full`), with EVERY callee
proved: the closed TIGHT-COSTS callee shapes `IExp.dhypsQ` (asm's `Q.NatDiv.ensCLG`, expmc's Q-form `expNNSlow`,
infra's `expNNPowerOfTwo`) and asm's `Q.NatRem.ensCR`. Also exports `hNE` (the closed `EvenHyp.ExpNNHypNE`, i.e. the
inner `nat.expNN` calls of `nat.expNNEven`), so that arm64 Exp/EvenRow imports this row instead of compiling the
expNN / expNNSlow chains itself (release order: this row right before Exp/EvenRow; EvenRow own-set cut).
Runtime premises: the live `makeslice`, `growslice`, `memclrNoHeapPointers`, `memmove` (+ zero-length), `newobject`,
`gcWriteBarrier2` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NRow

abbrev cF : Nat → Nat → Nat → Nat := IExp.clFQ
abbrev cR : Nat → Nat → Nat → Nat := IExp.clRQ
abbrev cS : Nat → Nat → Nat → Nat → Nat := IExp.clSQ
abbrev cP : Nat → Nat → Nat → Nat → Nat := P2D.cP sqrCQ mulCQ

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closed inner `nat.expNN` (no even path) at window `70720`, as `nat.expNNEven`'s callee shape -/
theorem hNE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    EvenHyp.ExpNNHypNE impl R 70720 cF NatRem.need cR ExpSlow.need P2D.needP cS cP := by
  have hDN := IExp.dhypsQ hap hmk hgr hmc hmv hno hwb (Q.NatDiv.ensCLG impl hap R hgr hmc hwb hmk hmv hmz)
    (K := 70720) (Nat.le_refl _)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need cR :=
    Q.rem_of_Q (Q.NatRem.ensCR impl hap R hgr hmc hwb hmk hmv hmz)
  exact fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
    ExpN.ens_noEven impl hap R hDN hRem IExp.rem_n IExp.rem_11 (by decide) b L zp zl zc st xp xl xc yp yl yc mp n
      mc slow

/-- the precondition (= `ExpN.Pre` at window `70720` with the closed costs) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  ExpN.Pre R b L 70720 cF NatRem.need cR ExpSlow.need P2D.needP cS cP zp zl zc st xp xl xc yp yl yc mp n mc slow s

/-- the postcondition (= `ExpN.Post`): `x^y mod m`, normalised, in `z`'s array or a fresh one -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc st xp xl yp yl mp n : Nat)
    (s s' : State) : Prop :=
  ExpN.Post R b L 70720 cF cR cS cP zp zc st xp xl yp yl mp n s s'

set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`** (arm64): `z.expNN(stk, x, y, m, false)` with `stk ≠ nil` and `m` odd or a power of two returns
`x^y mod m` (`Pre` / `Post`), for every runtime meeting the live allocation / copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m n mc slow : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN")
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, n, mc, slow]
      (Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat m.toNat n.toNat
        mc.toNat slow.toNat)
      (Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat m.toNat n.toNat) := by
  have h := hNE impl hap R hmk hgr hmc hmv hmz hno hwb b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat
    xc.toNat y.toNat yl.toNat yc.toNat m.toNat n.toNat mc.toNat slow.toNat
  simp only [Expmc.bv_ofNat_toNat] at h
  exact Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.NRow.Pre]) hap h

end FvModexp.Arm64.NRow

namespace FvModexp.Arm64.NRow.Witness

open Janus.Contracts.Toy FvModexp.Arm64.AsmWit FvModexp.Arm64.ExpWit FvModexp.Arm64.EvenHyp FvModexp.Arm64.NHyp
open FvModexp.Arm64.ExpHyp

set_option maxRecDepth 100000

abbrev KW : Nat := 70720

/-- `z = nil`, `stk = ST`, `x = [3]`, `y = [5]`, `m = [5]` (the `y` words: odd), `slow = false` -/
def args : List (BitVec 64) :=
  [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1, BitVec.ofNat 64 YP, 1, 1, 0]

abbrev s0 : State :=
  mkS (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN") args

theorem g0 : (s0.regs 28).toNat = G0 := by decide

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`3^5 mod 5`) at `K = 70720` -/
theorem pre : Pre R BW [] 0 0 0 ST XP 1 1 YP 1 1 YP 1 1 0 s0 := by
  have hm : s0.mem = mem0 := rfl
  unfold Pre ExpN.Pre ExpN.NPre XFacts
  rw [hm, stLen0]
  simp only [g0, mkS_sp, stW0, stLen0, stCap0]
  refine ⟨?_, Or.inl (by decide +kernel), ?_⟩
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
      | (simp only [LiveSep, BitVec.toNat_ofNat, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, rt_eq, outside_cons, outside_nil, and_true, SP0, HEAP, HEND, HSIZE, BUMP, WBUF]
         omega)
      | (intro r hr; simp at hr; done)
      | exact Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | trivial
      | (intros; trivial)
      | (simp only [Apart, gA_eq, wbA_eq]; decide)
      | (simp only [Apart, freeOf, W4En.free, stW0, stCap0, stLen0]; decide)
      | (simp only [GuardOK, StackOK, acc0]; decide +kernel)
      | (decide +kernel)
      | (rw [acc0]; decide +kernel)
      | (simp only [StkOK, NatLive, Held, InRanges, outside_cons, outside_nil, and_true, rt_eq, acc0, stW0, stLen0,
          stCap0]; decide +kernel)
      | (simp only [NatNorm]; decide +kernel)
      | (simp only [Globals, RunIface.Globals, gA_eq, wbA_eq]; decide +kernel)
      | exact ⟨OP, one0 [] _ (by simp only [stWs, stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append,
          outside_cons, outside_nil, and_true]; decide)
          (by simp only [stWs, stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append, outside_cons,
            outside_nil, and_true]; decide), sa0⟩
      | skip
  · refine ⟨⟨by decide, by decide, fun _ => ⟨Or.inr ?_, by decide⟩⟩, fun _ => by simp only [Apart, gA_eq]; decide⟩
    rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, the call `z.expNN(stk, 3, 5, 5, false)` with `z = nil` and the stack `{w, 0, 4}`; one call-site
state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z zl zc st x xl xc y yl yc m n mc slow : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN")
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, n, mc, slow] s ∧
    Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat m.toNat n.toNat
      mc.toNat slow.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
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
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      (s_c.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s_c ∧
      LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
        (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3)) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      ExpWit.noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat m.toNat n.toNat (s.setRet ret) s' :=
  ⟨WStubs.impl, R, BW, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1,
    BitVec.ofNat 64 YP, 1, 1, 0, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret,
    setup _ args (by decide), pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact AsmWit.site_mz _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact ExpWit.site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _)
      BW [] 0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 (BitVec.ofNat 64 YP) 1 1 (BitVec.ofNat 64 YP) 1 1 0 s0 (setup _ args (by decide)) pre RET
      hret⟩


end FvModexp.Arm64.NRow.Witness
