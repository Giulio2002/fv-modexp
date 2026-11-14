import FvModexp.Proofs.Arm64.Exp.IExpClD
import FvModexp.Proofs.Arm64.Exp.EvInst
import FvModexp.Proofs.Arm64.Exp.NCap
import FvModexp.Proofs.Arm64.NatQ.RemC
import FvModexp.Proofs.Common.NCostU
import FvModexp.Proofs.Arm64.Witness.StubsMvz
import FvModexp.Proofs.Arm64.Int.ModRowW

set_option autoImplicit false

/-!
# Row: `nat.expNNEven` (arm64) on the Run extraction (agent infra)

`correctness` = `ExpEven.fullI` (the CRT split `m = 2^n · m2`: two inner `nat.expNN` calls, `subMod2N`,
`modularInverseModPowerOfTwo`, two `mul`s, `trunc`, `add`) with EVERY callee proved: the inner `nat.expNN` is expmc's
`ExpN.ens_noEven` (window 70720) on the closed TIGHT-COSTS callee shapes `IExp.dhypsQ` (asm's `Q.NatDiv.ensCLG`,
expmc's Q-form `expNNSlow`, infra's `expNNPowerOfTwo`; expmc s69: no old `nat.sqr` SCC) and asm's `Q.NatRem.ensCR`; the cost bounds `bU`/`cU` are the dominating box maxima `Exp.supU` (expmc's
`Common/NCostU`, as top's `Run.Closed.expC`); the need monotonicity facts are proved here (copied from top's RunOkRowC).
Window `[SP - 72368, SP + 112)`. Runtime premises: the live `makeslice`, `growslice`, `memclrNoHeapPointers`,
`memmove` (+ zero-length), `newobject`, `gcWriteBarrier2` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenRow

abbrev cF : Nat → Nat → Nat → Nat := IExp.clFQ
abbrev cR : Nat → Nat → Nat → Nat := IExp.clRQ
abbrev cS : Nat → Nat → Nat → Nat → Nat := IExp.clSQ
abbrev cP : Nat → Nat → Nat → Nat → Nat := P2D.cP sqrCQ mulCQ
abbrev bUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpEven.NBudE cF cR cS cP)
abbrev cUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpN.NCost cF cR cS cP)
/-- `nat.expNNEven`'s stack need and cost -/
abbrev nE : Nat → Nat → Nat → Nat := ExpEven.needE NatRem.need ExpSlow.need P2D.needP
abbrev cE : Nat → Nat → Nat → Nat → Nat := ExpEven.costE cF cR cS cP bUC cUC sqrCQ mulCQ (ExpEven.mulBrE mulCQ)

/-- (copied from top's `Run.Closed.rem_mono`) -/
theorem rem_mono : ∀ x a a', a ≤ a' → NatRem.need x a ≤ NatRem.need x a' := fun _ _ _ _ => by
  simp only [NatRem.need]; omega

/-- (copied from top's `Run.Closed.slow_mono`) -/
theorem slow_mono : ∀ x y a a', a ≤ a' → ExpSlow.need x y a ≤ ExpSlow.need x y a' := fun x _ a a' h => by
  simp only [ExpSlow.need]
  by_cases h1 : x ≤ 128 ∧ a' ≤ 128
  · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]; exact Nat.le_refl _
  · rw [if_neg h1]; split <;> omega

theorem p2_mono : ∀ x y a a', a ≤ a' → P2D.needP x y a ≤ P2D.needP x y a' := fun _ _ _ _ _ => Nat.le_refl _

theorem fnE_eq : segAddr Extracted.program ExpEven.fn = ExpEven.fnE := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.expNNEven` as a closed summary on `LibNE` (window 72368) -/
theorem sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ExpEven.EvenSum impl R 72368 112 nE cE := by
  have hDN := IExp.dhypsQ hap hmk hgr hmc hmv hno hwb (Q.NatDiv.ensCLG impl hap R hgr hmc hwb hmk hmv hmz)
    (K := 70720) (Nat.le_refl _)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need cR :=
    Q.rem_of_Q (Q.NatRem.ensCR impl hap R hgr hmc hwb hmk hmv hmz)
  have hNE : EvenHyp.ExpNNHypNE impl R 70720 cF NatRem.need cR ExpSlow.need P2D.needP cS cP :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem IExp.rem_n IExp.rem_11 (by decide) b L zp zl zc st xp xl xc yp yl yc mp n
        mc slow
  exact ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by decide) (by decide)
    rem_mono slow_mono p2_mono (bU := bUC) (cU := cUC) (Exp.dom _) (Exp.dom _) (stk := 72368) (by decide) (by decide)
    (by decide)

/-- the precondition (= `EvenSum`'s, window `72368`/`112`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl m ml mc : Nat)
    (s : State) : Prop :=
  ExpEven.Pre R b L 72368 112 nE cE z zl zc st x xl y yl m ml mc s ∧ NHyp.XFacts R L x xl xc

/-- the postcondition: the ABI registers kept and `CPostR` with the value `x^y mod m` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z zc st x xl y yl m ml : Nat) (s s' : State) :
    Prop :=
  ExpEven.Post R b L 72368 112 cE z zc st x xl y yl m ml s s'

set_option maxHeartbeats 64000000 in
/-- **`nat.expNNEven`** (arm64): `z.expNNEven(stk, x, y, m)` returns `x^y mod m` for every `x > 0`, `y ≥ 2`, even
`m > 0` of at most 128 words (`Pre` / `Post`), for every runtime meeting the live allocation / copy / clear /
write-barrier contracts. -/
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
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ExpEven.fn)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc]
      (Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat m.toNat ml.toNat
        mc.toNat)
      (Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat m.toNat ml.toNat) := by
  have hS := sum impl hap R hmk hgr hmc hmv hmz hno hwb
  refine Ensures.full (ns := LibNE.names) hap ?_
  rw [← LibNE.eq_only, fnE_eq]
  intro ret hret s hs hpre
  janus_intro hs
  have hr4 : (s.regs 30).toNat % 4 = 0 := by
    rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; have := hret.aligned; omega
  have hr48 : (s.regs 30).toNat < 2 ^ 48 := by rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; omega
  have bv := Expmc.bv_ofNat_toNat
  exact Summary.returns (hS b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat
      yc.toNat m.toNat ml.toNat mc.toNat) hret h_pc h_lr
    ⟨h_x0.trans (bv _).symm, h_x1.trans (bv _).symm, h_x2.trans (bv _).symm, h_x3.trans (bv _).symm,
      h_x4.trans (bv _).symm, h_x5.trans (bv _).symm, h_x6.trans (bv _).symm, h_x7.trans (bv _).symm,
      h_x8.trans (bv _).symm, h_x9.trans (bv _).symm, h_x10.trans (bv _).symm, h_x11.trans (bv _).symm,
      h_x12.trans (bv _).symm, hpre.1, z.isLt, xc.isLt, yc.isLt, hr4, hr48, hpre.2⟩
    fun s' hq => ⟨⟨hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.1⟩, hq⟩

end FvModexp.Arm64.EvenRow

namespace FvModexp.Arm64.EvenRow.Witness

open Janus.Contracts.Toy FvModexp.Arm64.AsmWit FvModexp.Arm64.ExpWit FvModexp.Arm64.EvenHyp FvModexp.Arm64.NHyp
open FvModexp.Arm64.ExpHyp

set_option maxRecDepth 100000

abbrev KW : Nat := 72368

def args : List (BitVec 64) :=
  [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1, BitVec.ofNat 64 MP, 1, 1]

abbrev s0 : State := mkS (segAddr Extracted.program ExpEven.fn) args

theorem g0 : (s0.regs 28).toNat = G0 := by decide

theorem bud : cE 0 1 1 1 ≤ BW := by decide +kernel

/-- the three inputs `x = [3]`, `y = [5]`, `m = [6]` are readable, held, outside the window, apart from the stack -/
theorem insOK : ∀ p n, (p, n) ∈ [(XP, 1), (YP, 1), (MP, 1)] → RdIn R [] s0 KW 112 p n ∧ n ≤ 2 ^ 9 ∧
    NatNorm s0.mem p n ∧ Apart p (8 * n) ST 24 ∧ Apart p (8 * n) (freeOf s0.mem ST).1 (freeOf s0.mem ST).2 ∧
    (0 < 0 → Apart 0 (8 * 0) p (8 * n)) := by
  have hm : s0.mem = mem0 := rfl
  intro p n hpn
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpn
  simp only [RdIn, freeOf, win, hm, stW0, stLen0, stCap0, mkS_sp]
  rcases hpn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨⟨by decide, by rw [acc0]; decide +kernel, by decide,
      Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide),
      by simp only [outside_cons, outside_nil, and_true]; decide⟩, by decide, by simp only [NatNorm]; decide +kernel,
      by simp only [Apart]; decide, by simp only [Apart]; decide, fun h => absurd h (by decide)⟩

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`3^5 mod 6`) at `stk = 72368` -/
theorem pre : Pre R BW [] 0 0 0 ST XP 1 1 YP 1 MP 1 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  unfold Pre ExpEven.Pre CPre XFacts
  rw [hm, stLen0]
  simp only [win, WrOut, RdIn, freeOf, g0, mkS_sp, stW0, stLen0, stCap0]
  refine ⟨⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide,
    by decide, by decide, by decide, by simp only [outside_cons, outside_nil, and_true]; decide, ?_⟩, ?_⟩
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
      | exact bud
      | (intro _; exact ⟨by simp only [outside_cons, outside_nil, and_true]; decide +kernel,
          by simp only [Apart]; decide⟩)
      | (simp only [Globals, RunIface.Globals, gA_eq, wbA_eq]; decide +kernel)
      | skip
  · exact ⟨OP, one0 [] _ (by simp only [stWs, stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append,
      outside_cons, outside_nil, and_true]; decide)
      (by simp only [stWs, stkWs, stW0, stLen0, stCap0, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true]; decide), sa0⟩
  · refine ⟨⟨by decide, by decide, fun _ => ⟨Or.inr ?_, by decide⟩⟩, fun _ => by simp only [Apart, gA_eq]; decide⟩
    rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, the call `z.expNNEven(stk, 3, 5, 6)` with `z = nil` and the stack `{w, 0, 4}`; one call-site
state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z zl zc st x xl xc y yl yc m ml mc : BitVec 64) (ret : Nat) (s : State),
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
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program ExpEven.fn)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc] s ∧
    Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat m.toNat ml.toNat mc.toNat s ∧
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
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat m.toNat ml.toNat s s' :=
  ⟨WStubs.impl, R, BW, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1,
    BitVec.ofNat 64 MP, 1, 1, RET, s0, WStubs.hap,
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
      BW [] 0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 (BitVec.ofNat 64 YP) 1 1 (BitVec.ofNat 64 MP) 1 1 RET
      hret s0 (setup _ args (by decide)) pre⟩

end FvModexp.Arm64.EvenRow.Witness
