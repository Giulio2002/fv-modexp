import FvModexp.Proofs.Arm64.Nat.RemC
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Int.ModRowW
import FvModexp.Proofs.Arm64.Witness.StubsMvz

set_option autoImplicit false

/-!
# Row: `nat.rem` (arm64) on the Run extraction — `NHyp.RemHyp` (+ `0 < st`, "[asm s34] FINDING")

`correctness` = `NatRem.ensC` (`stk.nat` + `nat.div` = `NatDiv.ensCL`, every callee proved) moved to
`Extracted.program.link impl` (`Ensures.full`); window `41712` below / `112` above `SP`. Statement: `RemDefs.Pre`
(= `NHyp.CPre` with the inputs `u`, `v`, `0 < len v`, `¬alias(z, u)`, `0 < st`) → `CPostR` with value `U mod V`.
Runtime premises: the live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`, `makeslice`, `memmove`
(+ `MemmoveZeroLive`) contracts.
`Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, toy allocator, budget `0x80000`), a 48 KiB stack, the
threshold globals at their initial values, the call `z.rem(stk, u, v)` with `z = nil`, `u = 7`, `v = 3`, the stack
`{w, len 0, cap 4}`; one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.RemRow

/-- **`nat.rem`** (arm64): `r = z.rem(stk, u, v)` (`v ≠ 0`, `len ≤ 2^9`, normalised, `z` not aliasing `u`) returns
`U mod V` normalised (in `z`'s array or a fresh one), the stack restored; writes only `z`, the stack, the runtime's
memory and the window; for every runtime meeting the live contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program NatRem.fn) [z, zl, zc, st, u, ul, uc, v, vl, vc]
      (fun s => NatRem.Pre R b (NatDiv.cost DivRec.drsC) L z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat
        uc.toNat v.toNat vl.toNat s)
      (fun s s' => NatRem.Post R b (NatDiv.cost DivRec.drsC) L z.toNat zc.toNat st.toNat u.toNat ul.toNat v.toNat
        vl.toNat s s') :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.NatRem.Pre, FvModexp.Arm64.NHyp.CPre, FvModexp.stLen, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.StackNat.wT, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, FvModexp.Arm64.NHyp.freeOf, FvModexp.Arm64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.StackNat.wbA, FvModexp.Arm64.RunIface.gA, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]) hap (NatRem.ensC impl hap R hgr hmc hwb hmk hmv hmz b L z zl zc st u ul uc v vl vc)

end FvModexp.Arm64.RemRow

namespace FvModexp.Arm64.RemRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x40` -/
abbrev VP : Nat := OB + 0x40

/-- `u = 7` at `OB`, `v = 3` at `VP`, the stack header at `ST`, the threshold globals, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OB then 7 else if a = VP then 3
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = gA then 40 else if a = gA + 8 then 40 else if a = gA + 16 then 12 else if a = gA + 24 then 80 else 0

/-- a 48 KiB stack, the other standard regions, `runtime.writeBarrier`'s flag word, the threshold globals -/
def regs : List Region := ⟨SP0 - 0xC000, 0xC100, true⟩ :: stdRegs.tail ++ [⟨StackNat.wbA, 8, false⟩, ⟨gA, 32, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 VP, 1, 1]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program NatRem.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x80000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem rtOut (a n : Nat) (h : WBUF + 64 ≤ a ∧ a + n ≤ HEAP) : Outside a n R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; simp only [BUMP, HEAP, WBUF] at *; omega

theorem len0 : stLen mem0 ST = 0 := by decide +kernel

theorem cost0 : NatRem.cost (NatDiv.cost DivRec.drsC) (stLen mem0 ST) 1 1 ≤ 0x80000 := by
  rw [len0]; simp only [NatRem.cost, NatDiv.cost, DivLarge.cost]; rw [DivRec.drsC_small (by decide)]; decide +kernel

theorem pre : NatRem.Pre R 0x80000 (NatDiv.cost DivRec.drsC) [] 0 0 0 ST OB 1 1 VP 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.sp = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 28 = BitVec.ofNat 64 G0 := rfl
  simp only [NatRem.Pre, NatRem.NoAlias, NHyp.CPre, CallEnv, Globals, ExpHyp.WrOut, ExpHyp.RdIn, ExpHyp.StackOK', StkOK,
    List.mem_cons, List.not_mem_nil, hm, hsp, hg]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cost0, inv1 _⟩, ?_⟩,
    ?_, ?_⟩
  all_goals try and_intros
  all_goals first
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | (intro r hr; simp at hr; done)
    | (intros; trivial)
    | (intro p c hpc hc; rcases hpc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> exact absurd hc (by omega))
    | (intro p n hpn; rcases hpn with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        (try exact h.elim) <;> obtain ⟨rfl, rfl⟩ := h <;> and_intros <;> first
          | (simp only [acc0] <;> decide +kernel)
          | exact Or.inr (rtOut _ _ (by decide +kernel))
          | (simp only [win, stW, stCap, outside_cons, outside_nil, and_true] <;> decide +kernel)
          | (unfold NatNorm; right; decide +kernel)
          | (intro h; exact absurd h (by decide))
          | (simp only [NHyp.freeOf, stW, stLen, stCap, Apart] <;> decide +kernel)
          | (unfold Apart <;> decide +kernel)
          | decide +kernel)
    | (simp only [NHyp.freeOf, stW, stLen, stCap, Apart] <;> decide +kernel)
    | (intro _; and_intros <;> first
        | (simp only [acc0] <;> decide +kernel)
        | exact Or.inr (rtOut _ _ (by decide +kernel))
        | (simp only [win, stW, stCap, outside_cons, outside_nil, and_true] <;> decide +kernel)
        | (unfold Apart <;> decide +kernel)
        | decide +kernel)
    | (simp only [NatLive]; intro h; exact absurd h (by decide))
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (show _ = _; decide)
    | (exact Or.inr (rtOut _ _ (by decide +kernel)))
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)),
        by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (intro h; exact absurd h (by decide))
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (intro _; exact ⟨by unfold Apart; decide +kernel, by unfold Apart; decide +kernel⟩)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | decide +kernel

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program NatRem.fn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, empty live set, `z.rem(stk, u, v)` with `z = nil`, `u = 7`, `v = 3`; one call-site state
per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z zl zc st u ul uc v vl vc : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program NatRem.fn)
      [z, zl, zc, st, u, ul, uc, v, vl, vc] s ∧
    NatRem.Pre R b (NatDiv.cost DivRec.drsC) L z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat
      vl.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      (s_c.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s_c ∧
      LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
        (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3)) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧
      NatRem.Post R b (NatDiv.cost DivRec.drsC) L z.toNat zc.toNat st.toNat u.toNat ul.toNat v.toNat vl.toNat (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x80000, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 VP, 1, 1,
    RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mz _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R) 0x80000 []
      0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 1 1 (BitVec.ofNat 64 VP) 1 1 s0 setup pre RET hret⟩

end FvModexp.Arm64.RemRow.Witness
