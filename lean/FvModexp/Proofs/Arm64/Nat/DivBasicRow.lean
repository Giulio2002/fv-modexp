import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

/-!
# Row: `nat.divBasic` (arm64) on the Run extraction

`correctness` = `DivBasic.ens` (its `(*stack).nat` call discharged inside by `StackNat.hyp`), moved to
`Extracted.program.link impl` (`Ensures.full`); runtime premises: the live `growslice`, `memclrNoHeapPointers` and
`gcWriteBarrier2` contracts. `Witness.nonvacuous`: the shared witness runtime, the toy allocator invariant, the Run
extraction's read-only data, the `runtime.writeBarrier` flag in memory, and the call `divBasic(q, stk, u, v)` with
`u = [5, 2^63 + 1]`, `v = [0, 2^63]` (`U / V = 1`), `len q = 1`, a stack `{w, len 0, cap 4}`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivBasicRow

/-- **`nat.divBasic`** (arm64): `q = divBasic(stk, u, v)` stores `U / V` in `q[0 : qn]` and `U mod V` in `u`, returns the
stack with its `len`; writes only `q[0 : qn]`, `u`, the stack header and free part, the runtime's memory and the window. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivBasic.fn) [qp, ql, qc, st, up, ul, uc, vp, vl, vc]
      (DivBasic.Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat)
      (DivBasic.Post R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp.toNat vl.toNat) :=
  Ensures.full hap (DivBasic.ens impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl vc)

end FvModexp.Arm64.DivBasicRow

namespace FvModexp.Arm64.DivBasicRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x100` -/
abbrev VP : Nat := OB + 0x100

/-- `u = [5, 2^63 + 1]` at `OB`, `v = [0, 2^63]` at `VP`, the stack header at `ST`, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OB then 5 else if a = OB + 8 then 1 else if a = OB + 15 then 0x80 else if a = VP + 15 then 0x80
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4 else 0

/-- the standard regions plus the `runtime.writeBarrier` flag word -/
def regs : List Region := stdRegs ++ [⟨StackNat.wbA, 8, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 2, 2, BitVec.ofNat 64 VP, 2, 2]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program DivBasic.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program DivBasic.fn)
    args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem pre : DivBasic.Pre R 0x1000 [] OA 1 ST OB 2 2 VP 2 s0 := by
  unfold DivBasic.Pre
  refine ⟨⟨⟨by decide +kernel, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel⟩,
    dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, WStubs.serves [], ?_, ?_, by decide, ?_, ?_, ?_,
    ?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ => Or.inl (by decide), ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, inv1 _⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [DivBasic.freeP, DivBasic.freeN, stW, stLen, stCap, Apart, win, outside_cons, outside_nil,
        and_true, show s0.mem = mem0 from rfl]; decide +kernel)
    | (rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq,
        show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [Held, InRanges, outside_cons, outside_nil, and_true, rt_eq]; decide +kernel)
    | (simp only [ExpHyp.stackNatCost, stLen, show s0.mem = mem0 from rfl]; decide +kernel)
    | (show _ ≤ (s0.mem).readLE _ 8; rw [show s0.mem = mem0 from rfl]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, `divBasic(q, stk, u, v)` with `u = [5, 2^63 + 1]`, `v = [0, 2^63]`, `len q = 1`; one
call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc vp vl vc : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program DivBasic.fn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc] s ∧
    DivBasic.Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ DivBasic.Post R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp.toNat vl.toNat s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 2, 2,
    BitVec.ofNat 64 VP, 2, 2, RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 0x1000 []
      (BitVec.ofNat 64 OA) 1 1 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 2 2 (BitVec.ofNat 64 VP) 2 2 RET hret s0
      setup pre⟩

end FvModexp.Arm64.DivBasicRow.Witness
