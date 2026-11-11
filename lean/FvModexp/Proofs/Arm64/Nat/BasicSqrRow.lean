import FvModexp.Proofs.Arm64.Nat.BasicSqr
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

/-!
# Row: `basicSqr` (arm64) on the Run extraction

`correctness` = `BasicSqr.ens` with its `(*stack).nat` premise discharged by `StackNat.hyp` (stk 4208, above 24), moved
to `Extracted.program.link impl` (`Ensures.full`); runtime premises: the live `memclrNoHeapPointers`, `growslice` and
`gcWriteBarrier2` contracts. `Witness.nonvacuous`: the shared witness runtime, the toy allocator invariant, the Run
extraction's read-only data, the threshold globals (`basicSqrThreshold = 12`) and the `runtime.writeBarrier` flag in
memory, and the call `basicSqr(stk, z, x)` with `x = 3` (one limb), `z` two zero limbs, a stack `{w, len 0, cap 4}`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.BasicSqrRow

/-- **`basicSqr`** (arm64): `basicSqr(stk, z, x)` with `len z = 2·len x` stores `x²` in `z[0:2n]`, returns the stack
with its `len`, writes only `z[0:2n]`, the stack header and free part, the runtime's memory and the window. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program BasicSqr.fn) [st, zp, zl, zc, xp, xl, xc]
      (BasicSqr.Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat)
      (BasicSqr.Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat) :=
  Ensures.full hap (BasicSqr.ens impl hap R hmc 4208 24 (StackNat.hyp impl hap R hgr hmc hwb) (by decide) (by decide)
    b L st zp zl zc xp xl xc)

end FvModexp.Arm64.BasicSqrRow

namespace FvModexp.Arm64.BasicSqrRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100

/-- `x = 3` at `OB`, the stack header at `ST`, `basicSqrThreshold = 12`, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OB then 3 else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = BasicSqr.thrA then 12 else 0

/-- the standard regions plus the threshold globals (writable `.data`) and the `runtime.writeBarrier` flag word -/
def regs : List Region := stdRegs ++ [⟨RunIface.gA, 32, true⟩, ⟨StackNat.wbA, 8, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 ST, BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 1, 1]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program BasicSqr.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program BasicSqr.fn)
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

theorem pre : BasicSqr.Pre R 0x1000 [] ST OA 2 2 OB 1 s0 := by
  refine ⟨⟨⟨by decide +kernel, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel⟩,
    dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, WStubs.serves [], ?_, ?_, ?_, by decide, rfl,
    by decide, by decide, ?_, ?_, ?_, ?_, by decide, Or.inr ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_⟩, ?_, ?_, ?_, inv1 _, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [BasicSqr.freeP, BasicSqr.freeN, stW, stLen, stCap, Apart, win, outside_cons, outside_nil,
        and_true, show s0.mem = mem0 from rfl]; decide +kernel)
    | (rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq,
        show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [NatLive, Held, InRanges, outside_cons, outside_nil, and_true, rt_eq, show s0.mem = mem0 from rfl,
        acc0]; decide +kernel)
    | decide +kernel
    | (trace_state; sorry)

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, `basicSqr(stk, z, x)` with `x = 3` (`len 1`, the `basicMul` path), `len z = 2`; one
call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (st zp zl zc xp xl xc : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program BasicSqr.fn)
      [st, zp, zl, zc, xp, xl, xc] s ∧
    BasicSqr.Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s ∧
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
      ABIReturn s s' ∧ BasicSqr.Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 ST, BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 1, 1, RET, s0,
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
      (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 1 1 RET hret s0 setup pre⟩

end FvModexp.Arm64.BasicSqrRow.Witness
