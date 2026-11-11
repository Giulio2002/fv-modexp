import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

/-!
# Row: `(*stack).nat` (arm64) on the Run extraction

`correctness` = `StackNat.ens` moved to `Extracted.program.link impl` (`Ensures.full`); runtime premises: the live
`growslice`, `memclrNoHeapPointers` and `gcWriteBarrier2` contracts. `Witness.nonvacuous`: the shared witness runtime
(`WStubs.impl`), the toy allocator invariant, the Run extraction's read-only data loaded, the `runtime.writeBarrier` flag
word readable (0: barrier off), and the call `stk.nat(1)` on a stack `{w: OB, len: 0, cap: 4}` at `OA`; plus one
call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNatRow

/-- **`(*stack).nat`** (arm64): `stk.nat(n)` returns `n` words at `w' + 8·len` of the stack's (possibly grown) array and
advances the stack's `len` by `(n + 3) &^ 3`; writes only the header, the old array's free part, the runtime's memory and
the window; for every runtime meeting the live `growslice`/`memclr`/write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program StackNat.fn) [st, n]
      (fun s => StackNat.Pre R b L 4208 24 st.toNat n.toNat s)
      (fun s s' => StackNat.Post R b L 4208 24 st.toNat n.toNat s s') :=
  Ensures.full hap (StackNat.ens impl hap R hgr hmc hwb b L st n)

end FvModexp.Arm64.StackNatRow

namespace FvModexp.Arm64.StackNatRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header `{w: OB, len: 0, cap: 4}` at `OA`, all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OA + 2 then 0xB0 else if a = OA + 16 then 4 else 0

/-- the standard regions plus the (read-only here) `runtime.writeBarrier` flag word -/
def regs : List Region := stdRegs ++ [⟨StackNat.wbA, 8, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 1]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program StackNat.fn)
    args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

/-- the toy runtime's invariant for the witness memory (as `AsmWit.inv0`, with the extra region) -/
theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem pre : StackNat.Pre R 0x1000 [] 4208 24 OA 1 s0 := by
  refine ⟨⟨⟨by decide +kernel, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel⟩,
    dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, WStubs.serves [], ?_, ?_, fun _ => ⟨?_, ?_⟩,
    by decide, by decide +kernel, by decide +kernel, inv1 _, by rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel,
    ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq,
        show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (trace_state; sorry)

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime
(toy `growslice`, looping `memclr`, toy write barrier), budget `0x1000`, empty live set, the call `stk.nat(1)` on a
stack with room (`len 0`, `cap 4`); one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64)
    (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program StackNat.fn) [st, n] s ∧
    StackNat.Pre R b L 4208 24 st.toNat n.toNat s ∧
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
      ABIReturn s s' ∧ StackNat.Post R b L 4208 24 st.toNat n.toNat s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 1, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 0x1000 [] (BitVec.ofNat 64 OA) 1
      RET hret s0 setup pre⟩

end FvModexp.Arm64.StackNatRow.Witness
