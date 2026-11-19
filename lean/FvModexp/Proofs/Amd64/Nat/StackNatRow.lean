import FvModexp.Proofs.Amd64.Nat.StackNat
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

/-!
# Row: `(*stack).nat` (amd64) on the Run extraction — the twin of Arm64/Nat/StackNatRow.lean
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNatRow

/-- **`(*stack).nat`** (amd64): as `FvModexp.Arm64.StackNatRow.correctness`. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program StackNat.fn) [st, n]
      (fun s => StackNat.Pre R b L 4192 24 st.toNat n.toNat s)
      (fun s s' => StackNat.Post R b L 4192 24 st.toNat n.toNat s s') :=
  Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Amd64.StackNat.Pre, FvModexp.Amd64.CallEnv, FvModexp.StkOK, FvModexp.Amd64.win, FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.TlsOK, FvModexp.NatLive]) hap (by simp [numIntRegs]) (StackNat.ens impl hap R hgr hmc hwb b L st n)

end FvModexp.Amd64.StackNatRow

namespace FvModexp.Amd64.StackNatRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header `{w: OB, len: 0, cap: 4}` at `OA` (`OB = 0xE00000`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OA + 2 then 0xE0 else if a = OA + 16 then 4 else 0

/-- the standard regions plus the `runtime.writeBarrier` flag word -/
def regs : List Janus.Arm64.Region := stdRegs ++ [⟨StackNat.wbA, 8, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 1]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 1
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program StackNat.fn)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) :
    mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

/-- the toy runtime's invariant for the witness memory (as `AsmWit.inv0`, with the extra region) -/
theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  show wbytes (toyBytes g) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem pre : StackNat.Pre R 0x1000 [] 4192 24 OA 1 s0 := by
  refine ⟨⟨?_, ?_, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut, ⟨?_, ?_, ?_⟩⟩,
    WStubs.serves [], ?_, ?_, fun _ => ⟨?_, ?_⟩, by decide, by decide +kernel, by decide +kernel, inv1 _, ?_, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩; rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩; rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq,
        show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together (the call `stk.nat(1)` on a
stack with room), one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64)
    (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program StackNat.fn) [st, n] s ∧
    StackNat.Pre R b L 4192 24 st.toNat n.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ StackNat.Post R b L 4192 24 st.toNat n.toNat (s.setRet ret) s' :=
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
      s0 setup pre RET hret⟩

end FvModexp.Amd64.StackNatRow.Witness
