import FvModexp.Proofs.Arm64.NatQ.NatSqr
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

set_option autoImplicit false

/-!
# Row (Q-form, TIGHT COSTS; release row): `nat.sqr` (arm64) on the Run extraction — the whole squaring SCC `{nat.sqr, karatsubaSqr}` + `basicSqr`

`correctness` = `Q.NatSqr.ens` (amortised stack budget: level-free cost `sqrCQ (len x)` + the reserve
`stkR H`, Common/StackPot; `H` a bound of every stack level reached) moved to `Extracted.program.link impl` (`Ensures.full`); runtime premises: the live
`makeslice`, `growslice`, `memclrNoHeapPointers`, `memmove` and `gcWriteBarrier2` contracts. `Witness.nonvacuous`: the
shared witness runtime, the toy allocator invariant, the Run extraction's read-only data, the four threshold globals
(`40, 40, 12, 80`) and the `runtime.writeBarrier` flag in memory, and the call `z.sqr(stk, x)` with `x = 3` (one limb),
`z` an empty slice of capacity 2, a stack `{w, len 0, cap 4}`, window `sqrW 1`; one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SqrRowQ

/-- **`nat.sqr`** (arm64): `z.sqr(stk, x)` (any length `≤ 2^12`, operands not normalised) returns `X²` normalised, in
`z`'s array when `cap z ≥ 2·len x` and `z` is not `x`'s alias (then writing exactly `z[0:2·len x]`), else in a fresh
array apart from the live set and the stack's final array; the stack comes back with its `len` (a new stack array is an
element of the final live set); writes only `z`, the stack header and free part, the runtime's memory and the window
`sqrW (len x)`; for every runtime meeting the live allocation / copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program Q.NatSqr.fn) [zp, zl, zc, st, xp, xl, xc]
      (Q.NatSqr.SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)
      (Q.NatSqr.SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.Q.NatSqr.SPre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.NatAdd.wordT, FvModexp.NatLive, FvModexp.Arm64.Q.NatSqr.guard, FvModexp.Arm64.Q.NatSqr.StkSep, FvModexp.Arm64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.stkR, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.RunIface.wbA, FvModexp.Arm64.Q.BasicSqr.freeP, FvModexp.Arm64.Q.BasicSqr.freeN, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.StackNat.wbA, FvModexp.stkRes, FvModexp.potK]) hap (Q.NatSqr.ens impl hap R hmk hgr hmc hmv hwb H b L W zp zl zc st xp xl xc)

end FvModexp.Arm64.SqrRowQ

namespace FvModexp.Arm64.SqrRowQ.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len 0, cap 4}` -/
abbrev ST : Nat := OA + 0x100

/-- `x = 3` at `OB`, the stack header at `ST`, the threshold globals at `gA`, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OB then 3 else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = RunIface.gA then 40 else if a = RunIface.gA + 8 then 40 else if a = RunIface.gA + 16 then 12
  else if a = RunIface.gA + 24 then 80 else 0

/-- the standard regions plus the threshold globals (writable `.data`) and the `runtime.writeBarrier` flag word -/
def regs : List Region := stdRegs ++ [⟨RunIface.gA, 32, true⟩, ⟨StackNat.wbA, 8, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 0, 2, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 1, 1]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program Q.NatSqr.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program Q.NatSqr.fn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x4000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem pre : Q.NatSqr.SPre R 0x4000 72 [] (sqrW 1) OA 2 ST OB 1 1 s0 := by
  unfold Q.NatSqr.SPre
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, ?_,
    WStubs.serves [], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩,
    fun _ => ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩, Or.inr fun _ _ => ?_,
    ⟨?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, inv1 _⟩
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
    | (simp only [BasicSqr.freeP, BasicSqr.freeN, Held, InRanges, stW, stLen, stCap, rt_eq, outside_cons,
        outside_nil, and_true, show s0.mem = mem0 from rfl]; decide +kernel)
    | (unfold sqrW ksqrW; decide)
    | (simp only [stkR, stCap, show s0.mem = mem0 from rfl]; unfold sqrCQ makeB; decide +kernel)
    | (simp only [stLen, show s0.mem = mem0 from rfl]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x4000`, reserve level `H = 72`, empty live set, `z.sqr(stk, x)` with `x = 3` (`len 1`), `cap z = 2` (reused), the stack
`{w, 0, 4}`, window `sqrW 1`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program Q.NatSqr.fn)
      [zp, zl, zc, st, xp, xl, xc] s ∧
    Q.NatSqr.SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s ∧
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
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ Q.NatSqr.SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 72, 0x4000, [], sqrW 1, BitVec.ofNat 64 OA, 0, 2, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 1, 1, RET,
    s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 72 0x4000 [] (sqrW 1)
      (BitVec.ofNat 64 OA) 0 2 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 1 1 s0 setup pre RET hret⟩

end FvModexp.Arm64.SqrRowQ.Witness
