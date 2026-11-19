import FvModexp.Proofs.Arm64.Int.ModC
import FvModexp.Proofs.Arm64.Int.ModRowW
import FvModexp.Proofs.Arm64.Witness.StubsMvz
import FvModexp.Proofs.Arm64.Nat.RowLink

set_option autoImplicit false

/-!
# Row: `(*Int).Mod` (arm64) on the Run extraction — `z.Mod(z, y)` as `Run` calls it

`correctness` = `IMod.ensC` (every callee proved: `nat.div` with a nil stack = asm's `NatDiv.ensMC`, the budget lemma
`IMod.bud`) moved to `Extracted.program.link impl` (`Ensures.full`), window `41808` below / `32` above `SP`. Statement:
`RunIface.ModSpec`'s pre/post (`IntPre`/`IntPost` with budget `ModBudget (max (len z) (len y))`). Runtime premises: the
live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2/4`, `makeslice`, `memmove` (+ `MemmoveZeroLive`),
`newobject`, `sync.(*Pool).Get`/`Put` (`*big.stack`, `StkSh`) contracts.
`Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, toy allocator, budget `0x80000`), a 48 KiB stack, the
threshold globals at their initial values, and the call `z.Mod(z, y)` with `z = 7`, `y = 3` (one limb each); one
call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
open Janus.Contracts.Pool FvModexp
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.ModRow

/-- `(*Int).Mod`'s symbol -/
abbrev fnModL : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod"

/-- the precondition (`RunIface.ModSpec`'s, window 41808 / 32) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64) (s : State) :
    Prop :=
  S = StkSh ∧ IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L 41808 32 [z.toNat, y.toNat] s ∧
    0 < IntV s.mem y.toNat ∧ IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧
    PoolG R s.mem (win s 41808 32) ∧ ModX s.mem z.toNat

/-- the postcondition: `X0 = z`, `z = z mod y` (`IntPost`), `y` unchanged -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L 41808 32 z.toNat
    (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧ IntV s'.mem y.toNat = IntV s.mem y.toNat

/-- **`(*Int).Mod`** (arm64): `z.Mod(z, y)` (`y > 0`, operands of at most 128 words) returns `z` holding `z mod y`,
leaves `y` unchanged, writes only `z`, the runtime's memory and the window; for every runtime meeting the live
contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (S : PoolShape)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      Free.stkT S)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      Free.stkT S)
    (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program fnModL) [z, z, y]
      (Pre R b L S z y) (Post R b L z y) := by
  janus_ensures_old [FvModexp.Arm64.ModRow.Pre, FvModexp.Arm64.RunIface.IntPre, FvModexp.Arm64.RunIface.lenW, FvModexp.Arm64.RunIface.IntV, FvModexp.Arm64.RunIface.IntLenLe, FvModexp.Arm64.RunIface.maxW, FvModexp.Arm64.RunIface.PoolG, FvModexp.Arm64.win, FvModexp.Arm64.RunIface.ModX, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.RunIface.IntOK, FvModexp.natVal, FvModexp.Arm64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Arm64.RunIface.gA, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.NatNorm]
  intro ret hret s hs ⟨hS, hp⟩
  subst hS
  exact (Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.ModRow.Pre, FvModexp.Arm64.RunIface.IntPre, FvModexp.Arm64.RunIface.lenW, FvModexp.Arm64.RunIface.IntV, FvModexp.Arm64.RunIface.IntLenLe, FvModexp.Arm64.RunIface.maxW, FvModexp.Arm64.RunIface.PoolG, FvModexp.Arm64.win, FvModexp.Arm64.RunIface.ModX, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.RunIface.IntOK, FvModexp.natVal, FvModexp.Arm64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Arm64.RunIface.gA, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.NatNorm]) hap (IMod.ensC impl hap R hgr hmc hwb hwb4 hmk hmv hmz hno hget hput (stk := 41808) (above := 32)
    (by decide) (by decide) b L z y)).toOld ret hret s hs hp

end FvModexp.Arm64.ModRow

namespace FvModexp.Arm64.ModRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `z` header at `OA` (`abs = (OB, 1, 1)`, `7`), `y` at `OA + 0x40` (`abs = (OB + 0x40, 1, 1)`, `3`) -/
def g (a : Nat) : Byte :=
  if a = OA + 10 then 0xB0 else if a = OA + 16 then 1 else if a = OA + 24 then 1 else
  if a = OA + 0x48 then 0x40 else if a = OA + 0x4A then 0xB0 else if a = OA + 0x50 then 1 else
  if a = OA + 0x58 then 1 else if a = OB then 7 else if a = OB + 0x40 then 3 else
  if a = gA then 40 else if a = gA + 8 then 40 else if a = gA + 16 then 12 else if a = gA + 24 then 80 else 0

/-- a 48 KiB stack, the other standard regions, `runtime.writeBarrier`'s flag word -/
def regs : List Region := ⟨SP0 - 0xC000, 0xC100, true⟩ :: stdRegs.tail ++ [⟨wbA, 8, false⟩, ⟨gA, 32, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40)]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program fnModL),
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

theorem pre : (Pre R 0x80000 [] StkSh (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) s0) := by
  unfold Pre
  refine ⟨rfl, ?_⟩
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.sp = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 28 = BitVec.ofNat 64 G0 := rfl
  simp only [IntPre, CallEnv, Globals, PoolG, ModX, IntOK, List.forall_mem_cons, List.pairwise_cons,
    List.mem_singleton, List.not_mem_nil, forall_eq, and_true,
    hm, hsp, hg]
  and_intros
  all_goals first
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | exact inv1 _
    | (intro r hr; simp at hr; done)
    | (intros; trivial)
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (show _ = _; decide)
    | (exact Or.inr (rtOut _ _ (by decide +kernel)))
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)), by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (unfold IntLenLe maxW; decide +kernel)
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | decide +kernel
theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program fnModL)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, empty live set, `z.Mod(z, y)` with `z = 7`, `y = 3`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64)
    (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh ∧
    PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program fnModL) [z, z, y] s ∧
    Pre R b L StkSh z y s ∧
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
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier4") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4 L b s_c) ∧
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
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧ Post R b L z y (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x80000, [], BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _,
    by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _,
    hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.wb4A 0 0 0, by rw [WStubs.addr_wb4]; rfl, by rw [WStubs.addr_wb4]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mz _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.getA OA 0 0, by rw [WStubs.addr_get]; rfl, by rw [WStubs.addr_get]; exact site_get _⟩,
    ⟨[(HEAP, HEAP + 24)], 0x1000, [(HEAP, HEAP + 24)], callP WStubs.putA, by rw [WStubs.addr_put]; rfl,
      by rw [WStubs.addr_put]; exact site_put _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _)
      (by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] hty _) (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_no]; exact WStubs.no [] hty _) StkSh (by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _)
      (by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _) 0x80000 []
      (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) s0 setup pre RET hret⟩

end FvModexp.Arm64.ModRow.Witness
