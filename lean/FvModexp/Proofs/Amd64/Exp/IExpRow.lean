import FvModexp.Proofs.Amd64.Exp.IExpCl
import FvModexp.Proofs.Amd64.Witness.StubsGrow
import FvModexp.Proofs.Amd64.Int.ModRowW
import FvModexp.Proofs.Amd64.Witness.Stubs
import FvModexp.Proofs.Amd64.Nat.RowLink

set_option autoImplicit false

/-!
# Row: `(*Int).exp` (amd64) on the Run extraction — `z.exp(z, y, m, false)` as `Run` calls it (agent expmc s84)

Twin of Arm64/ExpQ/IExpRow.lean. `correctness` = expmc's `IExp.ensCl` (`(*Int).exp` with every callee proved and the
closed TIGHT-COSTS budget; premises = the live runtime contracts only), moved to `Extracted.program.link impl`
(`Ensures.full64`), window `43736` below / `48` above `RSP` (`K = 42248`, `K + 0x5d0`). Statement: `IExp.ExpSpecA`'s
pre/post (`RunIface.ExpSpec`'s + `hasADX` readable, `natOne`'s word apart from the thresholds). The precondition reads
no byte of `[RSP, RSP + 8)` (the return address).
`Witness.nonvacuous`: the shared witness runtime `WStubs.impl`, toy allocator, budget `0x300000`, a 64 KiB stack, the
threshold globals, `natOne` and the `hasADX` byte, the call `z.exp(z, y, m, false)` with `z = 3`, `y = 5`, `m = 7`
(one limb each); one call-site state per contract; the call returns.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe maxW ExpBudget lenW PoolG ModX OneG)

namespace FvModexp.Amd64.IExpRow

/-- `(*Int).exp`'s symbol -/
abbrev fnExpL : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).exp"

theorem fn_eq : RunIface.P ++ "(*Int).exp" = fnExpL := by decide

/-- the precondition (`IExp.ExpSpecA`'s, window 43736 / 48) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y mm : BitVec 64) (s : State) :
    Prop :=
  S = StkSh ∧
    ((IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
        (lenW s.mem y.toNat)) L 43736 48 [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
      IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
      OneG R L s.mem (win s 43736 48) [z.toNat, y.toNat, mm.toNat] ∧
      PoolG R s.mem (win s 43736 48) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 RunIface.wbA 4 ∧ ModX s.mem z.toNat) ∧
      IExp.ExpA s.mem)

/-- the postcondition: `RAX = z`, `z = x ^ y mod m` (`IntPost`), `fsBase` and `DF` kept -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
    IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
      (lenW s.mem y.toNat)) L 43736 48 z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s'

/-- **`(*Int).exp`** (amd64): `z.exp(z, y, m, false)` (`m > 0`, operands of at most 128 words) returns `z` holding
`z ^ y mod m`, writes only `z`, the runtime's memory and the window; for every runtime meeting the live contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (S : PoolShape)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      Free.stkT S)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      Free.stkT S)
    (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program fnExpL) [z, z, y, mm, 0#64]
      (Pre R b L S z y mm) (Post R b L z y mm) := by
  intro ret hret s hs ⟨hS, hp⟩
  subst hS
  have h := Ensures.full64 hap (by simp [numIntRegs])
    (IExp.ensCl impl hap R hgr hmc hmv hmz hmk hno hwb hget hput (stk := 43736) (above := 48) (Nat.le_refl _)
      (by decide) b L z y mm)
  rw [fn_eq] at h
  exact h ret hret s hs hp

end FvModexp.Amd64.IExpRow

namespace FvModexp.Amd64.IExpRow.Witness

open FvModexp.Amd64.AsmWit FvModexp.Amd64.ModRowW Janus.Contracts.Toy

set_option maxRecDepth 100000

abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88
abbrev nAw : Nat := 12050400
abbrev opw : Nat := 0xb4af00
/-- the stack region below `SP0` -/
abbrev WW : Nat := 0x10000
abbrev BW : Nat := 0x300000

theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : RunIface.wbA = wbAw := by decide
theorem adx_eq : Callees.adxAddr = adxW + 2 := by decide
theorem nA_eq : RunIface.natOneA = nAw := by decide

/-- `z = 3` header at `OA` (`abs = (OB, 1, 1)`), `y = 5` at `OA + 0x40`, `m = 7` at `OA + 0x80`; `natOne = {opw, 1, 1}`,
`opw[0] = 1`; the four thresholds `40, 40, 12, 80` at `gA`; all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OA + 10 then 0xE0 else if a = OA + 16 then 1 else if a = OA + 24 then 1 else
  if a = OA + 0x48 then 0x40 else if a = OA + 0x4A then 0xE0 else if a = OA + 0x50 then 1 else
  if a = OA + 0x58 then 1 else
  if a = OA + 0x88 then 0x80 else if a = OA + 0x8A then 0xE0 else if a = OA + 0x90 then 1 else
  if a = OA + 0x98 then 1 else
  if a = OB then 3 else if a = OB + 0x40 then 5 else if a = OB + 0x80 then 7 else
  if a = nAw + 1 then 0xaf else if a = nAw + 2 then 0xb4 else if a = nAw + 8 then 1 else if a = nAw + 16 then 1 else
  if a = opw then 1 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

/-- a 64 KiB stack, the other standard regions, the thresholds, `runtime.writeBarrier`'s flag word, `natOne`, `hasADX` -/
def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨nAw, 24, true⟩, ⟨opw, 8, true⟩,
    ⟨adxW, 8, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), BitVec.ofNat 64 (OA + 0x80), 0#64]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then BitVec.ofNat 64 OA
      else if i = 1 then BitVec.ofNat 64 (OA + 0x40) else if i = 7 then BitVec.ofNat 64 (OA + 0x80)
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program fnExpL), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program fnExpL)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv BW [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem rtOut (a n : Nat) (h : WBUF + 64 ≤ a ∧ a + n ≤ HEAP) : Outside a n R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; simp only [BUMP, HEAP, WBUF] at *; omega

theorem op0 : mem0.readLE RunIface.natOneA 8 = opw := by rw [nA_eq]; decide +kernel

theorem one0 : OneG R [] mem0 (win s0 43736 48) [OA, OA + 0x40, OA + 0x80] := by
  dsimp only [OneG]
  rw [op0, nA_eq]
  refine ⟨opw, ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
      exact ⟨by simp only [Apart]; decide +kernel, by simp only [Apart]; decide +kernel,
        fun _ => ⟨by simp only [Apart]; decide +kernel, by simp only [Apart]; decide +kernel⟩⟩

theorem cpu0 : IExp.ExpA mem0 := by
  dsimp only [IExp.ExpA]
  rw [adx_eq, op0, gA_eq]
  exact ⟨by rw [acc0]; decide +kernel, by simp only [Apart]; decide⟩

set_option maxHeartbeats 64000000 in
theorem pre : Pre R BW [] StkSh (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) (BitVec.ofNat 64 (OA + 0x80)) s0 := by
  unfold Pre
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, one0, ?_, ?_, ?_, ?_⟩, cpu0⟩
  all_goals
    have hm : s0.mem = mem0 := rfl
    have hsp : s0.regs 4 = BitVec.ofNat 64 SP0 := rfl
    have hg : s0.regs 14 = BitVec.ofNat 64 G0 := rfl
    have hfs : s0.fsBase = BitVec.ofNat 64 (T0 + 8) := rfl
    try simp only [IntPre, CallEnv, RunIface.Globals, PoolG, ModX, RunIface.IntOK, List.forall_mem_cons,
      List.pairwise_cons, List.mem_singleton, List.not_mem_nil, forall_eq, hm, hsp, hg, hfs]
    try and_intros
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
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)),
        by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (unfold IntLenLe maxW; decide +kernel)
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | (constructor <;> first | decide +kernel | (rw [hm, acc0]; decide +kernel))
    | decide +kernel

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` holds, with every conjunct of its precondition, a call-site state per runtime
contract, and the returning run: the shared witness runtime, budget `0x300000`, empty live set, `z.exp(z, y, m, false)`
with `z = 3`, `y = 5`, `m = 7`. -/
theorem nonvacuous :
    ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64)
      (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh ∧
    PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program fnExpL) [z, z, y, mm, 0#64] s ∧
    Pre R b L StkSh z y mm s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R b L z y mm s s' :=
  ⟨WStubs.impl, R, BW, [], BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), BitVec.ofNat 64 (OA + 0x80), RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _,
    by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _,
    hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.getA OA 0 0, by rw [WStubs.addr_get]; rfl, by rw [WStubs.addr_get]; exact site_get _⟩,
    ⟨[(HEAP, HEAP + 24)], 0x1000, [(HEAP, HEAP + 24)], callP WStubs.putA, by rw [WStubs.addr_put]; rfl,
      by rw [WStubs.addr_put]; exact site_put _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mv]; exact WStubs.mvz R) (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_no]; exact WStubs.no [] hty _) (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) StkSh
      (by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _) (by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _)
      BW [] (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) (BitVec.ofNat 64 (OA + 0x80)) RET hret s0 setup pre⟩

end FvModexp.Amd64.IExpRow.Witness
