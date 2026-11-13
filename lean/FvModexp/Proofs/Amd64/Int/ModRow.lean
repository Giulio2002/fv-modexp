import FvModexp.Proofs.Amd64.Int.ModCA
import FvModexp.Proofs.Amd64.Int.ModRowW
import FvModexp.Proofs.Amd64.Witness.Stubs
import FvModexp.Proofs.Amd64.Nat.RowLink

set_option autoImplicit false

/-!
# Row: `(*Int).Mod` (amd64) on the Run extraction — `z.Mod(z, y)` as `Run` calls it (PREMISE FORM)

Twin of Arm64/Int/ModRow.lean. `correctness` = `IMod.ensCA` moved to `Extracted.program.link impl` (`Ensures.full64`),
window `41800` below / `16` above `RSP`. Statement: `IMod.ModSpecA`'s pre/post (= `RunIface.ModSpec`'s, plus the
`hasADX` byte readable; coordinator DECISION on "[divmc s56]"): `IntPre`/`IntPost` with budget
`ModBudget (max (len z) (len y))`. Runtime premises: the live `makeslice`, `memmove` (+ `MemmoveZeroLive64`),
`newobject`, `gcWriteBarrier4`, `sync.(*Pool).Get`/`Put` (`*big.stack`, `StkSh`) contracts.

STATUS (premise form): `nat.div`'s large-divisor path enters as the premise `Q.DivLarge.HypG impl R dc` with the
budget bound `hbud` on its cost `dc`, until asm's amd64 `divLarge` proof lands (then both are discharged as in arm64's
`IMod.ensC`/`IMod.bud`). `Witness.nonvacuous_of`: for every such `dc` satisfying them on the shared witness runtime,
every other hypothesis and every precondition conjunct hold together (the shared witness runtime `WStubs.impl`, toy
allocator, budget `0x80000`, a 64 KiB stack, the threshold globals at their initial values, the `hasADX` byte, the call
`z.Mod(z, y)` with `z = 7`, `y = 3`, one limb each; one call-site state per contract) and the call returns.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe maxW ModBudget lenW PoolG ModX)

namespace FvModexp.Amd64.ModRow

/-- `(*Int).Mod`'s symbol -/
abbrev fnModL : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod"

theorem fn_eq : RunIface.P ++ "(*Int).Mod" = fnModL := by decide

/-- the precondition (`IMod.ModSpecA`'s, window 41800 / 16) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64) (s : State) :
    Prop :=
  S = StkSh ∧ (IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L 41800 16 [z.toNat, y.toNat] s ∧
    0 < IntV s.mem y.toNat ∧ IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧
    PoolG R s.mem (win s 41800 16) ∧ ModX s.mem z.toNat) ∧ s.mem.accessible Callees.adxAddr 1 false = true

/-- the postcondition: `RAX = z`, `z = z mod y` (`IntPost`), `y` unchanged, `fsBase` and `DF` kept -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
    IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L 41800 16 z.toNat
      (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧ IntV s'.mem y.toNat = IntV s.mem y.toNat

/-- **`(*Int).Mod`** (amd64): `z.Mod(z, y)` (`y > 0`, operands of at most 128 words) returns `z` holding `z mod y`,
leaves `y` unchanged, writes only `z`, the runtime's memory and the window; for every runtime meeting the live
contracts — PREMISE FORM: given `nat.div`'s large-divisor summary `Q.DivLarge.HypG impl R dc` and its cost bound. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb4 : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
      4096 R 4)
    (S : PoolShape)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R Free.stkT S)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R Free.stkT S)
    (dc : Nat → Nat → Nat) (hL : Q.DivLarge.HypG impl R dc)
    (hbud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → Q.NatDiv.costMQ dc ul vl ≤ ModBudget (max ul vl))
    (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program fnModL) [z, z, y]
      (Pre R b L S z y) (Post R b L z y) := by
  intro ret hret s hs ⟨hS, hp⟩
  subst hS
  have h := Ensures.full64 hap (by simp [numIntRegs])
    (IMod.ensCA impl hap R hmk hmv hmz hno hget hput hwb4 dc hL hbud (stk := 41800) (above := 16)
      (by decide) (by decide) b L z y)
  rw [fn_eq] at h
  exact h ret hret s hs hp

end FvModexp.Amd64.ModRow

namespace FvModexp.Amd64.ModRow.Witness

open FvModexp.Amd64.AsmWit FvModexp.Amd64.ModRowW Janus.Contracts.Toy

set_option maxRecDepth 100000

abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88
/-- the stack region below `SP0` -/
abbrev WW : Nat := 0x10000

theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : RunIface.wbA = wbAw := by decide
theorem adx_eq : Callees.adxAddr = adxW + 2 := by decide

/-- `z` header at `OA` (`abs = (OB, 1, 1)`, `7`), `y` at `OA + 0x40` (`abs = (OB + 0x40, 1, 1)`, `3`), the four
thresholds `40, 40, 12, 80` at `gA`; all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OA + 10 then 0xE0 else if a = OA + 16 then 1 else if a = OA + 24 then 1 else
  if a = OA + 0x48 then 0x40 else if a = OA + 0x4A then 0xE0 else if a = OA + 0x50 then 1 else
  if a = OA + 0x58 then 1 else if a = OB then 7 else if a = OB + 0x40 then 3 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

/-- a 64 KiB stack, the other standard regions, the thresholds, `runtime.writeBarrier`'s flag word, `hasADX` -/
def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40)]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then BitVec.ofNat 64 OA
      else if i = 1 then BitVec.ofNat 64 (OA + 0x40)
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program fnModL), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program fnModL)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x80000 [] gp (view R.rt [] mem0) := by
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

set_option maxHeartbeats 64000000 in
theorem pre : Pre R 0x80000 [] StkSh (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) s0 := by
  unfold Pre
  refine ⟨rfl, ?_⟩
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.regs 4 = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 14 = BitVec.ofNat 64 G0 := rfl
  have hfs : s0.fsBase = BitVec.ofNat 64 (T0 + 8) := rfl
  simp only [IntPre, CallEnv, RunIface.Globals, PoolG, ModX, RunIface.IntOK, List.forall_mem_cons,
    List.pairwise_cons, List.mem_singleton, List.not_mem_nil, forall_eq, hm, hsp, hg, hfs]
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

/-- Every hypothesis of `correctness` except the `nat.div` large-divisor premise and its cost bound (still premises,
taken here for the witness runtime) holds, with every conjunct of its precondition, a call-site state per runtime
contract, and the returning run: the shared witness runtime, budget `0x80000`, empty live set, `z.Mod(z, y)` with
`z = 7`, `y = 3`. -/
theorem nonvacuous_of (dc : Nat → Nat → Nat) (hL : Q.DivLarge.HypG WStubs.impl R dc)
    (hbud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → Q.NatDiv.costMQ dc ul vl ≤ ModBudget (max ul vl)) :
    ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64)
      (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R Free.stkT StkSh ∧
    Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R Free.stkT StkSh ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program fnModL) [z, z, y] s ∧
    Pre R b L StkSh z y s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier4") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R b L z y s s' :=
  ⟨WStubs.impl, R, 0x80000, [], BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] hty _,
    by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _,
    by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _,
    hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb4A 0 0 0, by rw [WStubs.addr_wb4]; rfl, by rw [WStubs.addr_wb4]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.getA OA 0 0, by rw [WStubs.addr_get]; rfl, by rw [WStubs.addr_get]; exact site_get _⟩,
    ⟨[(HEAP, HEAP + 24)], 0x1000, [(HEAP, HEAP + 24)], callP WStubs.putA, by rw [WStubs.addr_put]; rfl,
      by rw [WStubs.addr_put]; exact site_put _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_no]; exact WStubs.no [] hty _) (by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] hty _) StkSh
      (by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _) (by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _)
      dc hL hbud 0x80000 [] (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) RET hret s0 setup pre⟩

end FvModexp.Amd64.ModRow.Witness
