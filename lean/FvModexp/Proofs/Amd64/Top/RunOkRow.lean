import FvModexp.Proofs.Amd64.Top.RunOkLib
import FvModexp.Amd64.RunErr
import FvModexp.Proofs.Amd64.Witness.StubsMvz
import FvModexp.Proofs.Amd64.Witness.StubsMkz
import FvModexp.Proofs.Amd64.Int.IntBytes

set_option autoImplicit false

/-!
# Row 1, amd64, success path: `Run` on call data that passes EIP-7823 returns `(compute data (parseLengths data), nil)`

`correctness_ok`: for every input slice whose length headers pass `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns `(out, nil)` with `out = compute data (parseLengths data)` (EthLib), keeping the Go ABI and
the memory frame. The statement uses `FvModexp.Spec.*` (`Spec.RunAmd64`: `EnvW`, `Input`, `OkReqs`, `Globals`,
`okBudget`, `OkRet`, `FrameW`).

STATUS: the big-number callees `(*Int).Mod`, `(*Int).exp` enter as PREMISES in their interface shape
(`RunIface.ModSpec`/`ExpSpec`, call depth `stkM`/`aboveM`, window `W ≥ 616 + stkM`) until their machine-code proofs land
(divmc / expmc); `(*Int).Bytes` is discharged (`IntBytes.bytesSpec_at`).

`WitnessOk.nonvacuous_of`: every hypothesis (except the two callee specs, still premises) and every precondition
conjunct hold together for the shared amd64 witness runtime and the call `Run(c, p, 99, 99)` on 99 zero bytes (lengths `0, 0, 0`)
(budget `0x300000` ≤ the toy heap's `2^22`, window `0x20000`), with a call-site state per runtime contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run

/-- **Row 1, amd64, EIP-7823 success** (callee specs `Mod`/`exp` as premises). -/
theorem correctness_ok (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (stkM aboveM : Nat) (hM : RunIface.ModSpecA impl R stkM aboveM) (hE : RunIface.ExpSpecA impl R stkM aboveM)
    (W : Nat) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (hk1 : 4160 ≤ stkM) (ha1 : 16 ≤ aboveM)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
        RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.CpuOne s.mem ∧
        RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Spec.RunAmd64.EnvW, FvModexp.Spec.RunAmd64.CpuOne, FvModexp.Spec.RunAmd64.Input, FvModexp.Spec.OsakaReceiver, FvModexp.Spec.RunAmd64.Globals, FvModexp.Spec.RunAmd64.windowW, FvModexp.Spec.RunAmd64.NatOne, FvModexp.Spec.RunAmd64.StackPool, FvModexp.Amd64.Run.bytesAt_setRet, FvModexp.Spec.RunAmd64.window, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, Janus.Spec.Pool.newOffset]) hap (ns := LibRun.names) (by simp [numIntRegs])
    (LibRun.eq_only ▸ ensOkLib impl hap R hmk hmv hmz hno stkM aboveM hM hE
      (IntBytes.bytesSpec_at impl hap R hmk hmkz stkM aboveM hk1 ha1) W hW hW1 hab (by omega) b L c p len cp)

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run.WitnessOk

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- The window of the witness call. -/
def WW : Nat := 0x20000
/-- The budget of the witness call (`okBudget` of the lengths `0, 0, 0` is `149832`; the toy heap admits `2^22`; chosen while
`RunIface.ExpBudget` carried a temporary `2^32` slack, now removed (TIGHT COSTS: factor-free, ≤ `2^35`)). -/
def bW : Nat := 0x300000
def gAw : Nat := 0xb4ae88
def wbAw : Nat := 0xbb7040
/-- `natOne`'s header (`.data`) and the witness's choice of its backing word. -/
def nAw : Nat := 12050400
def opw : Nat := 0xb4af00

theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : RunIface.wbA = wbAw := by decide
theorem nA_eq : RunIface.natOneA = nAw := by decide

/-- The receiver's three flags (at `OA`) are 1; the call data (at `OB`): 99 zero bytes (lengths `0, 0, 0`: `Run` returns
the empty output before any `math/big` call); the four `math/big` thresholds `40, 40, 12, 80` at `gA`; all other witness bytes 0. -/
def g (a : Nat) : Byte :=
  if a = OA ∨ a = OA + 1 ∨ a = OA + 2 then 1 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else
  if a = nAw + 1 then 0xaf else if a = nAw + 2 then 0xb4 else if a = nAw + 8 then 1 else if a = nAw + 16 then 1 else
  if a = opw then 1 else 0

/-- `stdRegs` with the stack region grown to the window `WW` and the globals' regions. -/
def regs1 : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨nAw, 24, true⟩, ⟨opw, 8, true⟩]

abbrev mem1 : Janus.Arm64.Memory := wmem (toyBytes g) regs1

def c1 : BitVec 64 := BitVec.ofNat 64 OA
def p1 : BitVec 64 := BitVec.ofNat 64 OB

def s1 : State :=
  { regs := fun i => if i = 0 then c1 else if i = 3 then p1 else if i = 1 then 99 else if i = 7 then 99
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program RunAmd64.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem1, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem setup : CallSetup0 (segAddr Extracted.program RunAmd64.fn)
    [c1, p1, 99, 99] s1 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump1 : mem1.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv bW [] gp (view R.rt [] mem1) := by
  refine toyInv_init_live (m := mem1) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump1 (fun i hi hi' => ?_) (by rw [acc_eq (toyBytes g)]; decide +kernel)
    (by rw [acc_eq (toyBytes g)]; decide +kernel) (by rw [acc_eq (toyBytes g)]; decide +kernel)
  show wbytes (toyBytes g) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem pass1 : LengthsPass (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat) := by
  rw [lengthsPass_iff]; decide +kernel

theorem budget1 : RunAmd64.okBudget (parseLengths (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)) ≤ bW := by
  decide +kernel

theorem globals1 : RunAmd64.Globals R s1.mem (RunAmd64.windowW s1 WW) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.windowW, outside_cons, outside_nil, and_true]; decide +kernel)
    | (rw [show s1.mem = wmem (toyBytes g) regs1 from rfl, acc_eq]; decide +kernel)

theorem op1 : s1.mem.readLE RunIface.natOneA 8 = opw := by rw [nA_eq]; decide +kernel

theorem one1 : RunAmd64.NatOne R s1.mem (RunAmd64.windowW s1 WW) := by
  dsimp only [RunAmd64.NatOne]
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» = RunIface.natOneA from rfl, op1,
    nA_eq]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_, by decide, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.windowW, outside_cons, outside_nil, and_true]; decide +kernel)
    | (rw [show s1.mem = wmem (toyBytes g) regs1 from rfl, acc_eq]; decide +kernel)

theorem pool1 : RunAmd64.StackPool R s1.mem (RunAmd64.windowW s1 WW) := by
  dsimp only [RunAmd64.StackPool]
  refine ⟨?_, by decide +kernel, ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [RunAmd64.windowW, outside_cons, outside_nil, and_true]; decide +kernel

theorem pre : RunAmd64.EnvW R [] s1 WW ∧ RunAmd64.Input R [] c1 p1 99 99 s1 ∧ OsakaReceiver s1.mem c1.toNat ∧
    R.inv bW [] (s1.regs 14).toNat (view R.rt [] s1.mem) ∧ RunAmd64.OkReqs R ∧
    RunAmd64.Globals R s1.mem (RunAmd64.windowW s1 WW) ∧ RunAmd64.NatOne R s1.mem (RunAmd64.windowW s1 WW) ∧
    RunAmd64.StackPool R s1.mem (RunAmd64.windowW s1 WW) ∧
    RunAmd64.okBudget (parseLengths (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)) ≤ bW ∧
    LengthsPass (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat) := by
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩, fun r hr => by simp at hr, fun r hr => by simp at hr⟩,
    ⟨?_, by decide, Or.inr ?_, ?_, by decide, by decide, by decide, ?_, Or.inr ?_, ?_⟩,
    (by first | exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩ | exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩), inv1 _,
    ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
      fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩,
    globals1, one1, pool1, budget1, pass1⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.window, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s1.mem = wmem (toyBytes g) regs1 from rfl, acc_eq]; decide +kernel)
    | decide +kernel

theorem model_mk : MakesliceLiveContract64 (Extracted.program.ofImpl WStubs.impl) WStubs.mkA 4096 R :=
  WStubs.mk [] (by intro t ht; simp at ht) _
theorem model_mkz : MakesliceZeroLive64 (Extracted.program.ofImpl WStubs.impl) WStubs.mkA 4096 R :=
  WStubs.mkz [] (by intro t ht; simp at ht) _
theorem model_mv : MemmoveLive64 (Extracted.program.ofImpl WStubs.impl) WStubs.mvA 4096 R := WStubs.mv R
theorem model_mvz : MemmoveZeroLive64 (Extracted.program.ofImpl WStubs.impl) WStubs.mvA 4096 R := WStubs.mvz R
theorem model_no : NewobjectLiveContract64 (Extracted.program.ofImpl WStubs.impl) WStubs.noA 4096 R :=
  WStubs.no [] (by intro t ht; simp at ht) _

/-- The `MemmoveZeroLive64` premise at a call. -/
@[reducible] def mvzSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  (s.regs 1).toNat = 0 ∧ MemPre64 4096 3 s ∧
    LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3)

/-- `memmove(OA, OB, 0)` satisfies it. -/
theorem site_mvz (addr : Nat) : mvzSite R addr [] 0x1000 (callS addr OA OB 0) := by
  refine ⟨by simp only [cs_r1, BitVec.toNat_ofNat], ⟨cs_sg _ _ _ _, cs_callOKm _ _ _ _ 3 (by omega), ?_⟩,
    ⟨trivial, cs_inv _ _ _ _, fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩⟩
  all_goals try simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, calleeStack64, cs_g, cs_mem, cs_r0, cs_r1, cs_r3,
    cs_sp, BitVec.toNat_ofNat]
  all_goals first
    | (simp only [outside_cons, outside_nil, and_true]; decide)
    | (rw [memZ_acc]; decide +kernel)
    | decide

/-- The `MakesliceZeroLive64` premise at a call. -/
@[reducible] def mkzSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  (MakeslicePre64 4096 s ∧ StackRoom64 s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b 0 (s.regs 14).toNat s.mem
      (liveWin64 s 4096 3)) ∧
    typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat = 0 ∧
    Outside (s.regs 0).toNat 16 (calleeStack64 s 4096 3)

/-- `makeslice(uint8, 0, 0)` satisfies it. -/
theorem site_mkz (addr : Nat) : mkzSite R addr [] 0x1000 (callS addr IntBytes.uint8T 0 0) := by
  refine ⟨⟨⟨cs_callOK _ _ _ _ 3 (by omega), ?_, ?_, ?_, ?_⟩, cs_room _ _ _ _ 3 (by omega),
    trivial, cs_inv _ _ _ _, ?_, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 3 (by omega)⟩, ?_, ?_⟩
  all_goals try simp only [makesliceRound64, TypeOK, calleeStack64, cs_mem, cs_r0, cs_r1, cs_r3, cs_sp,
    BitVec.toNat_ofNat]
  all_goals first
    | decide +kernel
    | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)

-- (retired row, top s49: the old witness theorems `returnsF` / `compute1` / `nonvacuous_of` (lengths `0, 0, 0`) were
-- removed with the move to `ModSpecA` / `ExpSpecA` + `Spec.RunAmd64.CpuOne`; the success witness is `RunSucc.Witness`.)

end FvModexp.Amd64.Run.WitnessOk
