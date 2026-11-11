import FvModexp.Proofs.Arm64.Top.RunOkLib
import FvModexp.Proofs.Arm64.Top.RunErr
import FvModexp.Proofs.Arm64.Witness.StubsMvz

/-!
# Row 1, arm64, success path: `Run` on call data that passes EIP-7823 returns `(compute data (parseLengths data), nil)`

`correctness_ok`: for every input slice whose length headers pass `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns `(out, nil)` with `out = compute data (parseLengths data)` (EthLib), keeping the Go ABI and
the memory frame. The statement uses `FvModexp.Spec.*` (`Spec.RunArm64`: `EnvW`, `Input`, `OkReqs`, `Globals`,
`okBudget`, `OkRet`, `FrameW`).

STATUS (WIP, top s7): the big-number callees `(*Int).Mod`, `(*Int).exp`, `(*Int).Bytes` enter as PREMISES in their
interface shape (`RunIface.ModSpec`/`ExpSpec`/`BytesSpec`, call depth `stkM`/`aboveM`, window `W ≥ 624 + stkM`) until
their machine-code proofs land (divmc / expmc / top); then they are instantiated and `W` fixed.

`WitnessOk.nonvacuous_of`: every hypothesis (except the three callee specs, still premises) and every precondition
conjunct hold together for the toy runtime and the call `Run(c, p, 99, 99)` computing `3 ^ 5 mod 7` (budget `0x300000`
≤ the toy heap's `2^22`, window `0x20000`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- **Row 1, arm64, EIP-7823 success** (WIP: callee specs as premises). -/
theorem correctness_ok (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (stkM aboveM : Nat) (hM : RunIface.ModSpec impl R stkM aboveM) (hE : RunIface.ExpSpec impl R stkM aboveM)
    (hBy : RunIface.BytesSpec impl R stkM aboveM)
    (W : Nat) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
        RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧
        RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  ensOkLib impl hap R hmk hmv hmz hno stkM aboveM hM hE hBy W hW hW1 hab b L c p len cp

end FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
open FvModexp.Spec

namespace FvModexp.Arm64.Run.WitnessOk

open FvModexp.Arm64.Run.Witness (implAt hap ok R mvA mkA noA addr_mv addr_mk addr_no model_mv model_mk model_no ret sp0
  g0 cR pI bytes0 mem0 hret rt_eq)

set_option maxRecDepth 100000

/-- The window of the witness call. -/
def WW : Nat := 0x20000
/-- The budget of the witness call (`okBudget` of the lengths `1, 1, 1` is `2917704`; the toy heap admits `2^22`). -/
def bW : Nat := 0x300000
def gAw : Nat := 0x6d0e80
def wbAw : Nat := 0x743640

theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : RunIface.wbA = wbAw := by decide

/-- Below `0x500000` (the read-only data, the bump cell) the bytes of the error witness; the receiver flags; the call
data: lengths `1, 1, 1` (bytes 31, 63, 95), base `3`, exponent `5`, modulus `7`; the four `math/big` thresholds
`40, 40, 12, 80` at `gA`. -/
def bytes1 (a : Nat) : Byte :=
  if a < 0x500000 then bytes0 a else
  if a = cR then 1 else if a = cR + 1 then 1 else if a = cR + 2 then 1 else
  if a = pI + 31 then 1 else if a = pI + 63 then 1 else if a = pI + 95 then 1 else
  if a = pI + 96 then 3 else if a = pI + 97 then 5 else if a = pI + 98 then 7 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def mem1 : Memory :=
  ⟨bytes1, [⟨sp0 - WW, WW + 40, true⟩, ⟨g0, 0x100, false⟩, ⟨cR, 0x200, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩] ++
    Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def c1 : BitVec 64 := BitVec.ofNat 64 cR
def p1 : BitVec 64 := BitVec.ofNat 64 pI

def s1 : State :=
  { regs := fun i => if i = 0 then c1 else if i = 1 then p1 else if i = 2 then 99 else if i = 3 then 99
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 (segAddr Extracted.program RunArm64.fn),
    flags := ⟨false, false, false, false⟩, mem := mem1 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) (segAddr Extracted.program RunArm64.fn)
    [c1, p1, 99, 99] s1 :=
  ⟨rfl, rfl, by
    intro r h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem data_low : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0x500000 := by decide +kernel

/-- `DataLoaded` from the error witness's (same bytes below `0x500000`, the data regions kept). -/
theorem dataLoaded : Extracted.program.DataLoaded s1.mem := by
  intro d hd
  have h0 := Witness.dataLoaded d hd
  have hlow := data_low d hd
  refine ⟨?_, fun i hi => ?_⟩
  · have h48 : d.base + d.bytes.length ≤ 2 ^ 48 := by omega
    simp only [s1, mem1, List.any_eq_true]
    refine ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_right _ (List.mem_map.2 ⟨d, hd, rfl⟩), ?_⟩
    simp [h48]
  · show (bytes1 (d.base + i)).toNat = _
    rw [bytes1, if_pos (by omega)]
    exact h0.2 i hi

theorem bytes1_heap (i : Nat) (hi : HEAP ≤ i) : bytes1 i = 0 := by
  simp only [HEAP] at hi
  unfold bytes1 cR pI gAw
  repeat rw [if_neg (by omega)]

theorem bytes1_bump : mem1.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 : R.inv bW [] (s1.regs 28).toNat (view R.rt [] s1.mem) :=
  toyInv_init_live (m := mem1) (g := (s1.regs 28).toNat) (p0 := HEAP) (by decide) (by decide +kernel) (by decide +kernel)
    (by intro r hr; simp at hr) bytes1_bump (fun i hi _ => bytes1_heap i hi) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pass1 : LengthsPass (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat) := by
  rw [lengthsPass_iff]; decide +kernel

theorem budget1 : RunArm64.okBudget (parseLengths (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)) ≤ bW := by
  decide +kernel

theorem globals1 : RunArm64.Globals R s1.mem (RunArm64.windowW s1 WW) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide, by decide,
    by decide +kernel, ?_, ?_, by decide +kernel, ?_, ?_⟩
  · show Outside gAw 32 R.rt
    rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · show Outside gAw 32 _
    simp only [RunArm64.windowW, outside_cons, outside_nil, and_true]; decide +kernel
  · show Outside wbAw 4 R.rt
    rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · show Outside wbAw 4 _
    simp only [RunArm64.windowW, outside_cons, outside_nil, and_true]; decide +kernel

theorem pre : RunArm64.EnvW R [] s1 WW ∧ RunArm64.Input R [] c1 p1 99 99 s1 ∧ OsakaReceiver s1.mem c1.toNat ∧
    R.inv bW [] (s1.regs 28).toNat (view R.rt [] s1.mem) ∧ RunArm64.OkReqs R ∧
    RunArm64.Globals R s1.mem (RunArm64.windowW s1 WW) ∧
    RunArm64.okBudget (parseLengths (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)) ≤ bW ∧
    LengthsPass (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat) := by
  refine ⟨⟨⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, dataLoaded, ?_, ?_, ?_,
      by intro r hr; simp at hr, ?_⟩, by intro r hr; simp at hr⟩,
    ⟨by decide +kernel, by decide +kernel, Or.inr ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, Or.inr ?_, ?_⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, inv1,
    ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
      fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩,
    globals1, budget1, pass1⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [Apart]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · intro d hd; rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]
    have : ∀ d' ∈ Extracted.program.data, (d'.base + d'.bytes.length ≤ HEAP ∨ HEND ≤ d'.base) ∧
        (d'.base + d'.bytes.length ≤ BUMP ∨ BUMP + 8 ≤ d'.base) ∧ (d'.base + d'.bytes.length ≤ WBUF ∨ WBUF + 64 ≤ d'.base) := by
      decide +kernel
    exact this d hd
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [RunArm64.window, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [RunArm64.window, outside_cons, outside_nil, and_true]; decide +kernel

theorem model_mvz : MemmoveZeroLive (Extracted.program.ofImpl implAt) mvA 4096 R := WStubs.mvz R

/-- `memmove(dst, src, 0)` call site (the `MemmoveZeroLive` precondition is satisfiable). -/
def sMz : State := Witness.callS mvA (sp0 - 4800) pI 0

theorem site_mz : (sMz.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 sMz ∧
    LiveMemAt R mvA [(sMz.regs 0).toNat, (sMz.regs 1).toNat, (sMz.regs 2).toNat] [] 0x1000 sMz
      (calleeStack sMz 4096 3) :=
  ⟨by decide, ⟨(guardOK_iff _ _).1 (Witness.cs_room mvA _ _ _ 3 (by omega)).1, Witness.cs_callOK _ _ _ _ 3 (by omega),
      (Witness.cs_room mvA _ _ _ 3 (by omega)).2⟩,
    ⟨trivial, Witness.inv_cs _ _ _ _, fun r hr => by simp at hr, Witness.cs_winR _ _ _ _ 3 (by omega)⟩⟩

/-- The returning run at the witness, from `correctness_ok` (given the callee specs). -/
theorem returnsF (stkM aboveM : Nat) (hM : RunIface.ModSpec implAt R stkM aboveM)
    (hE : RunIface.ExpSpec implAt R stkM aboveM) (hBy : RunIface.BytesSpec implAt R stkM aboveM)
    (hW : 624 + stkM ≤ WW) (hab : aboveM ≤ 160) :
    Returns ((Extracted.program.link implAt).withExit ret) s1 fun s' =>
      ABIReturn s1 s' ∧ (RunArm64.OkRet (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat) s' ∧
        RunArm64.FrameW R bW (RunArm64.okBudget (parseLengths (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)))
          [] WW s1 s') :=
  FvModexp.Arm64.Run.correctness_ok implAt hap R (by rw [addr_mk]; exact model_mk) (by rw [addr_mv]; exact model_mv)
    (by rw [addr_mv]; exact model_mvz) (by rw [addr_no]; exact model_no) stkM aboveM hM hE hBy WW hW (by decide) hab
    bW [] c1 p1 99 99 ret hret s1 setup pre

/-- The output at the witness is `[3 ^ 5 mod 7] = [5]` (EthLib `compute` on the witness call data). -/
theorem compute1 : compute (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)
    (parseLengths (bytesAt s1.mem p1.toNat (99 : BitVec 64).toNat)) = ⟨#[5]⟩ := by
  decide +kernel

/-- All hypotheses of `correctness_ok` except the three callee specs (premises until their proofs land) hold together,
with every conjunct of its precondition, and the call returns: the toy runtime, an empty live set, budget `bW`, window
`WW`, and the call `Run(c, p, 99, 99)` computing `3 ^ 5 mod 7`. -/
theorem nonvacuous_of (stkM aboveM : Nat) (hM : RunIface.ModSpec implAt R stkM aboveM)
    (hE : RunIface.ExpSpec implAt R stkM aboveM) (hBy : RunIface.BytesSpec implAt R stkM aboveM)
    (hW : 624 + stkM ≤ WW) (hab : aboveM ≤ 160) :
    ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64)
      (ret : Nat) (s : State) (W : Nat),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    624 + stkM ≤ W ∧ 4800 ≤ W ∧ aboveM ≤ 160 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp] s ∧
    RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
    RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧
    RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
    LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧
    compute (bytesAt s.mem p.toNat len.toNat) (parseLengths (bytesAt s.mem p.toNat len.toNat)) = ⟨#[5]⟩ ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      ((s_c.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s_c ∧
        LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
          (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3))) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  ⟨implAt, R, bW, [], c1, p1, 99, 99, ret, s1, WW, hap, by rw [addr_mk]; exact model_mk, by rw [addr_mv]; exact model_mv,
    by rw [addr_mv]; exact model_mvz, by rw [addr_no]; exact model_no, hW, by decide, hab, hret, setup,
    pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2.1, pre.2.2.2.2.2.1, pre.2.2.2.2.2.2.1, pre.2.2.2.2.2.2.2,
    compute1, ⟨[], 0x1000, sMz, by rw [addr_mv]; rfl, by rw [addr_mv]; exact site_mz⟩,
    returnsF stkM aboveM hM hE hBy hW hab⟩

end FvModexp.Arm64.Run.WitnessOk
