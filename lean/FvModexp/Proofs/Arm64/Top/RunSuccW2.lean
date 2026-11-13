import FvModexp.Proofs.Arm64.Top.RunOkRow

set_option autoImplicit false

/-!
# A real-exponentiation witness state for the arm64 success row (`3^5 mod 7`), prepared for TIGHT COSTS (top s36)

The success witness of `Top/RunSucc` runs `Run` on 99 zero bytes (lengths `0, 0, 0`), because with the `2^32` slack of
`RunIface.ExpBudget` no input with a nonzero length fits the toy heap's budget. BRIEF "TIGHT COSTS" requires a witness that
runs a real exponentiation: this module builds that call — `Run(c, p, 99, 99)` on the call data with lengths `1, 1, 1`,
`B = 3`, `E = 5`, `M = 7` — with every precondition conjunct proved except the cost bound (`pre2`'s premise `budget2`,
discharged by `decide +kernel` once the budget is restored), and `compute2`: the EthLib output is `[5]`.
Same runtime, window, budget and memory layout as `Run.WitnessOk` (only the call-data bytes differ).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run.WitnessOk

open FvModexp.Arm64.Run.Witness (implAt hap ok R mvA mkA noA addr_mv addr_mk addr_no model_mv model_mk model_no ret sp0
  g0 cR pI bytes0 mem0 hret rt_eq)

set_option maxRecDepth 100000

/-- Below `0x500000` (the read-only data, the bump cell) the bytes of the error witness; the receiver flags; the call
data: lengths `1, 1, 1` and `B = 3`, `E = 5`, `M = 7` (99 bytes; `3^5 mod 7 = 5`); the four `math/big` thresholds
`40, 40, 12, 80` at `gA`. -/
def bytes2 (a : Nat) : Byte :=
  if a < 0x500000 then bytes0 a else
  if a = cR then 1 else if a = cR + 1 then 1 else if a = cR + 2 then 1 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else
  if a = nAw + 1 then 0x0f else if a = nAw + 2 then 0x6d else if a = nAw + 8 then 1 else if a = nAw + 16 then 1 else
  if a = opw then 1 else
  if a = pI + 31 then 1 else if a = pI + 63 then 1 else if a = pI + 95 then 1 else
  if a = pI + 96 then 3 else if a = pI + 97 then 5 else if a = pI + 98 then 7 else 0

def mem2 : Memory :=
  ⟨bytes2, [⟨sp0 - WW, WW + 40, true⟩, ⟨g0, 0x100, false⟩, ⟨cR, 0x200, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨nAw, 24, true⟩, ⟨opw, 8, true⟩] ++
    Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def c2 : BitVec 64 := BitVec.ofNat 64 cR
def p2 : BitVec 64 := BitVec.ofNat 64 pI

def s2 : State :=
  { regs := fun i => if i = 0 then c2 else if i = 1 then p2 else if i = 2 then 99 else if i = 3 then 99
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 (segAddr Extracted.program RunArm64.fn),
    flags := ⟨false, false, false, false⟩, mem := mem2 }

theorem setup2 : CallSetup ((Extracted.program.link implAt).withExit ret) (segAddr Extracted.program RunArm64.fn)
    [c2, p2, 99, 99] s2 :=
  ⟨rfl, rfl, by
    intro r h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem data_low2 : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0x500000 := by decide +kernel

/-- `DataLoaded` from the error witness's (same bytes below `0x500000`, the data regions kept). -/
theorem dataLoaded2 : Extracted.program.DataLoaded s2.mem := by
  intro d hd
  have h0 := Witness.dataLoaded d hd
  have hlow := data_low2 d hd
  refine ⟨?_, fun i hi => ?_⟩
  · have h48 : d.base + d.bytes.length ≤ 2 ^ 48 := by omega
    simp only [s2, mem2, List.any_eq_true]
    refine ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_right _ (List.mem_map.2 ⟨d, hd, rfl⟩), ?_⟩
    simp [h48]
  · show (bytes2 (d.base + i)).toNat = _
    rw [bytes2, if_pos (by omega)]
    exact h0.2 i hi

theorem bytes2_heap (i : Nat) (hi : HEAP ≤ i) : bytes2 i = 0 := by
  simp only [HEAP] at hi
  unfold bytes2 cR pI gAw nAw opw
  repeat rw [if_neg (by omega)]

theorem bytes2_bump : mem2.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv2 : R.inv bW [] (s2.regs 28).toNat (view R.rt [] s2.mem) :=
  toyInv_init_live (m := mem2) (g := (s2.regs 28).toNat) (p0 := HEAP) (by decide) (by decide +kernel) (by decide +kernel)
    (by intro r hr; simp at hr) bytes2_bump (fun i hi _ => bytes2_heap i hi) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pass2 : LengthsPass (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat) := by
  rw [lengthsPass_iff]; decide +kernel

theorem globals2 : RunArm64.Globals R s2.mem (RunArm64.windowW s2 WW) := by
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

theorem op2 : s2.mem.readLE RunIface.natOneA 8 = opw := by rw [nA_eq]; decide +kernel

theorem one2 : RunArm64.NatOne R s2.mem (RunArm64.windowW s2 WW) := by
  dsimp only [RunArm64.NatOne]
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» = RunIface.natOneA from rfl, op2,
    nA_eq]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel,
    by decide, ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [RunArm64.windowW, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [RunArm64.windowW, outside_cons, outside_nil, and_true]; decide +kernel

theorem pool2 : RunArm64.StackPool R s2.mem (RunArm64.windowW s2 WW) := by
  dsimp only [RunArm64.StackPool]
  refine ⟨?_, by decide +kernel, ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [RunArm64.windowW, outside_cons, outside_nil, and_true]; decide +kernel

theorem pre2 (budget2 : RunArm64.okBudget (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) ≤ bW) :
    RunArm64.EnvW R [] s2 WW ∧ RunArm64.Input R [] c2 p2 99 99 s2 ∧ OsakaReceiver s2.mem c2.toNat ∧
    R.inv bW [] (s2.regs 28).toNat (view R.rt [] s2.mem) ∧ RunArm64.OkReqs R ∧
    RunArm64.Globals R s2.mem (RunArm64.windowW s2 WW) ∧ RunArm64.NatOne R s2.mem (RunArm64.windowW s2 WW) ∧
    RunArm64.StackPool R s2.mem (RunArm64.windowW s2 WW) ∧
    RunArm64.okBudget (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) ≤ bW ∧
    LengthsPass (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat) := by
  refine ⟨⟨⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, dataLoaded2, ?_, ?_, ?_,
      by intro r hr; simp at hr, ?_⟩, by intro r hr; simp at hr⟩,
    ⟨by decide +kernel, by decide +kernel, Or.inr ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, Or.inr ?_, ?_⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, inv2,
    ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
      fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩,
    globals2, one2, pool2, budget2, pass2⟩
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

/-- The output at the witness is `[5]` (EthLib `compute` on lengths `1, 1, 1`, `3^5 mod 7`). -/
theorem compute2 : compute (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)
    (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) = ⟨#[5]⟩ := by
  decide +kernel

end FvModexp.Arm64.Run.WitnessOk
