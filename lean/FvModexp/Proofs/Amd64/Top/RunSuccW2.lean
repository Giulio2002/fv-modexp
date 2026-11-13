import FvModexp.Proofs.Amd64.Top.RunOkRow

set_option autoImplicit false

/-!
# A real-exponentiation witness state for the amd64 success row (`3^5 mod 7`), prepared for TIGHT COSTS (top s36)

Twin of `Arm64/Top/RunSuccW2.lean`: `Run(c, p, 99, 99)` on the call data with lengths `1, 1, 1`, `B = 3`, `E = 5`,
`M = 7`, same runtime/window/budget/layout as `Run.WitnessOk`; every precondition conjunct proved except the cost bound
(`pre2`'s premise `budget2`, discharged once the budget is restored); `compute2`: the EthLib output is `[5]`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run.WitnessOk

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- The receiver's three flags (at `OA`) are 1; the call data (at `OB`): lengths `1, 1, 1`, `B = 3`, `E = 5`, `M = 7`
(99 bytes; `3^5 mod 7 = 5`); the four `math/big` thresholds `40, 40, 12, 80` at `gA`; all other witness bytes 0. -/
def g2 (a : Nat) : Byte :=
  if a = OA ∨ a = OA + 1 ∨ a = OA + 2 then 1 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else
  if a = nAw + 1 then 0xaf else if a = nAw + 2 then 0xb4 else if a = nAw + 8 then 1 else if a = nAw + 16 then 1 else
  if a = opw then 1 else
  if a = OB + 31 then 1 else if a = OB + 63 then 1 else if a = OB + 95 then 1 else
  if a = OB + 96 then 3 else if a = OB + 97 then 5 else if a = OB + 98 then 7 else 0

/-- `stdRegs` with the stack region grown to the window `WW` and the globals' regions. -/
def regs2 : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨nAw, 24, true⟩, ⟨opw, 8, true⟩]

abbrev mem2 : Janus.Arm64.Memory := wmem (toyBytes g2) regs2

def c2 : BitVec 64 := BitVec.ofNat 64 OA
def p2 : BitVec 64 := BitVec.ofNat 64 OB

def s2 : State :=
  { regs := fun i => if i = 0 then c2 else if i = 3 then p2 else if i = 1 then 99 else if i = 7 then 99
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program RunAmd64.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem2, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem setup2 : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program RunAmd64.fn)
    [c2, p2, 99, 99] s2 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump2 : mem2.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv2 (gp : Nat) : R.inv bW [] gp (view R.rt [] mem2) := by
  refine toyInv_init_live (m := mem2) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump2 (fun i hi hi' => ?_) (by rw [acc_eq (toyBytes g2)]; decide +kernel)
    (by rw [acc_eq (toyBytes g2)]; decide +kernel) (by rw [acc_eq (toyBytes g2)]; decide +kernel)
  show wbytes (toyBytes g2) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem pass2 : LengthsPass (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat) := by
  rw [lengthsPass_iff]; decide +kernel

theorem globals2 : RunAmd64.Globals R s2.mem (RunAmd64.windowW s2 WW) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.windowW, outside_cons, outside_nil, and_true]; decide +kernel)
    | (rw [show s2.mem = wmem (toyBytes g2) regs2 from rfl, acc_eq]; decide +kernel)

theorem op2 : s2.mem.readLE RunIface.natOneA 8 = opw := by rw [nA_eq]; decide +kernel

theorem one2 : RunAmd64.NatOne R s2.mem (RunAmd64.windowW s2 WW) := by
  dsimp only [RunAmd64.NatOne]
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» = RunIface.natOneA from rfl, op2,
    nA_eq]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_, by decide, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.windowW, outside_cons, outside_nil, and_true]; decide +kernel)
    | (rw [show s2.mem = wmem (toyBytes g2) regs2 from rfl, acc_eq]; decide +kernel)

theorem pool2 : RunAmd64.StackPool R s2.mem (RunAmd64.windowW s2 WW) := by
  dsimp only [RunAmd64.StackPool]
  refine ⟨?_, by decide +kernel, ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [RunAmd64.windowW, outside_cons, outside_nil, and_true]; decide +kernel

theorem pre2 (budget2 : RunAmd64.okBudget (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) ≤ bW) :
    RunAmd64.EnvW R [] s2 WW ∧ RunAmd64.Input R [] c2 p2 99 99 s2 ∧ OsakaReceiver s2.mem c2.toNat ∧
    R.inv bW [] (s2.regs 14).toNat (view R.rt [] s2.mem) ∧ RunAmd64.OkReqs R ∧
    RunAmd64.Globals R s2.mem (RunAmd64.windowW s2 WW) ∧ RunAmd64.NatOne R s2.mem (RunAmd64.windowW s2 WW) ∧
    RunAmd64.StackPool R s2.mem (RunAmd64.windowW s2 WW) ∧
    RunAmd64.okBudget (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) ≤ bW ∧
    LengthsPass (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat) := by
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩, fun r hr => by simp at hr, fun r hr => by simp at hr⟩,
    ⟨?_, by decide, Or.inr ?_, ?_, by decide, by decide, by decide, ?_, Or.inr ?_, ?_⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, inv2 _,
    ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
      fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩,
    globals2, one2, pool2, budget2, pass2⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.window, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s2.mem = wmem (toyBytes g2) regs2 from rfl, acc_eq]; decide +kernel)
    | decide +kernel

/-- The output at the witness is `[5]` (EthLib `compute` on lengths `1, 1, 1`, `3^5 mod 7`). -/
theorem compute2 : compute (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)
    (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) = ⟨#[5]⟩ := by
  decide +kernel

end FvModexp.Amd64.Run.WitnessOk
