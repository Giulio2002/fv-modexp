import FvModexp.Proofs.Arm64.Nat.DivWVW
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.AsmWit

/-!
# Row: `divWVW` (arm64) on the Run extraction

`correctness` = `DivWVW.ens` moved to `Extracted.program.link impl` (`Ensures.full`); no runtime premise (the callees
`reciprocalWord`, `math/bits.Div64`, `divWW` are proved summaries inside `DivWVW.names`). `Witness.nonvacuous`: the shared
witness runtime, the toy allocator invariant, the Run extraction's read-only data loaded (`AsmWit.dataLoaded`), and the
call `divWVW(z[0:2], 0, x[0:2], 7)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivWVWRow

/-- **`divWVW`** (arm64): `X0 = (xn·B^n + x) mod y`, `z[0:n] = (xn·B^n + x) / y`; writes only `z[0:n]` and the window;
for every runtime. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivWVW.fn) [zp, zl, zc, xn, xp, xl, xc, y]
      (fun s => xl = zl ∧ DivWVW.Pre R b L zp zl xn xp y s) (fun s s' => DivWVW.Post R b L zp zl xn xp y s s') :=
  Ensures.full hap (DivWVW.ens impl hap R b L zp zl zc xn xp xl xc y)

end FvModexp.Arm64.DivWVWRow

namespace FvModexp.Arm64.DivWVWRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 2, 2, 0, BitVec.ofNat 64 OB, 2, 2, 7]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program DivWVW.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program DivWVW.fn)
    args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem pre : (2 : BitVec 64) = 2 ∧ DivWVW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 0 (BitVec.ofNat 64 OB) 7 s0 := by
  refine ⟨rfl, ⟨⟨by decide +kernel, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel,
      by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel⟩,
    dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, by decide, by decide,
    fun _ => ⟨by decide, Or.inr ?_, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel,
      by decide⟩, ?_,
    by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel, by decide, Or.inr ?_, ?_,
    Or.inr ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | exact inv0 g bump _

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
the toy allocator, budget `0x1000`, empty live set, the call `divWVW(z[0:2], 0, x[0:2], 7)`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xn xp xl xc y : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program DivWVW.fn)
      [zp, zl, zc, xn, xp, xl, xc, y] s ∧
    (xl = zl ∧ DivWVW.Pre R b L zp zl xn xp y s) :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, 0, BitVec.ofNat 64 OB, 2, 2, 7, RET, s0, WStubs.hap,
    hret, setup, pre⟩

end FvModexp.Arm64.DivWVWRow.Witness
