import FvModexp.Proofs.Arm64.Nat.SubVW
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.AsmWit

/-!
# Row: `subVW` (arm64) on the Run extraction

`correctness` = `SubVW.ens` moved to `Extracted.program.link impl` (`Ensures.full`); its one runtime premise is the live
`memmove` contract. `Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, looping `memmove`), the toy
allocator invariant, and the call `subVW(z[0:2], x[0:2], 1)` with `z`, `x` two-limb arrays apart (so `copy` calls
`memmove`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SubVWRow

/-- **`subVW`** (arm64): `z[0:n] = (x[0:n] + B^n - y) mod B^n`, borrow in `X0`; writes only `z[0:n]` and the
window; for every runtime meeting the live `memmove` contract. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program SubVW.fn) [zp, zl, zc, xp, xl, xc, y]
      (fun s => xl = zl ∧ SubVW.Pre R b L zp zl zc xp xc s) (fun s s' => SubVW.Post R b L zp zl xp y s s') :=
  Ensures.full hap (SubVW.ens impl hap R hmv b L zp zl zc xp xl xc y)

end FvModexp.Arm64.SubVWRow

namespace FvModexp.Arm64.SubVWRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x[0] = 5` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 2, 2, 1]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program SubVW.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program SubVW.fn)
    args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem pre : (2 : BitVec 64) = 2 ∧ SubVW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 2 s0 := by
  refine ⟨rfl, ⟨⟨by decide +kernel, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel⟩,
    ?_, ?_, ?_, fun r hr => by simp at hr⟩, by decide, by decide, by decide, by decide, fun _ => ⟨by decide,
    Or.inr ?_, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel, by decide⟩, ?_, fun _ => ?_,
    by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel, by decide, Or.inr ?_, ?_, Or.inr ?_, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | exact inv0 g bump _
    | (rw [if_neg (by decide)]; intro j _ _; trivial)

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
the toy allocator, budget `0x1000`, empty live set, the call `subVW(z[0:2], x[0:2], 1)`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc y : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program SubVW.fn)
      [zp, zl, zc, xp, xl, xc, y] s ∧
    (xl = zl ∧ SubVW.Pre R b L zp zl zc xp xc s) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ SubVW.Post R b L zp zl xp y s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 2, 2, 1, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mv]; exact WStubs.mv R) 0x1000 [] (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 2 2 1 RET hret s0 setup pre⟩

end FvModexp.Arm64.SubVWRow.Witness
