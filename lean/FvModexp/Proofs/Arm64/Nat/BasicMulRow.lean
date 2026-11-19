import FvModexp.Proofs.Arm64.Nat.BasicMul
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

set_option autoImplicit false

/-!
# Row: `basicMul` (arm64) on the Run extraction
`correctness` = `BasicMul.ens` moved to `Extracted.program.link impl` (`Ensures.full`); runtime premise: the live
`memclrNoHeapPointers` contract. `Witness.nonvacuous`: the shared witness runtime, the toy allocator invariant, the Run
extraction's read-only data in memory, and the call `basicMul(z, x, y)` with `x = 3`, `y = 5` (one limb each) and `z`
two limbs (`len 2`, `cap 2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.BasicMulRow

theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.basicMul")
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (BasicMul.Pre R b L zp zl zc xp xl yp yl) (BasicMul.Post R b L zp xp xl yp yl) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.BasicMul.Pre, FvModexp.Arm64.CallEnv, FvModexp.NatLive, FvModexp.Arm64.win, Janus.Spec.GuardOK, Janus.Spec.StackOK]) hap (BasicMul.ens impl hap R hmc b L zp zl zc xp xl xc yp yl yc)

end FvModexp.Arm64.BasicMulRow

namespace FvModexp.Arm64.BasicMulRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 3` at `OB`, `y = 5` at `OB + 8`, all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 3 else if a = OB + 8 then 5 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 (OB + 8), 1, 1]

/-- the address of `basicMul` -/
abbrev fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.basicMul"

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program fn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) stdRegs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem pre : BasicMul.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 1 (BitVec.ofNat 64 (OB + 8)) 1
    s0 := by
  unfold BasicMul.Pre
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_, trivial⟩, inv1 _⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [NatLive, Held, InRanges, outside_cons, outside_nil, and_true, rt_eq, show s0.mem = mem0 from rfl,
        acc0]; decide +kernel)
    | (simp only [Held, InRanges, outside_cons, outside_nil, and_true, rt_eq]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, `basicMul(z, x, y)` with `x = 3`, `y = 5` (`len 1` each), `len z = cap z = 2`; one
call-site state for the runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc] s ∧
    BasicMul.Pre R b L zp zl zc xp xl yp yl s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ BasicMul.Post R b L zp xp xl yp yl (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 (OB + 8), 1, 1,
    RET, s0, WStubs.hap, by rw [WStubs.addr_cl]; exact WStubs.cl R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_cl]; exact WStubs.cl R) 0x1000 []
      (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 1 1 (BitVec.ofNat 64 (OB + 8)) 1 1 s0 setup pre RET hret⟩

end FvModexp.Arm64.BasicMulRow.Witness
