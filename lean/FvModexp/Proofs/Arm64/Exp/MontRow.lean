import FvModexp.Proofs.Arm64.Exp.Mont
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites
import FvModexp.Proofs.Arm64.Witness.Stubs

/-!
# Calibration row: `nat.montgomery` (arm64) verified standalone on the Run extraction
`correctness` = `Mont.ens` moved to `Extracted.program.link impl` (`Ensures.full`, divmc's RowLink).
`Witness.nonvacuous`: the shared witness runtime, `montgomery(z, x, y, m, k, 1)` with `x = 3`, `y = 5`, `m = 7`,
`k = 0`, `len z = cap z = 2`; one call-site state per runtime contract (expmc s53).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.MontRow

theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc mp ml mc k n : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery")
      [zp, zl, zc, xp, xl, xc, yp, yl, yc, mp, ml, mc, k, n]
      (Mont.Pre R b L zp zc xp xl yp yl mp ml mc k n) (Mont.Post R b L zp zc xp yp mp k n) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.Mont.Pre, FvModexp.Arm64.Mont.Env, FvModexp.Arm64.Mont.Input, Janus.Spec.GuardOK, Janus.Spec.StackOK]) hap (Mont.ens impl hap R hclr hmv b L zp zl zc xp xl xc yp yl yc mp ml mc k n)

end FvModexp.Arm64.MontRow

namespace FvModexp.Arm64.MontRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 3` at `OB`, `y = 5` at `OB + 8`, `m = 7` at `OB + 16`, all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 3 else if a = OB + 8 then 5 else if a = OB + 16 then 7 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 (OB + 8), 1, 1, BitVec.ofNat 64 (OB + 16), 1, 1,
    0, 1]

/-- the address of `montgomery` -/
abbrev fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery"

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

theorem pre : Mont.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 (BitVec.ofNat 64 OB) 1 (BitVec.ofNat 64 (OB + 8)) 1
    (BitVec.ofNat 64 (OB + 16)) 1 1 0 1 s0 := by
  unfold Mont.Pre Mont.Env Mont.Input GuardOK StackOK
  repeat' apply And.intro
  all_goals first
    | exact inv1 _
    | trivial
    | (intro r hr; simp at hr)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = mem0 from rfl, acc0]; decide +kernel)
    | (simp only [Held, InRanges, outside_cons, outside_nil, and_true, rt_eq]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, `montgomery(z, x, y, m, 0, 1)` with `x = 3`, `y = 5`, `m = 7`, `len z = cap z = 2`;
one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc mp ml mc k n : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc, mp, ml, mc, k, n] s ∧
    Mont.Pre R b L zp zc xp xl yp yl mp ml mc k n s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ Mont.Post R b L zp zc xp yp mp k n (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 (OB + 8), 1, 1,
    BitVec.ofNat 64 (OB + 16), 1, 1, 0, 1, RET, s0, WStubs.hap, by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      0x1000 [] (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 1 1 (BitVec.ofNat 64 (OB + 8)) 1 1
      (BitVec.ofNat 64 (OB + 16)) 1 1 0 1 s0 setup pre RET hret⟩

end FvModexp.Arm64.MontRow.Witness
