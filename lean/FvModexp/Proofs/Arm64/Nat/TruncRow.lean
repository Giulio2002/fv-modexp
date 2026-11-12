import FvModexp.Proofs.Arm64.Nat.Trunc
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.AsmWit
import FvModexp.Proofs.Arm64.Witness.Stubs

/-!
# Row: `nat.trunc` (arm64) on the Run extraction

`correctness` = `Trunc.ens` moved to `Extracted.program.link impl` (`Ensures.full`); runtime premises: the live
`makeslice` and `memmove` contracts. `Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`), the toy
allocator invariant, the Run extraction's read-only data loaded, and the call `z.trunc(x, 70)` with an empty `z`
(`cap 0`, so `make(nat, 2, 6)` is requested) and the two-limb `x = 5 + 9·B`; plus one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.TruncRow

/-- **`nat.trunc`** (arm64): `z.trunc(x, n)` returns a normalised nat holding `X mod 2^n`, in `z`'s array (`cap z ≥
min(len x, ⌈n/64⌉)`) or a fresh one; writes only `z`'s array and the window; for every runtime meeting the live
`makeslice`/`memmove` contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc n : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc")
      [zp, zl, zc, xp, xl, xc, n]
      (fun s => Trunc.Pre R b L zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat n.toNat s)
      (fun s s' => Trunc.Post R b L zp.toNat zc.toNat xp.toNat xl.toNat n.toNat s s') :=
  Ensures.full hap (Trunc.ens impl hap R hmk hmv b L zp zl zc xp xl xc n)

end FvModexp.Arm64.TruncRow

namespace FvModexp.Arm64.TruncRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 70]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0,
    pc := BitVec.ofNat 64 (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc"),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET)
    (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc") args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem acc (a n : Nat) (w : Bool) : s0.mem.accessible a n w = (wmem (fun _ => 0) stdRegs).accessible a n w :=
  acc_eq _ a n w

theorem c_guard : GuardOK s0 4208 := ⟨by decide +kernel, by rw [acc]; decide +kernel, by decide +kernel⟩
theorem c_stack : StackOK s0 4208 64 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc]; decide +kernel⟩
theorem c_wrt : Outside (s0.sp.toNat - 4208) (4208 + 64) R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
theorem c_gw : Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4208) (4208 + 64) := by
  simp only [Apart]; decide +kernel
theorem c_grt : Outside ((s0.regs 28).toNat + 16) 8 R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
theorem c_xacc : s0.mem.accessible OB (8 * 2) false = true := by rw [acc]; decide +kernel
theorem c_xrt : Outside OB (8 * 2) R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
theorem c_xw : Outside OB (8 * 2) (win s0 4208 64) := by
  simp only [win, outside_cons, outside_nil, and_true]; decide +kernel

theorem pre : Trunc.Pre R 0x1000 [] OA 0 0 OB 2 70 s0 :=
  ⟨⟨⟨c_guard, c_stack, dataLoaded _ _, c_wrt, c_gw, c_grt, fun r hr => by simp at hr, roOut⟩, WStubs.serves [],
    by decide, ⟨by decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
    ⟨by decide, c_xacc, by decide, Or.inr c_xrt, c_xw⟩, by decide, by decide,
    Or.inr (fun h => absurd h (by decide)), by decide, inv0 g bump _⟩, Or.inr (by decide),
    Or.inr (Or.inr ⟨by decide, by decide⟩)⟩

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime
(toy `makeslice`, looping `memmove`), budget `0x1000`, empty live set, the call `z.trunc(x, 70)` with `cap z = 0`,
`len x = 2`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc n : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc")
      [zp, zl, zc, xp, xl, xc, n] s ∧
    Trunc.Pre R b L zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat n.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Trunc.Post R b L zp.toNat zc.toNat xp.toNat xl.toNat n.toNat s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 70, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) 0x1000 [] (BitVec.ofNat 64 OA) 0 0 (BitVec.ofNat 64 OB) 2 2 70 RET
      hret s0 setup pre⟩

end FvModexp.Arm64.TruncRow.Witness
