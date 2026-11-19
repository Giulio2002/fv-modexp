import FvModexp.Proofs.Arm64.Nat.DivW
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.AsmWit
import FvModexp.Proofs.Arm64.Witness.StubsMvz
import FvModexp.Proofs.Arm64.Int.ModRowW

/-!
# Row: `nat.divW` (arm64) on the Run extraction

`correctness` = `DivW.ens` moved to `Extracted.program.link impl` (`Ensures.full`); runtime premises: the live
`makeslice` and `memmove` contracts and the zero-length `memmove` contract (Janus PR #2, `MemmoveZeroLive`). `Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`), the toy
allocator invariant, the Run extraction's read-only data loaded, and the call `z.divW(x, 3)` with an empty `z`
(`cap 0`, so `make(nat, 2, 6)` is requested) and the two-limb `x = 5 + 9·B`; plus one call-site state per contract (incl. `MemmoveZeroLive`'s).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivWRow

/-- **`nat.divW`** (arm64): `z.divW(x, y)` returns a normalised nat holding `X / y` (in `z`'s array or a fresh one) and
`X % y`; writes only `z`'s array and the window; for every runtime meeting the live `makeslice`/`memmove` contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivW.fn) [zp, zl, zc, xp, xl, xc, y]
      (DivW.Pre R b L zp zc xp xl y) (DivW.Post R b L zp zc xp xl y) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.DivW.Pre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.DivW.wordT, FvModexp.NatLive, FvModexp.Arm64.win, FvModexp.NatNorm, Janus.Spec.GuardOK, Janus.Spec.StackOK]) hap (DivW.ens impl hap R hmk hmv hmz b L zp zl zc xp xl xc y)

end FvModexp.Arm64.DivWRow

namespace FvModexp.Arm64.DivWRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program DivW.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program DivW.fn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem top : mem0.readLE (OB + 8 * (2 - 1)) 8 ≠ 0 := by decide +kernel

theorem pre : DivW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 0 (BitVec.ofNat 64 OB) 2 3 s0 := by
  refine ⟨⟨⟨by decide +kernel, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel,
      by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel⟩,
    dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, ?_, by decide, by decide, by decide,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
    by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel, by decide, Or.inr ?_,
    Or.inr top, ?_, ?_, fun _ => ⟨trivial, by decide⟩, fun _ _ _ _ => trivial, fun h => absurd h (by decide)⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | exact inv0 g bump _

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime
(toy `makeslice`, looping `memmove`), budget `0x1000`, empty live set, the call `z.divW(x, 3)` with `cap z = 0`,
`len x = 2`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc y : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program DivW.fn)
      [zp, zl, zc, xp, xl, xc, y] s ∧
    DivW.Pre R b L zp zc xp xl y s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      (s_c.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s_c ∧
      LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
        (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3)) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧ DivW.Post R b L zp zc xp xl y (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, by rw [WStubs.addr_mv]; exact WStubs.mvz R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mz _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R) 0x1000 [] (BitVec.ofNat 64 OA) 0 0 (BitVec.ofNat 64 OB) 2 2 3 s0 setup pre RET
      hret⟩

end FvModexp.Arm64.DivWRow.Witness
