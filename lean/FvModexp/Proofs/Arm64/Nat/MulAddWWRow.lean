import FvModexp.Proofs.Arm64.Nat.MulAddWW
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.AsmWit

/-!
# Row: `nat.mulAddWW` (arm64) on the Run extraction

`correctness` = `MulAddWW.ens` moved to `Extracted.program.link impl` (`Ensures.full`); its one runtime premise is the
live `makeslice` contract. `Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, toy bump `makeslice`), the
toy allocator invariant, the Run extraction's read-only data loaded, and the call `z.mulAddWW(x, 3, 0)` with an empty
`z` (`cap 0`, so `make(nat, 3, 7)` is requested) and a two-limb `x`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.MulAddWWRow

/-- **`nat.mulAddWW`** (arm64): returns a normalised nat holding `X·y + r` in `z`'s array or a fresh one; writes only
`z`'s array and the window; for every runtime meeting the live `makeslice` contract. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program MulAddWW.fn) [zp, zl, zc, xp, xl, xc, y, r]
      (MulAddWW.Pre R b L zp zc xp xl y r) (MulAddWW.Post R b L zp zc xp xl y r) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.MulAddWW.Pre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.MulAddWW.wordT, FvModexp.NatLive, FvModexp.Arm64.win, Janus.Spec.GuardOK, Janus.Spec.StackOK]) hap (MulAddWW.ens impl hap R hmk b L zp zl zc xp xl xc y r)

end FvModexp.Arm64.MulAddWWRow

namespace FvModexp.Arm64.MulAddWWRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3, 0]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program MulAddWW.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program MulAddWW.fn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem pre : MulAddWW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 0 (BitVec.ofNat 64 OB) 2 3 0 s0 := by
  refine ⟨⟨⟨by decide +kernel, by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel,
      by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel⟩,
    dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, ?_, by decide, by decide,
    fun h => absurd h (by decide), ?_, fun h => absurd h (by decide),
    by rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel, by decide, Or.inr ?_, ?_, ?_,
    fun _ => ⟨trivial, by decide⟩⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | exact inv0 g bump _

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime
(toy `makeslice`), budget `0x1000`, empty live set, the call `z.mulAddWW(x, 3, 0)` with `cap z = 0`, `len x = 2`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc y r : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program MulAddWW.fn)
      [zp, zl, zc, xp, xl, xc, y, r] s ∧
    MulAddWW.Pre R b L zp zc xp xl y r s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧ MulAddWW.Post R b L zp zc xp xl y r (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3, 0, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl, by rw [WStubs.addr_mk]; exact site_mk _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _) 0x1000 [] (BitVec.ofNat 64 OA) 0 0 (BitVec.ofNat 64 OB) 2 2 3 0 s0 setup pre RET hret⟩

end FvModexp.Arm64.MulAddWWRow.Witness
