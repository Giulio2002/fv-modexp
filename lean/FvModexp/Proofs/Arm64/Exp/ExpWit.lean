import FvModexp.Proofs.Arm64.Exp.CalleeInst
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites
import FvModexp.Proofs.Arm64.Witness.Stubs

set_option autoImplicit false

/-!
# The exp layer (arm64): the shared witness memory of infra's rows (agent infra)

`z = nil`, `stk` = header `{w: OA + 0x200, len: 0, cap: 4}` at `ST = OA + 0x100`, `x = [3]` at `XP`, `y = [5]` at
`YP`, `natOne = {OP, 1, 1}` (header at its `.data` address, word in the `OB` object), the four `math/big` thresholds
`40, 40, 12, 80` at `gA`, the `runtime.writeBarrier` word. The stack region is `[SP0 - 0x20000, SP0 + 0x100)`: the
windows of the rows (`nat.sqr`'s `sqrWX = 70592` below the callers' frames) fit. Used by `P2W2Row`, `P2W4Row`,
`P2DRow` (the call `3^5 mod 2^8`) and `ModInvRow`.
-/

namespace FvModexp.Arm64.ExpWit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy FvModexp
open FvModexp.Arm64.AsmWit FvModexp.Arm64.EvenHyp

set_option maxRecDepth 100000

abbrev ST : Nat := OA + 0x100
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
abbrev OP : Nat := OB + 0x800
/-- `natOne`'s header (`.data`, outside the extracted read-only data) -/
abbrev NA : Nat := 0x704010
abbrev GA : Nat := 0x6d0e80
abbrev WBA : Nat := 0x743640
/-- the budget the witness runtime grants (`toyInv_init_live` admits up to `2^22`) -/
abbrev BW : Nat := 0x400000

theorem gA_eq : RunIface.gA = GA := by decide
theorem wbA_eq : StackNat.wbA = WBA := by decide
theorem nA_eq : natOneA = NA := by decide

def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = OP then 1
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xB0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else if a = GA then 40 else if a = GA + 8 then 40 else if a = GA + 16 then 12 else if a = GA + 24 then 80 else 0

def regs : List Region :=
  ⟨SP0 - 0x20000, 0x20100, true⟩ :: stdRegs.tail ++ [⟨GA, 32, false⟩, ⟨WBA, 8, false⟩, ⟨NA, 24, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

/-- the witness call state at `pc` with argument registers `args` -/
def mkS (pc : Nat) (args : List (BitVec 64)) : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 pc,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

@[simp] theorem mkS_mem (pc : Nat) (args : List (BitVec 64)) : (mkS pc args).mem = mem0 := rfl
@[simp] theorem mkS_sp (pc : Nat) (args : List (BitVec 64)) : (mkS pc args).sp = BitVec.ofNat 64 SP0 := rfl

theorem setup (pc : Nat) (args : List (BitVec 64)) (hl : args.length ≤ 28) :
    CallSetup ((Extracted.program.link WStubs.impl).withExit RET) pc args (mkS pc args) :=
  ⟨rfl, by simp only [mkS, dif_neg (show ¬ 30 < args.length by omega)]; rfl, fun i h => by simp only [mkS, dif_pos h]⟩

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv BW [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem stW0 : stW mem0 ST = OA + 0x200 := by decide +kernel
theorem stLen0 : stLen mem0 ST = 0 := by decide +kernel
theorem stCap0 : stCap mem0 ST = 4 := by decide +kernel

theorem accStk : mem0.accessible (SP0 - 0x20000) 0x20100 true = true := by rw [acc0]; decide +kernel

/-- the window `[lo, hi)` of a row is writable when it lies in the stack region -/
theorem accWin (lo n : Nat) (h1 : SP0 - 0x20000 ≤ lo) (h2 : lo + n ≤ SP0 + 0x100) :
    mem0.accessible lo n true = true :=
  Memory.accessible_sub _ accStk (Or.inr rfl) h1 (by simp only [SP0] at *; omega)

/-- `natOne` for any window list `w` the objects are outside of -/
theorem one0 (L : List (Nat × Nat)) (w : List (Nat × Nat)) (hw1 : Outside NA 24 w) (hw2 : Outside OP 8 w) :
    NatOne R L mem0 OP w := by
  dsimp only [NatOne]
  rw [nA_eq]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, hw1, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, hw2⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide

theorem sa0 : StkApart mem0 ST OP 8 := by
  intro _
  rw [stLen0, stCap0, stW0]
  exact ⟨by simp only [Apart]; decide, fun _ => by simp only [Apart]; decide⟩

/-- the premise of `NewobjectLiveContract` at a call (arm64 twin of divmc's amd64 `AsmWit.noSite`) -/
@[reducible] def noSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1)

/-- a `newobject(Word)` call satisfies it -/
theorem site_no (addr : Nat) : noSite R addr [] 0x1000 (callS addr Extracted.dataAddr.«type:big.Word#51b931e8» 0 0) := by
  refine ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ?_, ?_, ?_⟩, cs_room _ _ _ _ 1 (by omega),
    trivial, cs_inv _ _ _ _, ?_, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  all_goals try simp only [newobjectRound, TypeOK, cs_mem, cs_r0, BitVec.toNat_ofNat]
  all_goals first
    | decide +kernel
    | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩
    | (simp only [calleeStack, cs_sp, BitVec.toNat_ofNat, outside_cons, outside_nil, and_true]; decide +kernel)

end FvModexp.Arm64.ExpWit
