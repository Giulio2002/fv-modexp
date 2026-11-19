import FvModexp.Proofs.Arm64.Witness.Sites
import FvModexp.Proofs.Arm64.Nat.Callees
import FvModexp.Proofs.Arm64.Nat.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.MulDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# Row `DrsRowQ` (arm64): the witness facts and the `nat.mul` code inclusion, Q-form (TIGHT COSTS, asm s39/s42)

The witness of `DrsRow` (`u = [1, 0, 0]`, `v = [0, 2^63]`, `q = [0]`, the stack `{w, 0, 4}`, budget `0x80000`) at the
reserve level `H = 88` (`= stLen + 12·len v + 64`); the level-free cost `drsCQ 3 2 = 0`. The witness definitions are
copied from Arm64/Nat/DrsRowW.lean (namespace `DrsRowQ.Witness`) so that this row does not import the old `nat.mul`
chain (asm s42, row-time trim).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.DrsRowQ

open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

theorem mul_ns : Q.NatMul.names.contains DivRec.fn = false := by decide

theorem mul_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn ((Extracted.program.onlySegments Q.NatMul.names).link impl) (LibDrs.program.link impl) := by
  rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide))

end FvModexp.Arm64.DrsRowQ

namespace FvModexp.Arm64.DrsRowQ.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x40` -/
abbrev VP : Nat := OB + 0x40

/-- `u = [1, 0, 0]` at `OB`, `v = [0, 2^63]` at `VP`, the stack header at `ST`, the threshold globals, all other
witness bytes 0 (`q = [0]` at `OA`) -/
def g (a : Nat) : Byte :=
  if a = OB then 1 else if a = VP + 15 then 0x80
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = gA then 40 else if a = gA + 8 then 40 else if a = gA + 16 then 12 else if a = gA + 24 then 80 else 0

/-- a 48 KiB stack, the other standard regions, `runtime.writeBarrier`'s flag word, the threshold globals -/
def regs : List Region := ⟨SP0 - 0xC000, 0xC100, true⟩ :: stdRegs.tail ++ [⟨StackNat.wbA, 8, false⟩, ⟨gA, 32, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 3, 3, BitVec.ofNat 64 VP, 2, 2, 0]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program DivLarge.drsFn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x80000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem rtOut (a n : Nat) (h : WBUF + 64 ≤ a ∧ a + n ≤ HEAP) : Outside a n R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; simp only [BUMP, HEAP, WBUF] at *; omega

theorem len0 : stLen mem0 ST = 0 := by decide +kernel

theorem cost0Q : Q.drsCQ 3 2 + stkR 88 mem0 ST ≤ 0x80000 := by
  rw [Q.drsCQ_small (by decide)]; decide +kernel

theorem preQ : Q.DivLarge.DrsPre R 0x80000 [] 88 (Q.drsCQ 3 2) OA 1 1 ST OB 3 3 VP 2 2 s0 := by
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.sp = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 28 = BitVec.ofNat 64 G0 := rfl
  simp only [Q.DivLarge.DrsPre, Q.DivLarge.DrsPreW, CallEnv, Globals, EvenHyp.StkIn, ExpHyp.StackOK', StkOK, hm, hsp, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ⟨by decide +kernel, cost0Q⟩, inv1 _⟩
  all_goals try and_intros
  all_goals first
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | (intro r hr; simp at hr; done)
    | (intros; trivial)
    | (intro p c hpc hc; rcases hpc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> exact absurd hc (by omega))
    | (intro _; and_intros <;> first
        | (simp only [acc0] <;> decide +kernel)
        | exact Or.inr (rtOut _ _ (by decide +kernel))
        | (simp only [win, stW, stCap, outside_cons, outside_nil, and_true] <;> decide +kernel)
        | (unfold Apart <;> decide +kernel)
        | decide +kernel)
    | (simp only [NatLive]; intro h; exact absurd h (by decide))
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (show _ = _; decide)
    | (exact Or.inr (rtOut _ _ (by decide +kernel)))
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)),
        by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (intro h; exact absurd h (by decide))
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (intro _; exact ⟨by unfold Apart; decide +kernel, by unfold Apart; decide +kernel⟩)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | (simp only [natVal] <;> decide +kernel)
    | (simp only [Held, InRanges] <;> exact Or.inr (rtOut _ _ (by decide +kernel)))
    | decide +kernel

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program DivLarge.drsFn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem hty : TysOK [] := by intro t ht; simp at ht

end FvModexp.Arm64.DrsRowQ.Witness
