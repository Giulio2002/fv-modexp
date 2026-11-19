import FvModexp.Proofs.Amd64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-! (amd64 twin (asm s55) of the witness part of Arm64/NatQ/DrsRowWQ.lean)
# Row `DrsRowQ` (amd64): the witness state

`q.divRecursiveStep(u, v, 0, nil, stk)` with `q = [0]` at `OA`, `u = [1, 0, 0]` at `OB`, `v = [0, 2^63]` at `VP`,
the stack `{w: OA + 0x200, len 0, cap 4}` at `ST`, budget `0x80000`, reserve level `H = 88`, depth `0`; `v`'s header
`(VP, 2, 2)` is passed on the stack at `SP0 + 8 / + 16 / + 24`. Regions: a 48 KiB stack (the window is `40960`
below / `96` above `SP`), the threshold globals at `gA` (`divRecursiveThreshold = 40` first), `runtime.writeBarrier`'s
flag word and the `math/big.hasADX` byte. Independent of the `divRecursiveStep` proof (row-time: compiled in parallel).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DrsRowQ.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x40` -/
abbrev VP : Nat := OB + 0x40

/-- `u = [1, 0, 0]` at `OB`, `v = [0, 2^63]` at `VP`, the stack header at `ST`, the threshold globals at `gA`,
`v`'s header words `(VP, 2, 2)` at `SP0 + 8 / + 16 / + 24`, all other witness bytes 0 (`q = [0]` at `OA`) -/
def g (a : Nat) : Byte :=
  if a = OB then 1 else if a = VP + 15 then 0x80
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = RunIface.gA then 40 else if a = RunIface.gA + 8 then 40 else if a = RunIface.gA + 16 then 12
  else if a = RunIface.gA + 24 then 80
  else if a = SP0 + 8 then 0x40 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 2 else if a = SP0 + 24 then 2
  else 0

/-- a 48 KiB stack, the other standard regions, the threshold globals, `runtime.writeBarrier`'s flag word and the
`math/big.hasADX` byte -/
def regs : List Janus.Arm64.Region :=
  ⟨SP0 - 0xC000, 0xC100, true⟩ :: stdRegs.tail ++
    [⟨RunIface.gA, 32, true⟩, ⟨StackNat.wbA, 8, false⟩, ⟨Callees.adxAddr, 1, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 3, 3, 0]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 1 else if i = 1 then 1
      else if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 OB else if i = 8 then 3
      else if i = 9 then 3 else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program DivLarge.drsFn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program DivLarge.drsFn)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) :
    mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x80000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  show wbytes (toyBytes g) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega)]
  rw [if_neg (show ¬ i < HEAP from Nat.not_lt.mpr hi)]

theorem cost0Q : Q.drsCQ 3 2 + stkR 88 mem0 ST ≤ 0x80000 := by
  rw [Q.drsCQ_small (by decide)]; decide +kernel

theorem preQ : Q.DivLarge.DrsPre R 0x80000 [] 88 (Q.drsCQ 3 2) OA 1 1 ST OB 3 3 VP 2 2 s0 := by
  have hm : s0.mem = mem0 := rfl
  simp only [Q.DivLarge.DrsPre, Q.DivLarge.DrsPreW, CallEnv, RunIface.Globals, DivLarge.StkIn, StkOK, hm]
  and_intros
  all_goals first
    | (intros; trivial)
    | (exact ⟨by decide +kernel, by rw [hm, acc0]; decide +kernel, by decide +kernel, by decide⟩)
    | (exact ⟨by decide +kernel, by rw [hm, acc0]; decide +kernel, by decide +kernel⟩)
    | (exact ⟨⟨by decide, by decide⟩, by rw [hm, acc0]; decide +kernel, by decide +kernel⟩)
    | (intro _; exact ⟨by simp only [win, outside_cons, outside_nil, and_true]; decide +kernel,
        by simp only [Apart]; decide +kernel⟩)
    | (simp only [List.nil_append, List.append, List.map, List.map_nil, outside_nil]; done)
    | (intro r hr; simp at hr; done)
    | (intro _; and_intros <;> first
        | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
        | (simp only [Apart]; decide +kernel)
        | (rw [acc0]; decide +kernel)
        | decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_nil]; done)
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (simp only [Apart]; decide +kernel)
    | (rw [acc0]; decide +kernel)
    | (simp only [NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq,
        acc0]; decide +kernel)
    | (simp only [Held, InRanges, outside_cons, outside_nil, and_true, rt_eq]; decide +kernel)
    | (simp only [natVal]; decide +kernel)
    | decide +kernel
    | exact inv1 _
    | exact cost0Q
    | exact dataLoaded _ _
    | exact roOut

theorem hty : TysOK [] := by intro t ht; simp at ht

end FvModexp.Amd64.DrsRowQ.Witness
