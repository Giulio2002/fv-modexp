import FvModexp.Proofs.Amd64.NatQ.RemDefs
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsMvz

set_option autoImplicit false

/-!
# The witness state of the amd64 Q-form `nat.rem` row (`RemRowQ`, `NHyp.RemPreQ`; divmc s59) — twin of asm's
Amd64/NatQ/DivRowWitQ.lean

`z.rem(stk, u, v)` with `z = nil`, `u = 7` at `OB` (registers `RSI, R8, R9`), `v = 3` at `VP` (one limb; passed on the
stack at `RSP + 8 … + 24`), the stack `{w: OA + 0x200, len 0, cap 4}` at `ST`, a 48 KiB goroutine stack (window `41720`
below `RSP`), the threshold globals at their initial values; budget `0x80000`, reserve level `H = 96`
(`stLen + need 1 1 = 85`). `pre` holds for any level-free cost `cd` with `cd 1 1 + stkR 96 mem0 ST ≤ 0x80000`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Amd64.RunIface

namespace FvModexp.Amd64.RemRowQ.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x40` -/
abbrev VP : Nat := OB + 0x40

/-- `u = 7` at `OB`, `v = 3` at `VP`, the stack header at `ST`, the stack argument `v = {VP, 1, 1}` at `SP0 + 8 … + 24`,
the threshold globals, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OB then 7 else if a = VP then 3
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = SP0 + 8 then 0x40 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 1 else if a = SP0 + 24 then 1
  else if a = gA then 40 else if a = gA + 8 then 40 else if a = gA + 16 then 12 else if a = gA + 24 then 80 else 0

/-- a 48 KiB stack, the other standard regions, the threshold globals, `runtime.writeBarrier`'s flag word and the
`math/big.hasADX` byte -/
def regs : List Janus.Arm64.Region :=
  ⟨SP0 - 0xC000, 0xC100, true⟩ :: stdRegs.tail ++
    [⟨gA, 32, true⟩, ⟨StackNat.wbA, 8, false⟩, ⟨Callees.adxAddr, 1, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 1, 1]

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 OB
      else if i = 8 then 1 else if i = 9 then 1 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program Q.NatRem.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program Q.NatRem.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

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

theorem rtOut (a n : Nat) (h : WBUF + 64 ≤ a ∧ a + n ≤ HEAP) : Outside a n R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; simp only [BUMP, HEAP, WBUF] at *; omega

theorem len0 : stLen mem0 ST = 0 := by decide +kernel

/-- the stack argument `v = {VP, 1, 1}` -/
theorem words : s0.mem.readLE ((s0.regs 4).toNat + 8) 8 = (BitVec.ofNat 64 VP).toNat ∧
    s0.mem.readLE ((s0.regs 4).toNat + 16) 8 = (1 : BitVec 64).toNat ∧
    s0.mem.readLE ((s0.regs 4).toNat + 24) 8 = (1 : BitVec 64).toNat :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- the row's cost instance (`div`'s with asm's `drsCQ`) fits the witness budget -/
theorem cost0Q : Q.NatDiv.costQ Q.drsCQ 1 1 + stkR 96 mem0 ST ≤ 0x80000 := by
  simp only [Q.NatDiv.costQ, Q.DivLarge.costQ]; rw [Q.drsCQ_small (by decide)]; decide +kernel

theorem pre (cd : Nat → Nat → Nat) (hc : cd 1 1 + stkR 96 mem0 ST ≤ 0x80000) :
    NHyp.RemPreQ R 0x80000 96 [] 41720 112 0 0 0 ST OB 1 1 VP 1 1 (Q.NatRem.need 1 1)
      (cd 1 1 + stkR 96 s0.mem ST) s0 := by
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.regs 4 = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 14 = BitVec.ofNat 64 G0 := rfl
  simp only [NHyp.RemPreQ, NHyp.freeOf, NHyp.NoAlias, CallEnv, Globals, EvenHyp.WrOut, EvenHyp.RdIn,
    ExpHyp.StackOK', StkOK, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false, hm, hsp, hg]
  and_intros
  all_goals first
    | exact inv1 _
    | exact hc
    | (rw [len0]; decide)
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | (intro r hr; simp at hr; done)
    | (intro p n hpn; rcases hpn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> and_intros <;> first
        | (simp only [acc0] <;> decide +kernel)
        | exact Or.inr (rtOut _ _ (by decide +kernel))
        | (simp only [win, outside_cons, outside_nil, and_true] <;> decide +kernel)
        | (unfold NatNorm; right; decide +kernel)
        | (unfold Apart <;> decide +kernel)
        | (intro h; exact absurd h (by decide))
        | decide +kernel)
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
    | (intro h; exact absurd h (by decide))
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [hm, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [hm, acc0]; decide +kernel)
    | (intros; trivial)
    | decide +kernel

end FvModexp.Amd64.RemRowQ.Witness
