import FvModexp.Proofs.Amd64.Exp.W4FunE
import FvModexp.Proofs.Amd64.Witness.AsmWit
import FvModexp.Proofs.Amd64.Witness.Stubs

set_option autoImplicit false

/-!
# window-4 (amd64): witness state for the row (non-vacuity of `ExpW4.PreD`; agent expmc s59)

`z = nil`, `stk` = header `{w: OA + 0x200, len: 0, cap: 4}` at `ST = OA + 0x100`, `x = [3]` at `XP`, `y = [5]` at `YP`,
`m = [7]` at `MP` (the call `3^5 mod 7`); `y` and `m` (with `n`, `mc`) are the stack arguments at `RSP + 8 …`. The entry
`RSP = SP0 + 8` (Go's `RSP ≡ 8 mod 16` at entry: the frame `sp = RSP - 0x388` is 16-aligned), the return address
`RET` at `RSP`, a 64 KiB stack region (window depth `K = 41512`, `nat.div`'s), the four `math/big` thresholds at `gA`,
the write-barrier flag and the `hasADX` byte. `pre` holds for every `nat.div` cost function bounded by `CD` on the two
shapes window-4 calls it with (`len u = 3` and `len u = 1`, `len v = 1`).
-/

namespace FvModexp.Amd64.ExpW4.Witness

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy FvModexp
open FvModexp.Amd64.AsmWit

set_option maxRecDepth 100000

abbrev ST : Nat := OA + 0x100
abbrev MP : Nat := OB
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
/-- the entry `RSP` -/
abbrev RS : Nat := SP0 + 8
/-- the stack region below `SP0` -/
abbrev WW : Nat := 0x10000
/-- the budget the witness runtime grants, and the bound on `nat.div`'s cost it covers -/
abbrev BW : Nat := 0x100000
abbrev CD : Nat := 0x10000
abbrev KW : Nat := 41512
abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88

theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : StackNat.wbA = wbAw := by decide
theorem adx_eq : MontHyp.hasADX = adxW + 2 := by decide

/-- the objects, the stack header, the return address and the stack arguments, the thresholds; all other bytes 0 -/
def g (a : Nat) : Byte :=
  if a = MP then 7 else if a = XP then 3 else if a = YP then 5
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = RS + 1 then 0x10
  else if a = RS + 9 then 0x02 else if a = RS + 10 then 0xE0 else if a = RS + 16 then 1
  else if a = RS + 34 then 0xE0 else if a = RS + 40 then 1 else if a = RS + 48 then 1
  else if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1]

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 XP else if i = 8 then 1
      else if i = 9 then 1 else if i = 4 then BitVec.ofNat 64 RS else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program W4Loop.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program W4Loop.fn)
    [BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP,
      BitVec.ofNat 64 1, BitVec.ofNat 64 1] s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv BW [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem globals : RunIface.Globals R mem0 [((SP0 - 0x380) - 8 - KW, (SP0 - 0x380) + 0x3f8)] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (rw [acc0]; decide +kernel)

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies `PreD` (`z.expNNOddMontgomeryWindowSize4(stk, 3, 5, 7)`, `z = nil`) for every `nat.div`
cost function bounded by `CD` on window-4's two division shapes -/
theorem pre (costF : Nat → Nat → Nat → Nat) (hcF : ∀ l, l ≤ 2 ^ 16 → costF l 3 1 ≤ CD ∧ costF l 1 1 ≤ CD) :
    PreD R BW [] KW costF CD 0 0 ST XP 1 1 YP 1 MP 1 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat - 0x388 = SP0 - 0x380 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  unfold PreD EPreA
  rw [h4, h14, hfs, hm]
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, by decide, by decide, ?_, WStubs.serves []⟩, globals, ?_⟩,
    ?_⟩
  repeat' apply And.intro
  all_goals first
    | decide
    | exact inv1 _
    | exact dataLoaded _ _
    | exact roOut
    | (intro r hr; simp at hr)
    | (right; rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Held]; right; rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro h; exact absurd h (by decide))
    | exact (hcF _ (by decide)).1
    | exact (hcF _ (by decide)).2
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [acc0]; decide +kernel)
    | (intro _; rw [acc0]; decide +kernel)
    | (simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [Apart]; decide +kernel)
    | (simp only [NatNorm]; decide +kernel)
    | (simp only [NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, acc0]; decide +kernel)
    | (simp only [W4En.free, Apart]; decide +kernel)
    | (simp only [natVal]; decide +kernel)
    | decide +kernel
    | trivial

end FvModexp.Amd64.ExpW4.Witness
