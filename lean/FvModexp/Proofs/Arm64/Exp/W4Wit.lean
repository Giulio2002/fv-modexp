import FvModexp.Proofs.Arm64.Exp.W4FunDefs
import FvModexp.Proofs.Arm64.Witness.AsmWit

set_option autoImplicit false

/-!
# window-4 (arm64): witness state for the row (non-vacuity of `ExpW4.Pre`)

`z = nil`, `stk` = header `{w: OA + 0x200, len: 0, cap: 4}` at `ST = OA + 0x100`, `x = [3]` at `XP`, `y = [5]` at `YP`,
`m = [7]` at `MP` (the call `3^5 mod 7`). The stack region is widened to `[SP0 - 0x10000, SP0 + 0x100)` so the window
`[sp - K, sp + 1040)` (`sp = SP0 - 928`) fits for every `4304 ≤ K ≤ KMAX` (`nat.div`'s stack depth `stkD ≤ K` is not
known yet). `pre` holds for every `nat.div` cost function `costF` with `divCost costF 1 1 0 ≤ CD`. The row (`correctness` + `nonvacuous`) is completed when asm's `nat.div`
summary lands (it replaces the `ExpHyp.DivHypL` premise of `ExpW4.ens`).
-/

namespace FvModexp.Arm64.ExpW4.Witness

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy FvModexp
open FvModexp.Arm64.AsmWit

set_option maxRecDepth 100000

abbrev ST : Nat := OA + 0x100
abbrev MP : Nat := OB
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
/-- the largest window depth below the frame the witness stack region allows -/
abbrev KMAX : Nat := 0x10000 - 0x400
/-- the budget the witness runtime grants, and the bound on `nat.div`'s cost it covers -/
abbrev BW : Nat := 0x100000
abbrev CD : Nat := 0x10000

/-- `RunIface.gA` (the four `math/big` threshold globals) -/
abbrev GA : Nat := 0x6d0e80

/-- `m = 7` at `MP`, `x = 3` at `XP`, `y = 5` at `YP`, the stack header at `ST`, the thresholds `40, 40, 12, 80` at
`GA`, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = MP then 7 else if a = XP then 3 else if a = YP then 5
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = GA then 40 else if a = GA + 8 then 40 else if a = GA + 16 then 12 else if a = GA + 24 then 80 else 0

/-- the standard regions with a 64 KiB stack, plus the four threshold globals (one region) and the
`runtime.writeBarrier` flag word -/
def regs : List Region :=
  ⟨SP0 - 0x10000, 0x10100, true⟩ :: stdRegs.tail ++ [⟨RunIface.gA, 32, false⟩, ⟨StackNat.wbA, 8, false⟩]

theorem gA_eq : RunIface.gA = 7147136 := by decide
theorem wbA_eq : RunIface.wbA = 7616064 := by decide

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1, BitVec.ofNat 64 MP, 1, 1]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

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

theorem sp0 : s0.sp.toNat - 928 = SP0 - 928 := by decide
theorem g0 : (s0.regs 28).toNat = G0 := by decide

/-- the witness bound on the window-4 budget (`W4Bud` is monotone in `costD`) -/
theorem stl : stLen s0.mem ST = 0 := by simp only [stLen, show s0.mem = mem0 from rfl]; decide +kernel

theorem key {a b a0 b0 k : Nat} (h1 : a ≤ a0 + k) (h2 : b ≤ b0 + k) : max a b ≤ max a0 b0 + k := by omega
theorem key0 {s m m0 k : Nat} (h : m ≤ m0 + k) : s + m ≤ s + m0 + k := by omega

/-- `W4Bud` grows by at most `12 · costD` (each path holds at most a dozen `costD` copies; the path MAXIMUM, s42) -/
theorem bud_c (n xl c l : Nat) : W4Bud n xl c l ≤ W4Bud n xl 0 l + 12 * c := by
  unfold W4Bud
  simp only [W4Pro.xnPre]
  refine key0 ?_
  repeat' apply key
  all_goals (simp only [W4Pro.xjBud, W4Pro.xnBudA, W4Pro.xnBudAC, W4Pro.xjBudA, W4Pro.xnBudAA, W4Pro.xnBudAB]; omega)

theorem bud (costD : Nat) (h : costD ≤ CD) : W4Bud 1 1 costD (stLen s0.mem ST) ≤ BW := by
  have hl : stLen s0.mem ST = 0 := by simp only [stLen, show s0.mem = mem0 from rfl]; decide +kernel
  have e : W4Bud 1 1 costD 0 ≤ W4Bud 1 1 0 0 + 12 * costD := bud_c 1 1 costD 0
  have h0 : W4Bud 1 1 0 0 = 9528 := by decide +kernel
  rw [h0] at e
  rw [hl]
  generalize W4Bud 1 1 costD 0 = A at e ⊢
  simp only [CD, BW] at h ⊢; omega

theorem accStk : mem0.accessible (SP0 - 0x10000) 0x10100 true = true := by rw [acc0]; decide +kernel

theorem accWin (K : Nat) (hK : 4304 ≤ K) (hK' : K ≤ KMAX) :
    s0.mem.accessible (SP0 - 928 - K) (K + 1040) true = true :=
  Memory.accessible_sub _ accStk (Or.inr rfl) (by simp only [SP0, KMAX] at *; omega)
    (by simp only [SP0, KMAX] at *; omega)

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies window-4's precondition (`3^5 mod 7`), for every window depth `4304 ≤ K ≤ KMAX` and
every `nat.div` cost function with `divCost costF 1 1 0 ≤ CD` -/
theorem pre (K : Nat) (costF : Nat → Nat → Nat → Nat) (hK : 4304 ≤ K) (hK' : K ≤ KMAX)
    (hc : divCost costF 1 1 0 ≤ CD) :
    Pre R BW [] K costF 0 0 ST XP 1 1 YP 1 MP 1 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  unfold Pre
  rw [stl]
  unfold PreD W4En.EPre W4En.EEnv
  rw [g0, sp0]
  refine ⟨?_, ?_, ?_, ?_, ?_, bud _ hc⟩
  rotate_left
  · decide
  · simp only [natVal, hm]; decide +kernel
  · simp only [natVal, hm]; decide +kernel
  · simp only [stLen, hm, StackNat.rnd]; decide +kernel
  repeat' apply And.intro
  all_goals first
    | decide
    | exact accWin K hK hK'
    | exact dataLoaded _ _
    | exact WStubs.serves []
    | exact roOut
    | exact inv1 _
    | (intro h; exact absurd h (by decide))
    | (simp only [SP0, KMAX] at hK hK' ⊢; omega)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [LiveSep, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        rt_eq, outside_cons, outside_nil, and_true, SP0, KMAX, HEAP, HEND, HSIZE, BUMP, WBUF] at hK hK' ⊢; omega)
    | (simp only [Apart, W4En.free, stW, stLen, stCap, hm]; decide +kernel)
    | (simp only [Apart, W4En.free, stW, stLen, stCap, hm, SP0, KMAX] at hK hK' ⊢; omega)
    | (rw [hm]; decide +kernel)
    | (intros; trivial)
    | (simp [Outside]; done)
    | (intro r hr; simp at hr)
    | (have h0 : s0.mem.readLE (G0 + 16) 8 = 0 := by rw [hm]; decide +kernel
       rw [h0]; simp only [SP0, KMAX] at hK hK' ⊢; omega)
    | (simp only [Apart, gA_eq, wbA_eq, SP0, KMAX, G0, ST, MP, XP, YP, OA, OB] at hK hK' ⊢; omega)
    | (intro _
       have e1 : stW s0.mem ST = OA + 0x200 := by rw [hm]; decide +kernel
       have e2 : stCap s0.mem ST = 4 := by rw [hm]; decide +kernel
       rw [e1, e2]; simp only [Apart, SP0, KMAX, G0, OA] at hK hK' ⊢; omega)
    | (rw [hm, acc0]; decide +kernel)
    | (simp only [hm, NatNorm]; decide +kernel)
    | (simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq, hm,
        acc0]; decide +kernel)
    | skip

end FvModexp.Arm64.ExpW4.Witness
