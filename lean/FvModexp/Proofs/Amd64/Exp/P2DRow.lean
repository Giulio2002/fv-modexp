import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.Exp.CalleeInstR
import FvModexp.Proofs.Amd64.Exp.P2DE
import FvModexp.Proofs.Amd64.Exp.P2DW2
import FvModexp.Proofs.Amd64.Exp.P2W4W
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row: `nat.expNNPowerOfTwo` (amd64) on the Run extraction (agent asm s71; twin of infra's Arm64/Exp/P2DRow)

`correctness` = `P2D.ens` (the `NHyp.P2Hyp` shape: any `x > 0`, the odd part through the two windows, the even part
by `rsh` / recursive call / `lsh`) with the PROVED closed Q-form callees of `CalleeInstQ` / `CalleeInstR`
(`(*stack).nat`, `nat.sqr`, `nat.mul`, `nat.trunc`, `nat.rsh`, `nat.lsh` on `nsQ`, callee window `kc = mulWX64`)
and the two PROVED window summaries (`P2D.wsum2` = divmc's `P2W2.fullC`, `P2W4.wsum`), moved to
`Extracted.program.link impl` (`Ensures.full64`); window `[RSP - stk, RSP + 112)` for `42520 ≤ stk ≤ 2^20 + 0x78`,
budget `P2D.costP P2W2.costB P2W4.costB`. Runtime premises: the live `growslice`, `memclrNoHeapPointers`,
`memmove`, `makeslice`, `newobject`, `gcWriteBarrier2` contracts. `y` is the stack argument, `logM` is `R10`.
`Witness.nonvacuous`: `z = nil`, the stack `{w, 0, 4}`, `x = [3]`, `y = [5]`, `logM = 8` (`3^5 mod 2^8`), `natOne`,
a 64 KiB stack region, window `stk = 42520`, the shared witness runtime, one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2DRow

open Janus.Contracts.EqHashModel (CodeIn64)
open FvModexp.Amd64.CalleeInstQ FvModexp.Amd64.ExpHyp

/-- the precondition (= `NHyp.P2Hyp`'s; stack need `2^13`, budget `P2D.costP P2W2.costB P2W4.costB`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (z zl zc st x xl xc y yl yc lm : Nat)
    (s : State) : Prop :=
  NHyp.StkArg s 0 y yl yc ∧
    (NHyp.CPre R b L stk 112 z zl zc st [(x, xl), (y, yl)] (P2D.needP xl yl lm)
        (P2D.costP P2W2.costB P2W4.costB (stLen s.mem st) xl yl lm) s ∧
      0 < natVal s.mem x xl ∧ 0 < natVal s.mem y yl ∧ 1 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
      ∃ op, EvenHyp.NatOne R L s.mem op (win s stk 112 ++ [(z, z + 8 * zc)] ++ stWs s.mem st) ∧
        NHyp.StkApart s.mem st op 8) ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧ NHyp.XGc s.mem st x xl xc

/-- the postcondition: `CPostR` with the value `x^y mod 2^logM` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (z zc st x xl y yl lm : Nat)
    (s s' : State) : Prop :=
  NHyp.CPostR R b L stk 112 z zc st (natVal s.mem x xl ^ natVal s.mem y yl % 2 ^ lm)
    (P2D.costP P2W2.costB P2W4.costB (stLen s.mem st) xl yl lm) s s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the CLOSED callee shape `NHyp.P2Hyp` on `LibW.names` (for `ExpN.DHyps.p2`): only the live runtime contracts of the
whole extraction remain as premises -/
theorem hyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (stk : Nat) (hk0 : 42520 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x78) :
    NHyp.P2Hyp impl R LibW.names stk 112 P2D.needP (P2D.costP P2W2.costB P2W4.costB) := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hgrL : GrowsliceLiveContract64 (LibW.program.link impl) P2W2.grE 4096 R := by
    rw [show P2W2.grE = cA "runtime.growslice" by decide]; exact StackNatX.GrowsliceLiveContract64.of_codeIn' hc hgr
  have hmcL : MemclrNoHeapPointersLive64 (LibW.program.link impl) P2W2.mcE 4096 R := by
    rw [show P2W2.mcE = cA "runtime.memclrNoHeapPointers" by decide]; exact MemclrNoHeapPointersLive64.of_codeIn hc hmc
  have hmvL : MemmoveLive64 (LibW.program.link impl) P2W2.mvE 4096 R := by
    rw [show P2W2.mvE = cA "runtime.memmove" by decide]; exact MemmoveLive64.of_codeIn hc hmv
  have hmkL : MakesliceLiveContract64 (LibW.program.link impl) P2W2.mkE 4096 R := by
    rw [show P2W2.mkE = cA "runtime.makeslice" by decide]; exact MakesliceLiveContract64.of_codeIn hc hmk
  have hnoL : NewobjectLiveContract64 (LibW.program.link impl) P2W2.noE 4096 R := by
    rw [show P2W2.noE = cA "runtime.newobject" by decide]; exact NewobjectLiveContract64.of_codeIn hc hno
  have hwbL : WbLiveContract64 (LibW.program.link impl) P2W2.wbE 4096 R 2 := by
    rw [show P2W2.wbE = cA "runtime.gcWriteBarrier2" by decide]; exact WbLiveContract64.of_codeIn hc hwb
  have hW2 := P2D.wsum2 hap sub nf2 nfP hgrL hmcL hmvL hmkL hnoL hwbL (kc := mulWX64) (by decide)
    (sn hap hgr hmc hwb) (by decide) (by decide) (sq hap hgr hmc hmv hmk hwb _) (by decide) (Nat.le_refl _)
    (mu hap hgr hmc hmv hmk hwb _) (Nat.le_refl _) (Nat.le_refl _) (tr hap hmv hmk) (by decide) (by decide)
  have hW4 := P2W4.wsum hap sub nf4 nfP (by rw [show P2W4.grE = P2W2.grE by decide]; exact hgrL)
    (by rw [show P2W4.mcE = P2W2.mcE by decide]; exact hmcL) (by rw [show P2W4.mvE = P2W2.mvE by decide]; exact hmvL)
    (by rw [show P2W4.mkE = P2W2.mkE by decide]; exact hmkL) (by rw [show P2W4.noE = P2W2.noE by decide]; exact hnoL)
    (by rw [show P2W4.wbE = P2W2.wbE by decide]; exact hwbL) (kc := mulWX64) (by decide)
    (sn hap hgr hmc hwb) (by decide) (by decide) (sq hap hgr hmc hmv hmk hwb _) (by decide) (Nat.le_refl _)
    (mu hap hgr hmc hmv hmk hwb _) (Nat.le_refl _) (Nat.le_refl _) (tr hap hmv hmk) (by decide) (by decide)
  have e2 : max (41512 + 0x1d8) (P2Pre.K mulWX64 + 0x1d8) = 41984 := by decide
  have e4 : max (41512 + 0x300) (P2Pre.K mulWX64 + 0x300) = 42280 := by decide
  rw [e2] at hW2
  rw [e4] at hW4
  exact P2D.ens hap hmk hW2 hW4 sub nfD (rh hap hmv hmk) (by decide) (lh hap hmc hmv hmk) (by decide) stk (by omega)
    (by omega) (by omega) hk2 (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNPowerOfTwo`** (amd64): `z.expNNPowerOfTwo(stk, x, y, logM)` returns `x^y mod 2^logM` for every
`x > 0`, `y > 0`, `1 ≤ logM ≤ 2^13` (`Pre` / `Post`), for every runtime meeting the live allocation / copy / clear /
write-barrier contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 42520 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x78)
    (z zl zc st x xl xc lm : BitVec 64) (y yl yc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program NHyp.fnP2) [z, zl, zc, st, x, xl, xc, lm]
      (Pre R b L stk z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc lm.toNat)
      (Post R b L stk z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl lm.toNat) := by
  exact Ensures.full64 hap (by simp [numIntRegs])
    (hyp impl hap R hgr hmc hmv hmk hno hwb stk hk0 hk2 b L z zl zc st x xl xc lm y yl yc)

end FvModexp.Amd64.P2DRow

namespace FvModexp.Amd64.P2DRow.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
/-- `natOne`'s header (outside the extracted data) and its backing word -/
abbrev NA : Nat := 12050400
abbrev OP : Nat := OB + 0x800
/-- the stack region below `SP0` (the entry `RSP`) -/
abbrev WW : Nat := 0x10000
abbrev BW : Nat := 0x100000
abbrev KW : Nat := 42520
abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88

theorem nA_eq : natOneA = NA := by decide
theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : StackNat.wbA = wbAw := by decide

/-- `x = [3]`, `y = [5]` (passed at `SP0 + 8 …`), the stack header, `natOne = {OP, 1, 1}` with `OP[0] = 1`, the four
`math/big` thresholds; all other bytes 0 (the return address `RET` at `SP0` comes from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = OP then 1
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = SP0 + 9 then 0x02 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 1 else if a = SP0 + 24 then 1
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xE0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩, ⟨NA, 24, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP,
    BitVec.ofNat 64 1, BitVec.ofNat 64 1, BitVec.ofNat 64 8]

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 XP else if i = 8 then 1
      else if i = 9 then 1 else if i = 10 then 8 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program NHyp.fnP2),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program NHyp.fnP2)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

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

theorem stLen0 : stLen mem0 ST = 0 := by decide +kernel

theorem bud : P2D.costP P2W2.costB P2W4.costB 0 1 1 8 ≤ BW := by decide +kernel

theorem one0 : NatOne R [] s0.mem OP (win s0 KW 112 ++ [(0, 0 + 8 * 0)] ++ stWs s0.mem ST) := by
  have hm : s0.mem = mem0 := rfl
  dsimp only [NatOne]
  rw [nA_eq, hm]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel

theorem sg0 : StackGuardOK s0 KW :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem tls0 : TlsG s0 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem rd0 (p n : Nat) (hp : (p, n) ∈ [(XP, 1), (YP, 1)]) :
    RdIn R [] s0 KW 112 p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s0.mem p n ∧ Apart p (8 * n) ST 24 ∧
      Apart p (8 * n) (NHyp.freeOf s0.mem ST).1 (NHyp.freeOf s0.mem ST).2 ∧ (0 < 0 → Apart 0 (8 * 0) p (8 * n)) := by
  have hm : s0.mem = mem0 := rfl
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨⟨by decide, by rw [hm, acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩, by decide, ?_, ?_, ?_,
      fun h => absurd h (by decide)⟩
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
    · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
    · simp only [NatNorm, hm]; decide +kernel
    · simp only [Apart]; decide
    · simp only [Apart, hm]; decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`3^5 mod 2^8`, `z = nil`) at window `stk = 42520` -/
theorem pre : Pre R BW [] KW 0 0 0 ST XP 1 1 YP 1 1 8 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  refine ⟨⟨by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel⟩,
    ⟨?_, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel, by decide, by decide, by decide, ⟨OP, one0, ?_⟩⟩,
    by decide, by decide, ?_⟩
  · have hcb : P2D.costP P2W2.costB P2W4.costB (stLen s0.mem ST) 1 1 8 ≤ BW := by rw [hm, stLen0]; exact bud
    generalize P2D.costP P2W2.costB P2W4.costB (stLen s0.mem ST) 1 1 8 = cb at hcb ⊢
    unfold NHyp.CPre CallEnv TlsOK
    repeat' (first
      | exact hcb
      | exact inv1 _
      | exact WStubs.serves []
      | exact roOut
      | exact sg0
      | exact tls0
      | exact rd0
      | exact dataLoaded _ _
      | apply And.intro)
    all_goals try simp only [win, h4, h14, hfs, hm, stLen0]
    all_goals first
      | decide
      | (intro r hr; simp at hr; done)
      | (intro h; exact absurd h (by decide))
      | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [Apart, gA_eq, wbA_eq, nA_eq]; decide +kernel)
      | (rw [acc0]; decide +kernel)
      | (simp only [StkOK, NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, acc0]; decide +kernel)
      | decide +kernel
      | trivial
      | (simp only [List.map_nil, List.nil_append, List.append_nil, outside_nil]; done)
      | (show Outside _ _ (List.append [] []); trivial)
      | (intro _; simp only [outside_cons, outside_nil, and_true, Apart]; decide +kernel)
      | skip
  · intro _
    refine ⟨by simp only [Apart]; decide, fun _ => ?_⟩
    simp only [Apart, hm]; decide +kernel
  · simp only [NHyp.XGc, NHyp.freeOf, hm, nA_eq, gA_eq, Apart]
    refine ⟨fun _ => by decide, by decide +kernel, by rw [acc0]; decide +kernel, by rw [acc0]; decide +kernel,
      by decide, by decide +kernel⟩

/-- `pre` at the `BitVec` arguments of `correctness` -/
theorem preB : Pre R BW [] KW (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat
    (BitVec.ofNat 64 ST).toNat (BitVec.ofNat 64 XP).toNat (1 : BitVec 64).toNat (1 : BitVec 64).toNat YP 1 1
    (8 : BitVec 64).toNat s0 := by
  have e0 : (0 : BitVec 64).toNat = 0 := by decide
  have e1 : (BitVec.ofNat 64 ST).toNat = ST := by decide
  have e2 : (BitVec.ofNat 64 XP).toNat = XP := by decide
  have e3 : (1 : BitVec 64).toNat = 1 := by decide
  have e4 : (8 : BitVec 64).toNat = 8 := by decide
  rw [e0, e1, e2, e3, e4]; exact pre

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, window `stk = 42520`, the call `z.expNNPowerOfTwo(stk, 3, 5, 8)` with `z = nil` and the
stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat)
    (z zl zc st x xl xc lm : BitVec 64) (y yl yc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    42520 ≤ stk ∧ stk ≤ 2 ^ 20 + 0x78 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program NHyp.fnP2)
      [z, zl, zc, st, x, xl, xc, lm] s ∧
    Pre R b L stk z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc lm.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Post R b L stk z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl lm.toNat s s' :=
  ⟨WStubs.impl, R, BW, [], KW, 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, 8, YP, 1, 1, RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, Nat.le_refl _, by decide, hret,
    setup, preB,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _) (by rw [WStubs.addr_no]; exact WStubs.no [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) BW [] KW (Nat.le_refl _) (by decide)
      0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 8 YP 1 1 RET hret s0 setup preB⟩

end FvModexp.Amd64.P2DRow.Witness
