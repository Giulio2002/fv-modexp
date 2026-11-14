import FvModexp.Proofs.Amd64.Exp.EvenRowP
import FvModexp.Proofs.Amd64.Exp.SlowCl
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Exp.P2DRow
import FvModexp.Proofs.Amd64.NatQ.DivRowWitQ

set_option autoImplicit false

/-!
# Row: `nat.expNNEven` (amd64) on the Run extraction (agent asm s74; twin of infra's Arm64/Exp/EvenRow)

`correctnessP` = `EvenRow.sumP` (the `ExpEven.EvenSum` summary on `LibNE`, frame `stkE 41640 = 43152`, `above = 0x70`)
moved to `Extracted.program.link impl` (`Summary.of_codeIn64` + `Summary.returns`). Runtime premises: the live
`growslice`, `memclrNoHeapPointers`, `memmove` (+ zero-length), `makeslice`, `newobject`, `gcWriteBarrier2` contracts.
`correctnessP` takes amd64 `nat.expNNSlow`'s Q-form `hSQ` as a premise; `correctness` (the row) discharges it with
expmc's closed `Q.ExpSlow.hypCl` (on `LibW.names`, frame 41952 ≤ 41640 + 0x388), so only runtime contracts remain. `y` and `m` are the stack arguments (`RSP + 8 …`, `RSP + 32 …`).
`Witness`: the call `z.expNNEven(stk, 3, 5, 6)` (`3^5 mod 6`) with `z = nil`, the stack `{w, 0, 4}`;
`nonvacuous` instantiates every premise of `correctness` and runs it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.EvenRow

/-- the stack argument `y` (`RSP + 8 / 16 / 24`), with NUMERAL offsets: the v0.3.3 audit counts a read at `RSP + k` with a
non-numeral `k` (as in `NHyp.StkArg`'s body) as a read of the return-address word `[RSP]` -/
@[reducible] def ArgY (s : State) (y yl yc : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = y ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc

/-- the stack argument `m` (`RSP + 32 / 40 / 48`), numeral offsets (see `ArgY`) -/
@[reducible] def ArgM (s : State) (m ml mc : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 32) 8 = m ∧ s.mem.readLE ((s.regs 4).toNat + 40) 8 = ml ∧
    s.mem.readLE ((s.regs 4).toNat + 48) 8 = mc

theorem argY {s : State} {y yl yc : Nat} (h : ArgY s y yl yc) : NHyp.StkArg s 0 y yl yc := by
  unfold NHyp.StkArg; simp only [Nat.add_zero]; exact h

theorem argM {s : State} {m ml mc : Nat} (h : ArgM s m ml mc) : NHyp.StkArg s 24 m ml mc := by
  unfold NHyp.StkArg
  rw [show (s.regs 4).toNat + 24 + 8 = (s.regs 4).toNat + 32 by omega,
    show (s.regs 4).toNat + 24 + 16 = (s.regs 4).toNat + 40 by omega,
    show (s.regs 4).toNat + 24 + 24 = (s.regs 4).toNat + 48 by omega]
  exact h

/-- the precondition: the stack arguments `y`, `m` and `EvenSum`'s entry facts (window `43152` / `0x70`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : Nat)
    (s : State) : Prop :=
  ArgY s y yl yc ∧ ArgM s m ml mc ∧
    ExpEven.Pre R b L 43152 0x70 nE cE z zl zc st x xl y yl m ml mc s ∧ NHyp.XFacts R L x xl xc ∧
    ExpN.XG s.mem st x xl xc ∧ Outside x (8 * xc) (win s 43152 0x70)

/-- the postcondition: `CPostR` with the value `x^y mod m` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z zc st x xl y yl m ml : Nat) (s s' : State) :
    Prop :=
  ExpEven.Post R b L 43152 0x70 cE z zc st x xl y yl m ml s s'

theorem fnE_eq : segAddr Extracted.program ExpEven.fn = ExpEven.fnE := by decide

theorem bvN (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNNEven`** (amd64, premise form on `nat.expNNSlow`): `z.expNNEven(stk, x, y, m)` returns `x^y mod m`
for every `x > 0`, `y ≥ 2`, even `m > 0` of at most 128 words (`Pre` / `Post`), for every runtime meeting the live
allocation / copy / clear / write-barrier contracts, given `hSQ`. -/
theorem correctnessP (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    {nsS : List String} {stkS : Nat}
    (hSQ : NHyp.SlowHypQ impl R nsS stkS 112 ExpSlow.need Q.ExpSlow.needH
      (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)))
    (hnsS : ∀ x, nsS.contains x = true → LibN.names.contains x = true) (hnfS : nsS.contains ExpN.fn = false)
    (hKS : stkS ≤ 41640 + 0x388)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ExpEven.fn) [z, zl, zc, st, x, xl, xc]
      (Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m ml mc)
      (Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m ml) := by
  have hS0 := sumP impl hap R hgr hmc hmv hmz hmk hno hwb hSQ hnsS hnfS hKS
  have e : ExpEven.stkE 41640 = 43152 := by decide
  rw [e] at hS0
  have hc : Janus.Contracts.EqHashModel.CodeIn64 (LibNE.program.link impl) (Extracted.program.link impl) := by
    rw [LibNE.eq_only]; exact codeIn_restrict_of_apart64 hap LibNE.names
  have hS := Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc
    (hS0 b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m ml mc)
  rw [fnE_eq]
  intro ret hret s hs hpre
  have hr : s.mem.readLE (s.regs 4).toNat 8 = ret := hs.ret
  exact Summary.returns hS hret hs.rip (by rw [retAddrOf_eq, hs.ret]; rfl)
    ⟨hs.zero, hs.df, (hs.args 0 (by simp)).trans (bvN _).symm, (hs.args 1 (by simp)).trans (bvN _).symm,
      (hs.args 2 (by simp)).trans (bvN _).symm, (hs.args 3 (by simp)).trans (bvN _).symm,
      (hs.args 4 (by simp)).trans (bvN _).symm, (hs.args 5 (by simp)).trans (bvN _).symm,
      (hs.args 6 (by simp)).trans (bvN _).symm, argY hpre.1, argM hpre.2.1, hpre.2.2.1, z.isLt, xc.isLt,
      (argY hpre.1).2.2 ▸ readLE_lt_8 _ _,
      by rw [hr]; exact hret.user, hpre.2.2.2.1, hpre.2.2.2.2.1, hpre.2.2.2.2.2⟩
    fun s' ⟨⟨h1, h2, h3, h4⟩, hp⟩ => ⟨⟨h1, h2, h3, h4⟩, hp⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNNEven`** (amd64, closed): `z.expNNEven(stk, x, y, m)` returns `x^y mod m`
for every `x > 0`, `y ≥ 2`, even `m > 0` of at most 128 words (`Pre` / `Post`), for every runtime meeting the live
allocation / copy / clear / write-barrier contracts (`nat.expNNSlow` closed by expmc's `Q.ExpSlow.hypCl`). -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ExpEven.fn) [z, zl, zc, st, x, xl, xc]
      (Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m ml mc)
      (Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m ml) :=
  correctnessP impl hap R hgr hmc hmv hmz hmk hno hwb (Q.ExpSlow.hypCl hap hgr hmc hmv hmz hmk hwb) libW_libN libW_nfN
    (by decide) b L z zl zc st x xl xc y yl yc m ml mc

end FvModexp.Amd64.EvenRow

namespace FvModexp.Amd64.EvenRow.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp
open FvModexp.Amd64.P2DRow.Witness (NA OP WW BW gAw wbAw adxW nA_eq gA_eq wbA_eq hret hty)

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
abbrev MP : Nat := OB + 0x300
abbrev KW : Nat := 43152

/-- `x = [3]`, `y = [5]` (at `SP0 + 8 …`), `m = [6]` (at `SP0 + 32 …`), the stack header, `natOne = {OP, 1, 1}` with
`OP[0] = 1`, the four `math/big` thresholds; all other bytes 0 (the return address `RET` at `SP0` from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = MP then 6 else if a = OP then 1
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = SP0 + 9 then 0x02 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 1 else if a = SP0 + 24 then 1
  else if a = SP0 + 33 then 0x03 else if a = SP0 + 34 then 0xE0 else if a = SP0 + 40 then 1
  else if a = SP0 + 48 then 1
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xE0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩, ⟨NA, 24, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP,
    BitVec.ofNat 64 1, BitVec.ofNat 64 1]

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 XP else if i = 8 then 1
      else if i = 9 then 1 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program ExpEven.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program ExpEven.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
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

theorem stLen0 : stLen mem0 ST = 0 := by decide +kernel

theorem bud : cE 0 1 1 1 ≤ BW := budW

theorem one0 : NatOne R [] s0.mem OP (win s0 KW 0x70 ++ [(0, 0 + 8 * 0)] ++ stWs s0.mem ST) := by
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

theorem rd0 (p n : Nat) (hp : (p, n) ∈ [(XP, 1), (YP, 1), (MP, 1)]) :
    RdIn R [] s0 KW 0x70 p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s0.mem p n ∧ Apart p (8 * n) ST 24 ∧
      Apart p (8 * n) (NHyp.freeOf s0.mem ST).1 (NHyp.freeOf s0.mem ST).2 ∧ (0 < 0 → Apart 0 (8 * 0) p (8 * n)) := by
  have hm : s0.mem = mem0 := rfl
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨⟨by decide, by rw [hm, acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩, by decide, ?_, ?_, ?_,
      fun h => absurd h (by decide)⟩
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
    · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
    · simp only [NatNorm, hm]; decide +kernel
    · simp only [Apart]; decide
    · simp only [Apart, hm]; decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`3^5 mod 6`, `z = nil`) -/
theorem pre : Pre R BW [] 0 0 0 ST XP 1 1 YP 1 1 MP 1 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  refine ⟨⟨by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel⟩,
    ⟨by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel⟩,
    ⟨?_, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel,
      by decide, by decide, by decide, by decide, by decide, ?_, ⟨OP, one0, ?_⟩⟩, ?_, ?_, ?_⟩
  · have hcb : cE (stLen s0.mem ST) 1 1 1 ≤ BW := by rw [hm, stLen0]; exact bud
    generalize cE (stLen s0.mem ST) 1 1 1 = cb at hcb ⊢
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
  · simp only [win, h4, outside_cons, outside_nil, and_true]; decide +kernel
  · intro _
    refine ⟨by simp only [Apart]; decide, fun _ => ?_⟩
    simp only [Apart, hm]; decide +kernel
  · refine ⟨⟨by decide, by decide, fun _ => ⟨?_, by decide⟩⟩, fun _ => by simp only [gA_eq, Apart]; decide⟩
    simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [ExpN.XG, W4En.free, hm, nA_eq, gA_eq, Apart]
    refine ⟨fun _ => by decide, by decide +kernel, by rw [acc0]; decide +kernel, by rw [acc0]; decide +kernel,
      by decide, by decide +kernel⟩
  · simp only [win, h4, outside_cons, outside_nil, and_true]; decide +kernel

/-- `pre` at the `BitVec` arguments of `correctnessP` -/
theorem preB : Pre R BW [] (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat
    (BitVec.ofNat 64 ST).toNat (BitVec.ofNat 64 XP).toNat (1 : BitVec 64).toNat (1 : BitVec 64).toNat YP 1 1 MP 1 1
    s0 := by
  have e0 : (0 : BitVec 64).toNat = 0 := by decide
  have e1 : (BitVec.ofNat 64 ST).toNat = ST := by decide
  have e2 : (BitVec.ofNat 64 XP).toNat = XP := by decide
  have e3 : (1 : BitVec 64).toNat = 1 := by decide
  rw [e0, e1, e2, e3]; exact pre

/-- Every contract hypothesis of the (closed) `correctness` and every conjunct of its precondition hold together: the shared witness runtime, budget `BW`, empty live set, the call `z.expNNEven(stk, 3, 5, 6)` with
`z = nil` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous :
    ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program ExpEven.fn)
      [z, zl, zc, st, x, xl, xc] s ∧
    Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m ml mc s ∧
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
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      DivRowQ.Witness.mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
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
      ABIReturn s s' ∧ Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m ml s s' :=
  ⟨WStubs.impl, R, BW, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, YP, 1, 1, MP, 1, 1, RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, hret, setup, preB,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl,
      by rw [WStubs.addr_mv]; exact DivRowQ.Witness.site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _) (by rw [WStubs.addr_no]; exact WStubs.no [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) BW []
      0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 YP 1 1 MP 1 1 RET hret s0 setup preB⟩

end FvModexp.Amd64.EvenRow.Witness
