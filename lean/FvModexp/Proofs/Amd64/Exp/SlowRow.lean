import FvModexp.Proofs.Amd64.Exp.SlowCl
import FvModexp.Proofs.Amd64.Exp.StkArgR
import FvModexp.Proofs.Amd64.Exp.P2DRow
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.NatQ.DivRowWitQ

set_option autoImplicit false

/-!
# Row: `nat.expNNSlow` (amd64) on the Run extraction (agent asm s80)

`correctness` = expmc's closed `Q.ExpSlow.hypCl` (`NHyp.SlowHypQ` on `LibW.names`, frame `41952` below / `112` above
`RSP`) moved to `Extracted.program.link impl` (`Ensures.full64`). The stack arguments `y` (`RSP + 8 / 16 / 24`) and `m`
(`RSP + 32 / 40 / 48`) are stated with NUMERAL offsets (`NHyp.StkArg0` / `StkArg24`, the v0.3.3 audit's `[RSP]`-word
rule); otherwise the precondition is `SlowHypQ`'s verbatim. Runtime premises: the live `growslice`,
`memclrNoHeapPointers`, `memmove` (+ zero-length), `makeslice`, `gcWriteBarrier2` contracts.
A LOWER row of `amd64 Exp/EvenRow` (its `nat.expNNSlow` closure is compiled and replayed here).
`Witness`: the call `z.expNNSlow(stk, 3, 5, 7)` (`3^5 mod 7`) with `z = nil`, the stack `{w, 0, 4}`, reserve
level `H = 112`; `nonvacuous` instantiates every premise of `correctness` and runs it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.SlowRow

open FvModexp.Amd64.ExpHyp

/-- the precondition: `NHyp.SlowHypQ`'s, with the stack arguments at numeral offsets -/
@[reducible] def Pre (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : Nat)
    (s : State) : Prop :=
  (NHyp.StkArg0 s y yl yc ∧ NHyp.StkArg24 s m ml mc) ∧
    (NHyp.CPre R b L 41952 112 z zl zc st [(x, xl), (y, yl), (m, ml)] (ExpSlow.need xl yl ml)
      (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ) xl yl ml + stkR H s.mem st) s ∧
    0 < natVal s.mem x xl ∧ 2 ≤ natVal s.mem y yl ∧ 0 < natVal s.mem m ml ∧ 0 < st) ∧
    NHyp.XFacts R L x xl xc ∧ stLen s.mem st + Q.ExpSlow.needH xl ml ≤ H

/-- the postcondition: `CPostR0Q` with the value `x^y mod m` -/
@[reducible] def Post (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (z zc st x xl y yl m ml : Nat) (s s' : State) :
    Prop :=
  NHyp.CPostR0Q R b L 41952 112 z zc st (natVal s.mem x xl ^ natVal s.mem y yl % natVal s.mem m ml)
    (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ) xl yl ml + stkR H s.mem st) (stkR H s'.mem st) s s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNNSlow`** (amd64, closed): `z.expNNSlow(stk, x, y, m)` returns `x^y mod m` normalised for every `x > 0`,
`y ≥ 2`, `m > 0` of at most `2^9` words (`Pre` / `Post`: TIGHT-COSTS Q-form, cost `costQ … xl yl ml + stkR H`, refund
`stkR H` after the call), for every runtime meeting the live allocation / copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program NHyp.fnSlow) [z, zl, zc, st, x, xl, xc]
      (Pre R H b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m ml mc)
      (Post R H b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m ml) :=
  (Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Amd64.SlowRow.Pre, FvModexp.Amd64.NHyp.StkArg0, FvModexp.Amd64.NHyp.StkArg24, FvModexp.Amd64.NHyp.CPre, FvModexp.stkR, FvModexp.natVal, FvModexp.stLen, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.TlsOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]) hap (by simp [numIntRegs])
    (Q.ExpSlow.hypCl hap hgr hmc hmv hmz hmk hwb H b L z zl zc st x xl xc y yl yc m ml mc)).mono_ret
    (fun _ h => ⟨⟨h.1.1.toStkArg, h.1.2.toStkArg⟩, h.2⟩) (fun _ _ _ _ h => h)

end FvModexp.Amd64.SlowRow

namespace FvModexp.Amd64.SlowRow.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp
open FvModexp.Amd64.P2DRow.Witness (NA OP WW BW gAw wbAw adxW nA_eq gA_eq wbA_eq hret hty)

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
abbrev MP : Nat := OB + 0x300
abbrev KW : Nat := 41952
abbrev HW : Nat := 112

/-- `x = [3]`, `y = [5]` (at `SP0 + 8 …`), `m = [7]` (at `SP0 + 32 …`), the stack header, `natOne = {OP, 1, 1}`, the
four `math/big` thresholds; all other bytes 0 (the return address `RET` at `SP0` from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = MP then 7 else if a = OP then 1
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
    rip := BitVec.ofNat 64 (segAddr Extracted.program NHyp.fnSlow),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem setup : CallSetup0 (segAddr Extracted.program NHyp.fnSlow)
    args s0 :=
  ⟨rfl, rfl, by decide, by
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

theorem bud : Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ) 1 1 1 + stkR HW mem0 ST ≤ BW := by
  decide +kernel

theorem sg0 : StackGuardOK s0 KW :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel, by decide +kernel⟩

theorem tls0 : TlsG s0 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem rd0 (p n : Nat) (hp : (p, n) ∈ [(XP, 1), (YP, 1), (MP, 1)]) :
    RdIn R [] s0 KW HW p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s0.mem p n ∧ Apart p (8 * n) ST 24 ∧
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
/-- the witness state satisfies the precondition (`3^5 mod 7`, `z = nil`, `H = 112`) -/
theorem pre : Pre R HW BW [] 0 0 0 ST XP 1 1 YP 1 1 MP 1 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  have hy : NHyp.StkArg0 s0 YP 1 1 := by unfold NHyp.StkArg0; rw [h4, hm]; decide +kernel
  have hmA : NHyp.StkArg24 s0 MP 1 1 := by unfold NHyp.StkArg24; rw [h4, hm]; decide +kernel
  refine ⟨⟨hy, hmA⟩,
    ⟨?_, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel, by decide⟩, ?_,
    by rw [hm, stLen0]; decide⟩
  · have hcb : Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ) 1 1 1 + stkR HW s0.mem ST ≤ BW := by
      rw [hm]; exact bud
    generalize Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ) 1 1 1 + stkR HW s0.mem ST = cb at hcb ⊢
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
  · refine ⟨⟨by decide, by decide, fun _ => ⟨?_, by decide⟩⟩, fun _ => by simp only [gA_eq, Apart]; decide⟩
    simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel

/-- `pre` at the `BitVec` arguments of `correctness` -/
theorem preB : Pre R HW BW [] (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat
    (BitVec.ofNat 64 ST).toNat (BitVec.ofNat 64 XP).toNat (1 : BitVec 64).toNat (1 : BitVec 64).toNat YP 1 1 MP 1 1
    s0 := by
  have e0 : (0 : BitVec 64).toNat = 0 := by decide
  have e1 : (BitVec.ofNat 64 ST).toNat = ST := by decide
  have e2 : (BitVec.ofNat 64 XP).toNat = XP := by decide
  have e3 : (1 : BitVec 64).toNat = 1 := by decide
  rw [e0, e1, e2, e3]; exact pre

/-- Every contract hypothesis of `correctness` and every conjunct of its precondition hold together: the shared
witness runtime, budget `BW`, reserve level `H = 112`, empty live set, the call `z.expNNSlow(stk, 3, 5, 7)` with
`z = nil` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous :
    ∃ (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
    (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program NHyp.fnSlow)
      [z, zl, zc, st, x, xl, xc] s ∧
    Pre R H b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m ml mc s ∧
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
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ Post R H b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m ml (s.setRet ret) s' :=
  ⟨WStubs.impl, R, HW, BW, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, YP, 1, 1, MP, 1, 1, RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, hret, setup, preB,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl,
      by rw [WStubs.addr_mv]; exact DivRowQ.Witness.site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) HW BW []
      0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 YP 1 1 MP 1 1 s0 setup preB RET hret⟩

end FvModexp.Amd64.SlowRow.Witness
