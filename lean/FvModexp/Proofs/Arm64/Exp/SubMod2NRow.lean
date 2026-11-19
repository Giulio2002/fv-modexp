import FvModexp.Proofs.Arm64.Exp.SubMod2NGR
import FvModexp.Proofs.Arm64.Nat.Trunc
import FvModexp.Proofs.Arm64.Nat.NatSub0
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites
import FvModexp.Proofs.Arm64.Witness.Stubs

set_option autoImplicit false

/-!
# Row: `nat.subMod2N` (arm64) on the Run extraction (agent infra)

`correctness` = `SubMod2N.ensG` (general form: any capacity of `z`, empty / `nil` operands) with the PROVED callees
`nat.trunc` (asm `Trunc.ens`), `nat.sub` (divmc `NatSub.ensR0`), `nat.add` (divmc `NatAdd.ensR`, inside `ensG`) and
asm's `nat.cmp`, moved to `Extracted.program.link impl` (`Ensures.full`). Runtime premises: the live `makeslice`,
`memmove` and `growslice` contracts.
`Witness.nonvacuous`: the shared witness runtime, the toy allocator invariant, `natOne` (header in `.data`, its word
in the `OB` object), the call `z.subMod2N(z, y, 64)` with `z = [5]` (cap 1) and `y = [3]`; one call-site state per
contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2NRow

open FvModexp.Arm64.SubMod2N

set_option maxHeartbeats 64000000 in
theorem trW_sub : ∀ x, Trunc.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)
set_option maxHeartbeats 64000000 in
theorem trW_fn : Trunc.names.contains SubMod2N.fn = false := by decide

/-- **`nat.subMod2N`** (arm64): `z.subMod2N(z, y, n)` returns a normalised nat holding `(Z − Y) mod 2^n`
(`Exp.subMod2N`), in `z`'s array or a fresh one, for every runtime meeting the live `makeslice` / `memmove` /
`growslice` contracts (`PreGR` / `PostG`; no constraint on `X30` beyond the ABI). -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program SubMod2N.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (PreGR R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.SubMod2N.PreGR, FvModexp.Arm64.CallEnv, FvModexp.Arm64.SubMod2N.K, FvModexp.Arm64.SubMod2N.A, FvModexp.Arm64.NatAdd.wordT, FvModexp.Arm64.EvenHyp.NatOne, FvModexp.Arm64.win, FvModexp.Arm64.EvenHyp.natOneA, FvModexp.NatLive, FvModexp.NatNorm, FvModexp.Arm64.SubMod2N.costG, Janus.Spec.GuardOK, Janus.Spec.StackOK]) hap (ensGR_of (SubMod2N.ensG impl hap R trW_sub trW_fn (by omega) (by omega)
    (Trunc.ens impl hap R hmk hmv)
    (fun b L zp zl zc xp xl xc yp yl yc => NatSub.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc)
    hmk hmv hgr) b L op zp zl zc yp yl yc n)

end FvModexp.Arm64.SubMod2NRow

namespace FvModexp.Arm64.SubMod2NRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy FvModexp.Arm64.SubMod2N FvModexp.Arm64.EvenHyp

set_option maxRecDepth 100000

/-- `natOne`'s header (`.data`, outside the extracted read-only data) -/
abbrev NA : Nat := 0x704010
/-- the witness's backing word of `natOne` -/
abbrev OP : Nat := OB + 0x800
abbrev YP : Nat := OB

theorem nA_eq : natOneA = NA := by decide

/-- `z = [5]` at `OA`, `y = [3]` at `OB`, `natOne = {OP, 1, 1}` with `OP[0] = 1`, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OA then 5 else if a = YP then 3 else if a = OP then 1
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xB0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else 0

def regs : List Region := stdRegs ++ [⟨NA, 24, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 YP, 1, 1, 64]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program SubMod2N.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program SubMod2N.fn)
    args s0 :=
  ⟨rfl, by first | decide | simp | omega, fun i h => by simp only [s0, dif_pos h]⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem one0 : NatOne R [] s0.mem OP (win s0 K A) := by
  have hm : s0.mem = mem0 := rfl
  dsimp only [NatOne]
  rw [nA_eq, hm]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel

theorem bud : cost 64 ≤ 0x1000 := by decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies `PreGR` (`z.subMod2N(z, y, 64)`, `z = [5]` cap 1, `y = [3]`) -/
theorem pre : PreGR R 0x1000 [] OP OA 1 1 YP 1 1 64 s0 := by
  have hm : s0.mem = mem0 := rfl
  have hone := one0
  unfold PreGR
  refine ⟨?_, WStubs.serves [], ?_, hone, ?_⟩
  · refine ⟨⟨by decide +kernel, by rw [hm, acc0]; decide +kernel, by decide +kernel⟩,
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [hm, acc0]; decide +kernel⟩,
      dataLoaded _ _, ?_, by simp only [Apart]; decide +kernel, ?_, fun r hr => by simp at hr, roOut⟩
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  repeat' apply And.intro
  all_goals first
    | decide
    | exact inv1 _
    | (intro _; exact bud)
    | exact bud
    | (intro h; exact absurd h (by decide))
    | (simp only [Apart, nA_eq]; decide +kernel)
    | (intro _; simp only [hm, acc0]; decide +kernel)
    | (intro _; simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _ _; simp only [Apart]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [hm, NatNorm]; decide +kernel)
    | (simp only [NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, hm, acc0]; decide +kernel)
    | trivial

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, the call `z.subMod2N(z, y, 64)` with `z = [5]` (cap 1), `y = [3]`; one call-site
state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (op zp zl zc yp yl yc n : Nat) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program SubMod2N.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n] s ∧
    PreGR R b L op zp zl zc yp yl yc n s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ PostG R b L zp zl zc yp yl n (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], OP, OA, 1, 1, YP, 1, 1, 64, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _) 0x1000 [] OP OA 1 1 YP 1 1 64
      s0 setup pre RET hret⟩

end FvModexp.Arm64.SubMod2NRow.Witness
