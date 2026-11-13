import FvModexp.Proofs.Amd64.Exp.SubMod2NGR
import FvModexp.Proofs.Amd64.Nat.Trunc
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row: `nat.subMod2N` (amd64) on the Run extraction (agent infra s49; twin of Arm64/Exp/SubMod2NRow.lean)

`correctness` = `SubMod2N.ensG` (general form: any capacity of `z`, empty / `nil` operands) with the PROVED callees
`nat.trunc` (asm `Trunc.ens`), `nat.sub` (divmc `NatSub.ensR0`) and `nat.add` (divmc `NatAdd.ensR`, inside `ensG`) and
asm's `nat.cmp`, moved to `Extracted.program.link impl` (`Ensures.full64`). Runtime premises: the live `makeslice`,
`memmove` and `growslice` contracts. `n` is the tenth argument, passed on the stack (`[RSP + 8]`, `PreGR`'s `EntR`).
`Witness.nonvacuous`: the shared witness runtime, the toy allocator invariant, `natOne` (header outside the extracted
data, its word in the `OB` object), the call `z.subMod2N(z, y, 64)` with `z = [5]` (cap 1), `y = [3]`, `n = 64` at
`SP0 + 8`; one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.SubMod2NRow

open FvModexp.Amd64.SubMod2N

set_option maxHeartbeats 64000000 in
theorem trW_sub : ∀ x, Trunc.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)
set_option maxHeartbeats 64000000 in
theorem trW_fn : Trunc.names.contains SubMod2N.fn = false := by decide

/-- **`nat.subMod2N`** (amd64): `z.subMod2N(z, y, n)` returns a normalised nat holding `(Z − Y) mod 2^n`
(`Exp.subMod2N`), in `z`'s array or a fresh one, for every runtime meeting the live `makeslice` / `memmove` /
`growslice` contracts (`PreGR` / `PostG`; no constraint on the return address beyond the ABI). -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program SubMod2N.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc]
      (PreGR R b L op zp zl zc yp yl yc n) (PostG R b L zp zl zc yp yl n) :=
  Ensures.full64 hap (by simp [numIntRegs])
    (ensGR_of (SubMod2N.ensG impl hap R trW_sub trW_fn (by omega) (by omega) (Trunc.ens impl hap R hmk hmv) hmk hmv
      hgr) b L op zp zl zc yp yl yc n)

end FvModexp.Amd64.SubMod2NRow

namespace FvModexp.Amd64.SubMod2NRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy FvModexp.Amd64.SubMod2N FvModexp.Amd64.EvenHyp

set_option maxRecDepth 100000

/-- `natOne`'s header (outside the extracted data) -/
abbrev NA : Nat := 12050400
/-- the witness's backing word of `natOne` -/
abbrev OP : Nat := OB + 0x800
abbrev YP : Nat := OB

theorem nA_eq : natOneA = NA := by decide

/-- `z = [5]` at `OA`, `y = [3]` at `OB`, `natOne = {OP, 1, 1}` with `OP[0] = 1`, `n = 64` at `SP0 + 8`, all other
witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OA then 5 else if a = YP then 3 else if a = OP then 1 else if a = SP0 + 8 then 64
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xE0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else 0

def regs : List Janus.Arm64.Region := stdRegs ++ [⟨NA, 24, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 YP, 1, 1]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 1 else if i = 1 then 1
      else if i = 7 then BitVec.ofNat 64 OA else if i = 6 then 1 else if i = 8 then 1
      else if i = 9 then BitVec.ofNat 64 YP else if i = 10 then 1 else if i = 11 then 1
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program SubMod2N.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program SubMod2N.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

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
  · refine ⟨?_, ?_, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut, ⟨?_, ?_, ?_⟩⟩
    all_goals first
      | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [Apart]; decide +kernel)
      | (rw [hm, acc0]; decide +kernel)
      | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [hm, acc0]; decide +kernel)
      | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [hm, acc0]; decide +kernel)
      | decide +kernel
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
    | (rw [hm]; decide +kernel)
    | decide +kernel
    | trivial

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, the call `z.subMod2N(z, y, 64)` with `z = [5]` (cap 1), `y = [3]`, `n = 64` on the
stack; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (op zp zl zc yp yl yc n : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096
      R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program SubMod2N.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc] s ∧
    PreGR R b L op zp zl zc yp yl yc n s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ PostG R b L zp zl zc yp yl n s s' :=
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
      RET hret s0 setup pre⟩

end FvModexp.Amd64.SubMod2NRow.Witness
