import FvModexp.Proofs.Arm64.Int.IntAS
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

/-!
# Row: `(*Int).Add` / `(*Int).Sub` (arm64) on the Run extraction

`correctness` = `IntAS.ens` moved to `Extracted.program.link impl` (`Ensures.full`), `Sub`: row `IntSubRow` (literal symbol names, audit round 8 I1);
runtime premises: the live `makeslice`, `memmove` and `gcWriteBarrier2` contracts. `Witness.nonvacuous`: the shared
witness runtime (`WStubs.impl`), the toy allocator invariant, the Run extraction's read-only data loaded, the
`runtime.writeBarrier` flag word readable (0: barrier off), and the call `z.Add(x, y)` with `x = 5`, `y = 9` (one limb
each, non-negative) and `z = 0` with a 2-word array; plus one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.IntASRow

/-- **`(*Int).Add` (`sub = false`) / `(*Int).Sub` (`sub = true`)** (arm64): `z.Add(x, y)` / `z.Sub(x, y)` returns `z`
holding `x + y` / `x - y` (signed, canonical sign, normalised `abs` in `z`'s array or a fresh one); writes only `z`'s
header, `z`'s array, the runtime's memory and the window; for every runtime meeting the live `makeslice`/`memmove`/
write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add") [z, x, y]
      (IntAS.Pre R b L z.toNat x.toNat y.toNat) (IntAS.Post false R b L z.toNat x.toNat y.toNat) :=
  Ensures.full hap (IntAS.ens impl hap R hmk hmv hwb false b L z x y)

end FvModexp.Arm64.IntASRow

namespace FvModexp.Arm64.IntASRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `z` header at `OA` (`abs = (OB + 0x100, 0, 2)`), `x` at `OA + 0x40` (`abs = (OB, 1, 1)`, `5`), `y` at
`OA + 0x80` (`abs = (OB + 0x40, 1, 1)`, `9`); all other witness bytes 0. -/
def g (a : Nat) : Byte :=
  if a = OA + 9 then 0x01 else if a = OA + 10 then 0xB0 else if a = OA + 24 then 2 else
  if a = OA + 0x48 + 2 then 0xB0 else if a = OA + 0x50 then 1 else if a = OA + 0x58 then 1 else
  if a = OA + 0x88 then 0x40 else if a = OA + 0x88 + 2 then 0xB0 else if a = OA + 0x90 then 1 else
  if a = OA + 0x98 then 1 else
  if a = OB then 5 else if a = OB + 0x40 then 9 else 0

/-- the standard regions plus the (read-only here) `runtime.writeBarrier` flag word -/
def regs : List Region := stdRegs ++ [⟨IntAS.wbA, 8, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), BitVec.ofNat 64 (OA + 0x80)]

def s0 (sub : Bool) : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program (IntAS.fn sub)),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET)
    (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add") args (s0 false) :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem setupSub : CallSetup ((Extracted.program.link WStubs.impl).withExit RET)
    (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub") args (s0 true) :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

/-- the toy runtime's invariant for the witness memory (as `AsmWit.inv0`, with the extra region) -/
theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem pre (sub : Bool) : IntAS.Pre R 0x1000 [] (BitVec.ofNat 64 OA).toNat (BitVec.ofNat 64 (OA + 0x40)).toNat
    (BitVec.ofNat 64 (OA + 0x80)).toNat (s0 sub) := by
  cases sub
  all_goals
    have hm : ∀ b, (s0 b).mem = mem0 := fun _ => rfl
    refine ⟨⟨⟨by decide +kernel, by rw [hm, acc0]; decide +kernel, by decide +kernel⟩,
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by rw [hm, acc0]; decide +kernel⟩,
      dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut⟩, WStubs.serves [], ?_,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ?_, Or.inr ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ?_, Or.inr ?_, ?_⟩,
      ?_, ?_, ?_, Or.inr ?_, ?_, ?_, Or.inr ?_, ?_, ?_, fun _ => ⟨?_, Or.inr ?_, ?_, ?_⟩, ?_, fun _ => ⟨?_, ?_, Or.inr ?_, Or.inr ?_⟩,
      ?_, ?_, inv1 _⟩
    all_goals first
      | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [Apart]; decide +kernel)
      | (simp only [hm, acc0]; decide +kernel)
      | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime
(toy `makeslice`, looping `memmove`, toy write barrier), budget `0x1000`, empty live set, the call `z.Add(x, y)` with
`x = 5`, `y = 9`, `z`'s array of capacity 2; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z x y : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add") [z, x, y] s ∧
    IntAS.Pre R b L z.toNat x.toNat y.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ IntAS.Post false R b L z.toNat x.toNat y.toNat s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), BitVec.ofNat 64 (OA + 0x80),
    RET, s0 false, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setup, pre false,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 0x1000 []
      (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) (BitVec.ofNat 64 (OA + 0x80)) RET hret (s0 false) setup (pre false)⟩


end FvModexp.Arm64.IntASRow.Witness
