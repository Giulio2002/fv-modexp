import FvModexp.Proofs.Amd64.Nat.Rsh
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Stubs

/-!
# Row: `nat.rsh` (amd64) on the Run extraction (see the arm64 twin)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.RshRow

/-- **`nat.rsh`** (amd64): `z.rsh(x, s)` (`x` normalised, `0 < len x`, `z` apart from `x`) returns a normalised nat
holding `X / 2^s`, in `z`'s array (`cap z ≥ len x - s/64`) or a fresh one of capacity `≥ len x - s/64`; writes only
`z`'s array and the window; keeps `FS` and `DF`; for every runtime meeting the live `makeslice`/`memmove`
contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc sh : BitVec 64) :
    Ensures (Extracted.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh")
      [zp, zl, zc, xp, xl, xc, sh]
      (fun s => Rsh.RshPre R b L 4248 64 zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat sh.toNat s ∧
        xl.toNat ≤ xc.toNat ∧ xc.toNat < 2 ^ 40)
      (fun s s' => Rsh.RshPost R b L 4248 64 zp.toNat zc.toNat xp.toNat xl.toNat sh.toNat s s') :=
  Ensures.full64 hap (by simp [numIntRegs]) (Rsh.ens impl hap R hmk hmv b L zp zl zc xp xl xc sh)

end FvModexp.Amd64.RshRow

namespace FvModexp.Amd64.RshRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 0 else if i = 1 then 0
      else if i = 7 then BitVec.ofNat 64 OB else if i = 6 then 2 else if i = 8 then 2 else if i = 9 then 3
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh"),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET)
    (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh") args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem top : mem0.readLE (OB + 8 * (2 - 1)) 8 ≠ 0 := by decide +kernel

theorem pre : Rsh.RshPre R 0x1000 [] 4248 64 OA 0 0 OB 2 3 s0 ∧ 2 ≤ 2 ∧ 2 < 2 ^ 40 := by
  refine ⟨⟨⟨?_, ?_, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut, ⟨?_, ?_, ?_⟩⟩,
    WStubs.serves [], by decide, ⟨by decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
    ⟨by decide, ?_, by decide, Or.inr ?_, ?_⟩, by decide, fun h => absurd h (by decide), Or.inr top, by decide,
    Or.inl (by decide), by decide, inv0 g bump _⟩, by decide, by decide⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together, one call-site state per
runtime contract, and the call `z.rsh(x, 3)` (`cap z = 0`, `len x = 2`) returns. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc sh : BitVec 64) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh")
      [zp, zl, zc, xp, xl, xc, sh] s ∧
    (Rsh.RshPre R b L 4248 64 zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat sh.toNat s ∧
      xl.toNat ≤ xc.toNat ∧ xc.toNat < 2 ^ 40) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Rsh.RshPost R b L 4248 64 zp.toNat zc.toNat xp.toNat xl.toNat sh.toNat s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) 0x1000 [] (BitVec.ofNat 64 OA) 0 0 (BitVec.ofNat 64 OB) 2 2 3 RET
      hret s0 setup pre⟩

end FvModexp.Amd64.RshRow.Witness
