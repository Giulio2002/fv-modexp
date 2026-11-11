import FvModexp.Proofs.Amd64.Nat.MulAddWW
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Stubs

/-!
# Row: `nat.mulAddWW` (amd64) on the Run extraction

`correctness` = `MulAddWW.ens` moved to `Extracted.program.link impl` (`Ensures.full64`); its one runtime premise is
the live `makeslice` contract. `Witness.nonvacuous`: the shared amd64 witness runtime (`WStubs.impl`, toy bump
`makeslice`), the toy allocator invariant, the read-only data loaded, the TLS slot holding `g`, the call
`z.mulAddWW(x, 3, 0)` with `cap z = 0` (so `make` calls `makeslice`), `len x = 2`, a `makeslice` call-site state and
the returning run.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.MulAddWWRow

/-- **`nat.mulAddWW`** (amd64): returns a normalised nat holding `X·y + r` in `z`'s array or a fresh one; writes only
`z`'s array and the window; for every runtime meeting the live `makeslice` contract. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program MulAddWW.fn) [zp, zl, zc, xp, xl, xc, y, r]
      (MulAddWW.Pre R b L zp zc xp xl y r) (MulAddWW.Post R b L zp zc xp xl y r) :=
  Ensures.full64 hap (by simp [numIntRegs]) (MulAddWW.ens impl hap R hmk b L zp zl zc xp xl xc y r)

end FvModexp.Amd64.MulAddWWRow

namespace FvModexp.Amd64.MulAddWWRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3, 0]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 0 else if i = 1 then 0
      else if i = 7 then BitVec.ofNat 64 OB else if i = 6 then 2 else if i = 8 then 2 else if i = 9 then 3
      else if i = 10 then 0 else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program MulAddWW.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program MulAddWW.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem pre : MulAddWW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 0 (BitVec.ofNat 64 OB) 2 3 0 s0 := by
  refine ⟨⟨?_, ?_, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut, ⟨?_, ?_, ?_⟩⟩, ?_,
    by decide, by decide, fun h => absurd h (by decide), ?_, fun h => absurd h (by decide), ?_, by decide, Or.inr ?_, ?_,
    ?_, fun _ => ⟨trivial, by decide⟩⟩
  all_goals first
    | exact inv0 g bump _
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together, a `makeslice` call-site
state, and the call returns: the shared witness runtime (toy `makeslice`), budget `0x1000`, empty live set, the call
`z.mulAddWW(x, 3, 0)` with `cap z = 0`, `len x = 2`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc y r : BitVec 64) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program MulAddWW.fn)
      [zp, zl, zc, xp, xl, xc, y, r] s ∧
    MulAddWW.Pre R b L zp zc xp xl y r s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ MulAddWW.Post R b L zp zc xp xl y r s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 0, 0, BitVec.ofNat 64 OB, 2, 2, 3, 0, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _) 0x1000
      [] (BitVec.ofNat 64 OA) 0 0 (BitVec.ofNat 64 OB) 2 2 3 0 RET hret s0 setup pre⟩

end FvModexp.Amd64.MulAddWWRow.Witness
