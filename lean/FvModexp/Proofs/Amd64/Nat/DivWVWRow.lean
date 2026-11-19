import FvModexp.Proofs.Amd64.Nat.DivWVW
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.AsmWit

/-!
# Row: `divWVW` (amd64) on the Run extraction

`correctness` = `DivWVW.ens` moved to `Extracted.program.link impl` (`Ensures.full64`); no runtime premise (the only
callee, `divWW`, is a proved summary inside `DivWVW.names`). `Witness.nonvacuous`: no runtime code (`impl = []`), the
toy allocator invariant, the Run extraction's read-only data loaded (`AsmWit.dataLoaded`), the TLS slot holding `g`,
the call `divWVW(z[0:2], 0, x[0:2], 7)` and its returning run.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivWVWRow

/-- **`divWVW`** (amd64): `RAX = (xn·B^n + x) mod y`, `z[0:n] = (xn·B^n + x) / y`; writes only `z[0:n]` and the
window; for every runtime. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivWVW.fn) [zp, zl, zc, xn, xp, xl, xc, y]
      (fun s => xl = zl ∧ DivWVW.Pre R b L zp zl xn xp y s) (fun s s' => DivWVW.Post R b L zp zl xn xp y s s') :=
  Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Amd64.DivWVW.Pre, FvModexp.Amd64.Callees.CallEnvND, FvModexp.NatLive, FvModexp.Amd64.win]) hap (by simp [numIntRegs]) (DivWVW.ens impl hap R b L zp zl zc xn xp xl xc y)

end FvModexp.Amd64.DivWVWRow

namespace FvModexp.Amd64.DivWVWRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x = 5 + 9·B` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else if a = OB + 8 then 9 else 0

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 2, 2, 0, BitVec.ofNat 64 OB, 2, 2, 7]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 2 else if i = 1 then 2 else if i = 7 then 0
      else if i = 6 then BitVec.ofNat 64 OB else if i = 8 then 2 else if i = 9 then 2 else if i = 10 then 7
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program DivWVW.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

def impl : List Amd64.Segment := []

theorem hap : Amd64.ImplApart Extracted.program impl := implApart_nil

theorem hret : RetAddr (Extracted.program.link impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link impl).withExit RET) (segAddr Extracted.program DivWVW.fn) args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩


theorem setup_at0 : CallSetup0 (segAddr Extracted.program DivWVW.fn) args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem pre : (2 : BitVec 64) = 2 ∧ DivWVW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 0 (BitVec.ofNat 64 OB) 7 s0 := by
  refine ⟨rfl, ⟨?_, ?_, by decide, ?_, ?_, ?_, fun r hr => by simp at hr, ?_, ?_, ?_⟩,
    by decide, by decide, fun _ => ⟨by decide, Or.inr ?_, ?_, by decide⟩, ?_, ?_, by decide, Or.inr ?_, ?_, Or.inr ?_,
    ?_⟩
  all_goals first
    | exact inv0 g bump _
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩; rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq];
        decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together, and the call returns:
budget `0x1000`, empty live set, the call `divWVW(z[0:2], 0, x[0:2], 7)`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xn xp xl xc y : BitVec 64) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program DivWVW.fn)
      [zp, zl, zc, xn, xp, xl, xc, y] s ∧
    (xl = zl ∧ DivWVW.Pre R b L zp zl xn xp y s) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧
      DivWVW.Post R b L zp zl xn xp y (s.setRet ret) s' :=
  ⟨impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, 0, BitVec.ofNat 64 OB, 2, 2, 7, RET, s0, hap, hret, setup_at0, pre,
    correctness impl hap R 0x1000 [] (BitVec.ofNat 64 OA) 2 2 0 (BitVec.ofNat 64 OB) 2 2 7 s0 setup_at0 pre RET hret⟩

end FvModexp.Amd64.DivWVWRow.Witness
