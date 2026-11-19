import FvModexp.Proofs.Amd64.Nat.AddVW
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Stubs

/-!
# Row: `addVW` (amd64) on the Run extraction

`correctness` = `AddVW.ens` moved to `Extracted.program.link impl` (`Ensures.full64`); its one runtime premise is the
live `memmove` contract. `Witness.nonvacuous`: the shared amd64 witness runtime (`WStubs.impl`, `REP MOVSB` `memmove`
of any size), the toy allocator invariant, the TLS slot holding `g`, the call `addVW(z[0:2], x[0:2], 1)` with `z`, `x`
two-limb arrays apart (so `copy` calls `memmove`), a `memmove` call-site state and the returning run.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.AddVWRow

/-- **`addVW`** (amd64): `z[0:n] = (x[0:n] + y) mod B^n`, carry `(x + y) / B^n` in `RAX`; writes only `z[0:n]` and the
window; for every runtime meeting the live `memmove` contract. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program AddVW.fn) [zp, zl, zc, xp, xl, xc, y]
      (fun s => xl = zl ∧ AddVW.Pre R b L zp zl zc xp xc s) (fun s s' => AddVW.Post R b L zp zl xp y s s') :=
  Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Amd64.AddVW.Pre, FvModexp.Amd64.Callees.CallEnvND, FvModexp.NatLive, FvModexp.Amd64.win]) hap (by simp [numIntRegs]) (AddVW.ens impl hap R hmv b L zp zl zc xp xl xc y)

end FvModexp.Amd64.AddVWRow

namespace FvModexp.Amd64.AddVWRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `x[0] = 5` (at `OB`), all other witness bytes 0 -/
def g (a : Nat) : Byte := if a = OB then 5 else 0

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) stdRegs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 2, 2, 1]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 2 else if i = 1 then 2
      else if i = 7 then BitVec.ofNat 64 OB else if i = 6 then 2 else if i = 8 then 2 else if i = 9 then 1
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program AddVW.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program AddVW.fn)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem pre : (2 : BitVec 64) = 2 ∧ AddVW.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 OB) 2 s0 := by
  refine ⟨rfl, ⟨?_, ?_, by decide, ?_, ?_, ?_, fun r hr => by simp at hr, ?_, ?_, ?_⟩,
    by decide, by decide, by decide, by decide, fun _ => ⟨by decide, Or.inr ?_, ?_, by decide⟩, ?_, fun _ => ⟨?_, ?_⟩,
    ?_, by decide, Or.inr ?_, ?_, Or.inr ?_, ?_, ?_⟩
  all_goals first
    | exact inv0 g bump _
    | (rw [if_neg (by decide)]; intro j _ _; trivial)
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

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together, a `memmove` call-site
state, and the call returns: the shared witness runtime, budget `0x1000`, empty live set, `addVW(z[0:2], x[0:2], 1)`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc y : BitVec 64) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program AddVW.fn)
      [zp, zl, zc, xp, xl, xc, y] s ∧
    (xl = zl ∧ AddVW.Pre R b L zp zl zc xp xc s) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧ AddVW.Post R b L zp zl xp y (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 OB, 2, 2, 1, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mv]; exact WStubs.mv R) 0x1000 [] (BitVec.ofNat 64 OA) 2 2
      (BitVec.ofNat 64 OB) 2 2 1 s0 setup pre RET hret⟩

end FvModexp.Amd64.AddVWRow.Witness
