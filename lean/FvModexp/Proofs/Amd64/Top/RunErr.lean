import FvModexp.Proofs.Amd64.Top.RunErrLib
import FvModexp.Proofs.Amd64.Witness.Stubs
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Spec.WitSitesAmd64

/-!
# Row 1, amd64, error path: `Run` on call data that fails EIP-7823 returns `(nil, err)`

`correctness`: for every input slice whose length headers fail `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns a nil `[]byte` and a non-nil `error`, keeping the Go ABI and the memory frame. The
statement uses only `FvModexp.Spec.*` (`Spec.RunAmd64`: environment, input, requests, frame, return).

`Witness.nonvacuous`: every hypothesis and every precondition conjunct hold together, for the shared amd64 witness
runtime (`WStubs`: toy `makeslice`/`newobject`, `REP MOVSB` memmove), a call-site state per contract, and a call whose
base-length header is 1025 (96 input bytes), with the returning run.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run

/-- **Row 1, amd64, EIP-7823 failure.** For every input slice `(p, len, cap)` whose call data fails
`checkLengths (parseLengths data)`, with the Osaka receiver `c`, `Run` returns `(nil, err)` with `err ≠ nil`. -/
theorem correctness (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => RunAmd64.Env R L s ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.ErrReqs R b len ∧
        LengthsFail (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.ErrRet s' ∧ RunAmd64.Frame R b (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) L s s') :=
  Ensures.full64 hap (ns := LibRun.names) (by simp [numIntRegs])
    (LibRun.eq_only ▸ ensErrLib impl hap R hmk hmv hno b L c p len cp)

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- The receiver's three flags (at `OA`) are 1; the input (at `OB`, 96 bytes) has base length `0x0401 = 1025`
(bytes 30, 31); all other witness bytes 0. -/
def g (a : Nat) : Byte :=
  if a = OA ∨ a = OA + 1 ∨ a = OA + 2 then 1 else if a = OB + 30 then 4 else if a = OB + 31 then 1 else 0

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) stdRegs

def c0 : BitVec 64 := BitVec.ofNat 64 OA
def p0 : BitVec 64 := BitVec.ofNat 64 OB

def s0 : State :=
  { regs := fun i => if i = 0 then c0 else if i = 3 then p0 else if i = 1 then 96 else if i = 7 then 96
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program RunAmd64.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program RunAmd64.fn)
    [c0, p0, 96, 96] s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem fail0 : LengthsFail (bytesAt s0.mem p0.toNat (96 : BitVec 64).toNat) := by
  intro h
  rw [lengthsPass_iff] at h
  have := h.1
  revert this
  decide +kernel

theorem pre : RunAmd64.Env R [] s0 ∧ RunAmd64.Input R [] c0 p0 96 96 s0 ∧ OsakaReceiver s0.mem c0.toNat ∧
    R.inv 0x1000 [] (s0.regs 14).toNat (view R.rt [] s0.mem) ∧ RunAmd64.ErrReqs R 0x1000 96 ∧
    LengthsFail (bytesAt s0.mem p0.toNat (96 : BitVec 64).toNat) := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩,
    ⟨?_, by decide, Or.inr ?_, ?_, by decide, by decide, by decide, ?_, Or.inr ?_, ?_⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, inv0 g bump _,
    ⟨trivial, fun h => absurd h (by decide), trivial, by decide⟩, fail0⟩
  all_goals first
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [RunAmd64.window, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [show s0.mem = wmem (toyBytes g) stdRegs from rfl, acc_eq]; decide +kernel)
    | decide +kernel

/-- The returning run, exactly as `correctness` states it at the witness. -/
theorem returnsF : Returns ((Extracted.program.link WStubs.impl).withExit RET) s0 fun s' =>
    ABIReturn s0 s' ∧ (RunAmd64.ErrRet s' ∧
      RunAmd64.Frame R 0x1000 (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) [] s0 s') :=
  FvModexp.Amd64.Run.correctness WStubs.impl WStubs.hap R
    (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
    (by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _) 0x1000 [] c0 p0 96 96 RET hret s0 setup pre

/-- All hypotheses of `correctness` hold together, with every conjunct of its precondition, a call-site state for each
contract, and the returning run: the shared witness runtime, an empty live set, budget `0x1000`, and the call
`Run(c, p, 96, 96)` on 96 header bytes whose base length is 1025. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64)
    (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp] s ∧
    RunAmd64.Env R L s ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.ErrReqs R b len ∧
    LengthsFail (bytesAt s.mem p.toNat len.toNat) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      WitSitesAmd64.mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      WitSitesAmd64.mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      WitSitesAmd64.noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (RunAmd64.ErrRet s' ∧
        RunAmd64.Frame R b (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) L s s') :=
  ⟨WStubs.impl, R, 0x1000, [], c0, p0, 96, 96, RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _, by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _, hret, setup,
    pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2.1, pre.2.2.2.2.2,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩, returnsF⟩

end FvModexp.Amd64.Run.Witness
