import FvModexp.Proofs.Arm64.Top.RunErrLib
import FvModexp.Proofs.Arm64.Witness.Stubs

/-!
# Row 1, arm64, error path: `Run` on call data that fails EIP-7823 returns `(nil, err)`

`correctness`: for every input slice whose length headers fail `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns a nil `[]byte` and a non-nil `error`, keeping the Go ABI and the memory frame. The
statement uses only `FvModexp.Spec.*` (`Spec.RunArm64`: environment, input, requests, frame, return).

`Witness.nonvacuous`: every hypothesis and every precondition conjunct hold together, for a runtime built from the Janus toy
allocator (`makeslice`/`newobject` bump stubs reading the type descriptor, a `memmove` stub that is never requested) and
a call whose base-length header is 1025.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- **Row 1, arm64, EIP-7823 failure.** For every input slice `(p, len, cap)` whose call data fails
`checkLengths (parseLengths data)`, with the Osaka receiver `c`, `Run` returns `(nil, err)` with `err ≠ nil`. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => RunArm64.Env R L s ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.ErrReqs R b len ∧
        LengthsFail (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunArm64.ErrRet s' ∧ RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s') :=
  Ensures.full hap (ns := LibRun.names) (LibRun.eq_only ▸ ensErrLib impl hap R hmk hmv hno b L c p len cp)

end FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
open FvModexp.Spec

namespace FvModexp.Arm64.Run.Witness

set_option maxRecDepth 100000

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def noA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")

/-- The shared witness runtime (`WStubs`): a stub at every contract address of the Run extraction. -/
def implAt : List Segment := WStubs.impl

theorem hap : ImplApart Extracted.program implAt := WStubs.hap

/-- Every request is served (the stubs never consult `ok`). -/
def ok : Nat → List Nat → Prop := fun _ _ => True

def R : RtInv := toyR [] ok

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_no : Extracted.program.contractAddr "runtime.newobject" = noA := by decide

theorem tys0 : TysOK [] := by intro t ht; simp at ht

theorem model_mv : MemmoveLive (Extracted.program.ofImpl implAt) mvA 4096 R := WStubs.mv R
theorem model_mk : MakesliceLiveContract (Extracted.program.ofImpl implAt) mkA 4096 R := WStubs.mk [] tys0 ok
theorem model_no : NewobjectLiveContract (Extracted.program.ofImpl implAt) noA 4096 R := WStubs.no [] tys0 ok

def ret : Nat := 0x1000
def sp0 : Nat := 0x800000
def g0 : Nat := 0x900000
def cR : Nat := 0xA00000
def pI : Nat := 0xA00100

/-- The read-only data of the extraction, by address (generated from `Extracted.lean`: the 49 objects in address order). -/
def dataByteW (a : Nat) : Option Byte :=
  if 0x2844c0 ≤ a ∧ a < 0x284640 then some (BitVec.ofNat 8 (Extracted.data0.bytes.getD (a - 0x2844c0) 0)) else
  if 0x284bc0 ≤ a ∧ a < 0x284dc0 then some (BitVec.ofNat 8 (Extracted.data1.bytes.getD (a - 0x284bc0) 0)) else
  if 0x28c500 ≤ a ∧ a < 0x28c600 then some (BitVec.ofNat 8 (Extracted.data2.bytes.getD (a - 0x28c500) 0)) else
  if 0x2a28e0 ≤ a ∧ a < 0x2a29e0 then some (BitVec.ofNat 8 (Extracted.data3.bytes.getD (a - 0x2a28e0) 0)) else
  if 0x2a2fe0 ≤ a ∧ a < 0x2a30e0 then some (BitVec.ofNat 8 (Extracted.data4.bytes.getD (a - 0x2a2fe0) 0)) else
  if 0x2b5ce0 ≤ a ∧ a < 0x2b5de0 then some (BitVec.ofNat 8 (Extracted.data5.bytes.getD (a - 0x2b5ce0) 0)) else
  if 0x2e5f12 ≤ a ∧ a < 0x2e5f16 then some (BitVec.ofNat 8 (Extracted.data6.bytes.getD (a - 0x2e5f12) 0)) else
  if 0x2e648a ≤ a ∧ a < 0x2e648f then some (BitVec.ofNat 8 (Extracted.data7.bytes.getD (a - 0x2e648a) 0)) else
  if 0x2e8cd0 ≤ a ∧ a < 0x2e8cd8 then some (BitVec.ofNat 8 (Extracted.data8.bytes.getD (a - 0x2e8cd0) 0)) else
  if 0x2e8f58 ≤ a ∧ a < 0x2e8f60 then some (BitVec.ofNat 8 (Extracted.data9.bytes.getD (a - 0x2e8f58) 0)) else
  if 0x2e9589 ≤ a ∧ a < 0x2e9592 then some (BitVec.ofNat 8 (Extracted.data10.bytes.getD (a - 0x2e9589) 0)) else
  if 0x2e98e0 ≤ a ∧ a < 0x2e98fb then some (BitVec.ofNat 8 (Extracted.data11.bytes.getD (a - 0x2e98e0) 0)) else
  if 0x2e995e ≤ a ∧ a < 0x2e9970 then some (BitVec.ofNat 8 (Extracted.data12.bytes.getD (a - 0x2e995e) 0)) else
  if 0x2ea181 ≤ a ∧ a < 0x2ea18b then some (BitVec.ofNat 8 (Extracted.data13.bytes.getD (a - 0x2ea181) 0)) else
  if 0x2ea5e3 ≤ a ∧ a < 0x2ea5ee then some (BitVec.ofNat 8 (Extracted.data14.bytes.getD (a - 0x2ea5e3) 0)) else
  if 0x2eafca ≤ a ∧ a < 0x2eafd6 then some (BitVec.ofNat 8 (Extracted.data15.bytes.getD (a - 0x2eafca) 0)) else
  if 0x2ecb24 ≤ a ∧ a < 0x2ecb34 then some (BitVec.ofNat 8 (Extracted.data16.bytes.getD (a - 0x2ecb24) 0)) else
  if 0x2ed820 ≤ a ∧ a < 0x2ed832 then some (BitVec.ofNat 8 (Extracted.data17.bytes.getD (a - 0x2ed820) 0)) else
  if 0x2edbc8 ≤ a ∧ a < 0x2edbda then some (BitVec.ofNat 8 (Extracted.data18.bytes.getD (a - 0x2edbc8) 0)) else
  if 0x2ee417 ≤ a ∧ a < 0x2ee42a then some (BitVec.ofNat 8 (Extracted.data19.bytes.getD (a - 0x2ee417) 0)) else
  if 0x2eebaf ≤ a ∧ a < 0x2eebc3 then some (BitVec.ofNat 8 (Extracted.data20.bytes.getD (a - 0x2eebaf) 0)) else
  if 0x2eecb3 ≤ a ∧ a < 0x2eecc7 then some (BitVec.ofNat 8 (Extracted.data21.bytes.getD (a - 0x2eecb3) 0)) else
  if 0x2ef9a5 ≤ a ∧ a < 0x2ef9bb then some (BitVec.ofNat 8 (Extracted.data22.bytes.getD (a - 0x2ef9a5) 0)) else
  if 0x2f00dd ≤ a ∧ a < 0x2f00f4 then some (BitVec.ofNat 8 (Extracted.data23.bytes.getD (a - 0x2f00dd) 0)) else
  if 0x2f091e ≤ a ∧ a < 0x2f0936 then some (BitVec.ofNat 8 (Extracted.data24.bytes.getD (a - 0x2f091e) 0)) else
  if 0x2f170f ≤ a ∧ a < 0x2f172a then some (BitVec.ofNat 8 (Extracted.data25.bytes.getD (a - 0x2f170f) 0)) else
  if 0x2f17b1 ≤ a ∧ a < 0x2f17cc then some (BitVec.ofNat 8 (Extracted.data26.bytes.getD (a - 0x2f17b1) 0)) else
  if 0x2f2280 ≤ a ∧ a < 0x2f229c then some (BitVec.ofNat 8 (Extracted.data27.bytes.getD (a - 0x2f2280) 0)) else
  if 0x2f2b75 ≤ a ∧ a < 0x2f2b93 then some (BitVec.ofNat 8 (Extracted.data28.bytes.getD (a - 0x2f2b75) 0)) else
  if 0x2f2fcb ≤ a ∧ a < 0x2f2fe9 then some (BitVec.ofNat 8 (Extracted.data29.bytes.getD (a - 0x2f2fcb) 0)) else
  if 0x2f365e ≤ a ∧ a < 0x2f367d then some (BitVec.ofNat 8 (Extracted.data30.bytes.getD (a - 0x2f365e) 0)) else
  if 0x2f6052 ≤ a ∧ a < 0x2f6077 then some (BitVec.ofNat 8 (Extracted.data31.bytes.getD (a - 0x2f6052) 0)) else
  if 0x2f6d4e ≤ a ∧ a < 0x2f6d75 then some (BitVec.ofNat 8 (Extracted.data32.bytes.getD (a - 0x2f6d4e) 0)) else
  if 0x2f7584 ≤ a ∧ a < 0x2f75ad then some (BitVec.ofNat 8 (Extracted.data33.bytes.getD (a - 0x2f7584) 0)) else
  if 0x2f7a7b ≤ a ∧ a < 0x2f7aa5 then some (BitVec.ofNat 8 (Extracted.data34.bytes.getD (a - 0x2f7a7b) 0)) else
  if 0x2f8063 ≤ a ∧ a < 0x2f808d then some (BitVec.ofNat 8 (Extracted.data35.bytes.getD (a - 0x2f8063) 0)) else
  if 0x2f8ee7 ≤ a ∧ a < 0x2f8f15 then some (BitVec.ofNat 8 (Extracted.data36.bytes.getD (a - 0x2f8ee7) 0)) else
  if 0x2f9199 ≤ a ∧ a < 0x2f91c7 then some (BitVec.ofNat 8 (Extracted.data37.bytes.getD (a - 0x2f9199) 0)) else
  if 0x2f97d7 ≤ a ∧ a < 0x2f9807 then some (BitVec.ofNat 8 (Extracted.data38.bytes.getD (a - 0x2f97d7) 0)) else
  if 0x2fa3f9 ≤ a ∧ a < 0x2fa42e then some (BitVec.ofNat 8 (Extracted.data39.bytes.getD (a - 0x2fa3f9) 0)) else
  if 0x2faba5 ≤ a ∧ a < 0x2fabdd then some (BitVec.ofNat 8 (Extracted.data40.bytes.getD (a - 0x2faba5) 0)) else
  if 0x2fb327 ≤ a ∧ a < 0x2fb364 then some (BitVec.ofNat 8 (Extracted.data41.bytes.getD (a - 0x2fb327) 0)) else
  if 0x2fb609 ≤ a ∧ a < 0x2fb748 then some (BitVec.ofNat 8 (Extracted.data42.bytes.getD (a - 0x2fb609) 0)) else
  if 0x2fc400 ≤ a ∧ a < 0x2fc445 then some (BitVec.ofNat 8 (Extracted.data43.bytes.getD (a - 0x2fc400) 0)) else
  if 0x2fc79d ≤ a ∧ a < 0x2fc7e9 then some (BitVec.ofNat 8 (Extracted.data44.bytes.getD (a - 0x2fc79d) 0)) else
  if 0x49ecc8 ≤ a ∧ a < 0x49edc8 then some (BitVec.ofNat 8 (Extracted.data45.bytes.getD (a - 0x49ecc8) 0)) else
  if 0x49f0c0 ≤ a ∧ a < 0x49f1e0 then some (BitVec.ofNat 8 (Extracted.data46.bytes.getD (a - 0x49f0c0) 0)) else
  if 0x49f990 ≤ a ∧ a < 0x49fa10 then some (BitVec.ofNat 8 (Extracted.data47.bytes.getD (a - 0x49f990) 0)) else
  if 0x4a09f8 ≤ a ∧ a < 0x4a0a18 then some (BitVec.ofNat 8 (Extracted.data48.bytes.getD (a - 0x4a09f8) 0)) else
  none

/-- The receiver's three flags are 1; the input's base-length header is `0x0401 = 1025` (bytes 30, 31); the bump cell
holds `HEAP`. -/
def bytes0 (a : Nat) : Byte :=
  match dataByteW a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = cR then 1 else if a = cR + 1 then 1 else if a = cR + 2 then 1
      else if a = pI + 30 then 4 else if a = pI + 31 then 1 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4800, 4840, true⟩, ⟨g0, 0x100, false⟩, ⟨cR, 0x200, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def c0 : BitVec 64 := BitVec.ofNat 64 cR
def p0 : BitVec 64 := BitVec.ofNat 64 pI

def s0 : State :=
  { regs := fun i => if i = 0 then c0 else if i = 1 then p0 else if i = 2 then 96 else if i = 3 then 96
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 (segAddr Extracted.program RunArm64.fn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) (segAddr Extracted.program RunArm64.fn)
    [c0, p0, 96, 96] s0 :=
  ⟨rfl, rfl, by
    intro r h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

/-- `DataLoaded`, one read-only object at a time (one kernel `decide` each; a single `decide` over all 49 objects does not finish in 15 min). -/
theorem dl0 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data0.base &&
      Extracted.data0.base + Extracted.data0.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data0.bytes.length), (s0.mem.bytes (Extracted.data0.base + i)).toNat = Extracted.data0.bytes[i] := by
  decide +kernel

theorem dl1 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data1.base &&
      Extracted.data1.base + Extracted.data1.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data1.bytes.length), (s0.mem.bytes (Extracted.data1.base + i)).toNat = Extracted.data1.bytes[i] := by
  decide +kernel

theorem dl2 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data2.base &&
      Extracted.data2.base + Extracted.data2.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data2.bytes.length), (s0.mem.bytes (Extracted.data2.base + i)).toNat = Extracted.data2.bytes[i] := by
  decide +kernel

theorem dl3 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data3.base &&
      Extracted.data3.base + Extracted.data3.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data3.bytes.length), (s0.mem.bytes (Extracted.data3.base + i)).toNat = Extracted.data3.bytes[i] := by
  decide +kernel

theorem dl4 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data4.base &&
      Extracted.data4.base + Extracted.data4.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data4.bytes.length), (s0.mem.bytes (Extracted.data4.base + i)).toNat = Extracted.data4.bytes[i] := by
  decide +kernel

theorem dl5 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data5.base &&
      Extracted.data5.base + Extracted.data5.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data5.bytes.length), (s0.mem.bytes (Extracted.data5.base + i)).toNat = Extracted.data5.bytes[i] := by
  decide +kernel

theorem dl6 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data6.base &&
      Extracted.data6.base + Extracted.data6.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data6.bytes.length), (s0.mem.bytes (Extracted.data6.base + i)).toNat = Extracted.data6.bytes[i] := by
  decide +kernel

theorem dl7 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data7.base &&
      Extracted.data7.base + Extracted.data7.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data7.bytes.length), (s0.mem.bytes (Extracted.data7.base + i)).toNat = Extracted.data7.bytes[i] := by
  decide +kernel

theorem dl8 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data8.base &&
      Extracted.data8.base + Extracted.data8.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data8.bytes.length), (s0.mem.bytes (Extracted.data8.base + i)).toNat = Extracted.data8.bytes[i] := by
  decide +kernel

theorem dl9 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data9.base &&
      Extracted.data9.base + Extracted.data9.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data9.bytes.length), (s0.mem.bytes (Extracted.data9.base + i)).toNat = Extracted.data9.bytes[i] := by
  decide +kernel

theorem dl10 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data10.base &&
      Extracted.data10.base + Extracted.data10.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data10.bytes.length), (s0.mem.bytes (Extracted.data10.base + i)).toNat = Extracted.data10.bytes[i] := by
  decide +kernel

theorem dl11 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data11.base &&
      Extracted.data11.base + Extracted.data11.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data11.bytes.length), (s0.mem.bytes (Extracted.data11.base + i)).toNat = Extracted.data11.bytes[i] := by
  decide +kernel

theorem dl12 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data12.base &&
      Extracted.data12.base + Extracted.data12.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data12.bytes.length), (s0.mem.bytes (Extracted.data12.base + i)).toNat = Extracted.data12.bytes[i] := by
  decide +kernel

theorem dl13 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data13.base &&
      Extracted.data13.base + Extracted.data13.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data13.bytes.length), (s0.mem.bytes (Extracted.data13.base + i)).toNat = Extracted.data13.bytes[i] := by
  decide +kernel

theorem dl14 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data14.base &&
      Extracted.data14.base + Extracted.data14.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data14.bytes.length), (s0.mem.bytes (Extracted.data14.base + i)).toNat = Extracted.data14.bytes[i] := by
  decide +kernel

theorem dl15 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data15.base &&
      Extracted.data15.base + Extracted.data15.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data15.bytes.length), (s0.mem.bytes (Extracted.data15.base + i)).toNat = Extracted.data15.bytes[i] := by
  decide +kernel

theorem dl16 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data16.base &&
      Extracted.data16.base + Extracted.data16.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data16.bytes.length), (s0.mem.bytes (Extracted.data16.base + i)).toNat = Extracted.data16.bytes[i] := by
  decide +kernel

theorem dl17 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data17.base &&
      Extracted.data17.base + Extracted.data17.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data17.bytes.length), (s0.mem.bytes (Extracted.data17.base + i)).toNat = Extracted.data17.bytes[i] := by
  decide +kernel

theorem dl18 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data18.base &&
      Extracted.data18.base + Extracted.data18.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data18.bytes.length), (s0.mem.bytes (Extracted.data18.base + i)).toNat = Extracted.data18.bytes[i] := by
  decide +kernel

theorem dl19 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data19.base &&
      Extracted.data19.base + Extracted.data19.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data19.bytes.length), (s0.mem.bytes (Extracted.data19.base + i)).toNat = Extracted.data19.bytes[i] := by
  decide +kernel

theorem dl20 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data20.base &&
      Extracted.data20.base + Extracted.data20.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data20.bytes.length), (s0.mem.bytes (Extracted.data20.base + i)).toNat = Extracted.data20.bytes[i] := by
  decide +kernel

theorem dl21 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data21.base &&
      Extracted.data21.base + Extracted.data21.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data21.bytes.length), (s0.mem.bytes (Extracted.data21.base + i)).toNat = Extracted.data21.bytes[i] := by
  decide +kernel

theorem dl22 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data22.base &&
      Extracted.data22.base + Extracted.data22.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data22.bytes.length), (s0.mem.bytes (Extracted.data22.base + i)).toNat = Extracted.data22.bytes[i] := by
  decide +kernel

theorem dl23 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data23.base &&
      Extracted.data23.base + Extracted.data23.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data23.bytes.length), (s0.mem.bytes (Extracted.data23.base + i)).toNat = Extracted.data23.bytes[i] := by
  decide +kernel

theorem dl24 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data24.base &&
      Extracted.data24.base + Extracted.data24.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data24.bytes.length), (s0.mem.bytes (Extracted.data24.base + i)).toNat = Extracted.data24.bytes[i] := by
  decide +kernel

theorem dl25 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data25.base &&
      Extracted.data25.base + Extracted.data25.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data25.bytes.length), (s0.mem.bytes (Extracted.data25.base + i)).toNat = Extracted.data25.bytes[i] := by
  decide +kernel

theorem dl26 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data26.base &&
      Extracted.data26.base + Extracted.data26.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data26.bytes.length), (s0.mem.bytes (Extracted.data26.base + i)).toNat = Extracted.data26.bytes[i] := by
  decide +kernel

theorem dl27 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data27.base &&
      Extracted.data27.base + Extracted.data27.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data27.bytes.length), (s0.mem.bytes (Extracted.data27.base + i)).toNat = Extracted.data27.bytes[i] := by
  decide +kernel

theorem dl28 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data28.base &&
      Extracted.data28.base + Extracted.data28.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data28.bytes.length), (s0.mem.bytes (Extracted.data28.base + i)).toNat = Extracted.data28.bytes[i] := by
  decide +kernel

theorem dl29 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data29.base &&
      Extracted.data29.base + Extracted.data29.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data29.bytes.length), (s0.mem.bytes (Extracted.data29.base + i)).toNat = Extracted.data29.bytes[i] := by
  decide +kernel

theorem dl30 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data30.base &&
      Extracted.data30.base + Extracted.data30.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data30.bytes.length), (s0.mem.bytes (Extracted.data30.base + i)).toNat = Extracted.data30.bytes[i] := by
  decide +kernel

theorem dl31 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data31.base &&
      Extracted.data31.base + Extracted.data31.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data31.bytes.length), (s0.mem.bytes (Extracted.data31.base + i)).toNat = Extracted.data31.bytes[i] := by
  decide +kernel

theorem dl32 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data32.base &&
      Extracted.data32.base + Extracted.data32.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data32.bytes.length), (s0.mem.bytes (Extracted.data32.base + i)).toNat = Extracted.data32.bytes[i] := by
  decide +kernel

theorem dl33 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data33.base &&
      Extracted.data33.base + Extracted.data33.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data33.bytes.length), (s0.mem.bytes (Extracted.data33.base + i)).toNat = Extracted.data33.bytes[i] := by
  decide +kernel

theorem dl34 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data34.base &&
      Extracted.data34.base + Extracted.data34.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data34.bytes.length), (s0.mem.bytes (Extracted.data34.base + i)).toNat = Extracted.data34.bytes[i] := by
  decide +kernel

theorem dl35 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data35.base &&
      Extracted.data35.base + Extracted.data35.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data35.bytes.length), (s0.mem.bytes (Extracted.data35.base + i)).toNat = Extracted.data35.bytes[i] := by
  decide +kernel

theorem dl36 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data36.base &&
      Extracted.data36.base + Extracted.data36.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data36.bytes.length), (s0.mem.bytes (Extracted.data36.base + i)).toNat = Extracted.data36.bytes[i] := by
  decide +kernel

theorem dl37 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data37.base &&
      Extracted.data37.base + Extracted.data37.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data37.bytes.length), (s0.mem.bytes (Extracted.data37.base + i)).toNat = Extracted.data37.bytes[i] := by
  decide +kernel

theorem dl38 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data38.base &&
      Extracted.data38.base + Extracted.data38.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data38.bytes.length), (s0.mem.bytes (Extracted.data38.base + i)).toNat = Extracted.data38.bytes[i] := by
  decide +kernel

theorem dl39 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data39.base &&
      Extracted.data39.base + Extracted.data39.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data39.bytes.length), (s0.mem.bytes (Extracted.data39.base + i)).toNat = Extracted.data39.bytes[i] := by
  decide +kernel

theorem dl40 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data40.base &&
      Extracted.data40.base + Extracted.data40.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data40.bytes.length), (s0.mem.bytes (Extracted.data40.base + i)).toNat = Extracted.data40.bytes[i] := by
  decide +kernel

theorem dl41 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data41.base &&
      Extracted.data41.base + Extracted.data41.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data41.bytes.length), (s0.mem.bytes (Extracted.data41.base + i)).toNat = Extracted.data41.bytes[i] := by
  decide +kernel

theorem dl42 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data42.base &&
      Extracted.data42.base + Extracted.data42.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data42.bytes.length), (s0.mem.bytes (Extracted.data42.base + i)).toNat = Extracted.data42.bytes[i] := by
  decide +kernel

theorem dl43 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data43.base &&
      Extracted.data43.base + Extracted.data43.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data43.bytes.length), (s0.mem.bytes (Extracted.data43.base + i)).toNat = Extracted.data43.bytes[i] := by
  decide +kernel

theorem dl44 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data44.base &&
      Extracted.data44.base + Extracted.data44.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data44.bytes.length), (s0.mem.bytes (Extracted.data44.base + i)).toNat = Extracted.data44.bytes[i] := by
  decide +kernel

theorem dl45 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data45.base &&
      Extracted.data45.base + Extracted.data45.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data45.bytes.length), (s0.mem.bytes (Extracted.data45.base + i)).toNat = Extracted.data45.bytes[i] := by
  decide +kernel

theorem dl46 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data46.base &&
      Extracted.data46.base + Extracted.data46.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data46.bytes.length), (s0.mem.bytes (Extracted.data46.base + i)).toNat = Extracted.data46.bytes[i] := by
  decide +kernel

theorem dl47 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data47.base &&
      Extracted.data47.base + Extracted.data47.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data47.bytes.length), (s0.mem.bytes (Extracted.data47.base + i)).toNat = Extracted.data47.bytes[i] := by
  decide +kernel

theorem dl48 : (s0.mem.regions.any fun r => r.base ≤ Extracted.data48.base &&
      Extracted.data48.base + Extracted.data48.bytes.length ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < Extracted.data48.bytes.length), (s0.mem.bytes (Extracted.data48.base + i)).toNat = Extracted.data48.bytes[i] := by
  decide +kernel

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  show ∀ d ∈ Extracted.data, _
  simp only [Extracted.data, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨dl0, dl1, dl2, dl3, dl4, dl5, dl6, dl7, dl8, dl9, dl10, dl11, dl12, dl13, dl14, dl15, dl16, dl17, dl18, dl19, dl20, dl21, dl22, dl23, dl24, dl25, dl26, dl27, dl28, dl29, dl30, dl31, dl32, dl33, dl34, dl35, dl36, dl37, dl38, dl39, dl40, dl41, dl42, dl43, dl44, dl45, dl46, dl47, dl48⟩

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByteW a = none := by
  unfold dataByteW
  repeat rw [if_neg (by omega)]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv0 : R.inv 0x1000 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_live (m := mem0) (g := (s0.regs 28).toNat) (p0 := HEAP) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro r hr; simp at hr) bytes0_bump (fun i hi hi' => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [cR, HEAP] at *; omega),
    if_neg (by simp only [cR, HEAP] at *; omega), if_neg (by simp only [cR, HEAP] at *; omega),
    if_neg (by simp only [pI, HEAP] at *; omega), if_neg (by simp only [pI, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem fail0 : LengthsFail (bytesAt s0.mem p0.toNat (96 : BitVec 64).toNat) := by
  intro h
  rw [lengthsPass_iff] at h
  have := h.1
  revert this
  decide +kernel

theorem pre : RunArm64.Env R [] s0 ∧ RunArm64.Input R [] c0 p0 96 96 s0 ∧ OsakaReceiver s0.mem c0.toNat ∧
    R.inv 0x1000 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧ RunArm64.ErrReqs R 0x1000 96 ∧
    LengthsFail (bytesAt s0.mem p0.toNat (96 : BitVec 64).toNat) := by
  refine ⟨⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, dataLoaded, ?_, ?_, ?_,
      by intro r hr; simp at hr, ?_⟩,
    ⟨by decide +kernel, by decide +kernel, Or.inr ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inr ?_, ?_⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, inv0, ⟨?_, fun h => absurd h (by decide +kernel), ?_, by decide +kernel⟩, fail0⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [Apart]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · intro d hd; rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]
    have : ∀ d' ∈ Extracted.program.data, (d'.base + d'.bytes.length ≤ HEAP ∨ HEND ≤ d'.base) ∧
        (d'.base + d'.bytes.length ≤ BUMP ∨ BUMP + 8 ≤ d'.base) ∧ (d'.base + d'.bytes.length ≤ WBUF ∨ WBUF + 64 ≤ d'.base) := by
      decide +kernel
    exact this d hd
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [RunArm64.window, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [RunArm64.window, outside_cons, outside_nil, and_true]; decide +kernel
  · trivial
  · trivial


/-! ## Call-site states of the three contracts (Janus audit: each contract precondition is satisfiable) -/

def callS (addr x y z : Nat) : State :=
  { s0 with pc := BitVec.ofNat 64 addr,
            regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 1 then BitVec.ofNat 64 y
              else if i = 2 then BitVec.ofNat 64 z else s0.regs i }

theorem cs_callOK (a x y z n : Nat) (hn : n ≤ 3) : CallOK (callS a x y z) 4096 n := by
  have hw : mem0.accessible ((BitVec.ofNat 64 sp0).toNat - 4096) (4096 + 8 + 8 * 3) true = true := by decide +kernel
  have hs : (BitVec.ofNat 64 sp0 : BitVec 64).toNat = sp0 := by decide
  exact ⟨(show (BitVec.ofNat 64 ret : BitVec 64).toNat % 4 = 0 by decide),
    (show (BitVec.ofNat 64 ret : BitVec 64).toNat < 2 ^ 48 by decide),
    (show (BitVec.ofNat 64 sp0 : BitVec 64).toNat % 16 = 0 by decide),
    (show 4096 ≤ (BitVec.ofNat 64 sp0 : BitVec 64).toNat by decide), by decide,
    (show (BitVec.ofNat 64 sp0 : BitVec 64).toNat + 8 + 8 * n ≤ 2 ^ 48 by rw [hs]; unfold sp0; omega),
    (show mem0.accessible ((BitVec.ofNat 64 sp0 : BitVec 64).toNat - 4096) (4096 + 8 + 8 * n) true = true from
      Memory.accessible_mono _ hw (Nat.le_refl _) (by omega))⟩

theorem cs_room (a x y z n : Nat) (hn : n ≤ 3) : StackRoom (callS a x y z) 4096 n := by
  refine ⟨⟨(show (BitVec.ofNat 64 g0 : BitVec 64).toNat + 24 ≤ 2 ^ 48 by decide),
    (show mem0.accessible ((BitVec.ofNat 64 g0 : BitVec 64).toNat + 16) 8 false = true by decide +kernel),
    (show mem0.readLE ((BitVec.ofNat 64 g0 : BitVec 64).toNat + 16) 8 + 4096 < (BitVec.ofNat 64 sp0 : BitVec 64).toNat
      by decide +kernel)⟩, ?_⟩
  show Outside ((BitVec.ofNat 64 g0 : BitVec 64).toNat + 16) 8
    [((BitVec.ofNat 64 sp0 : BitVec 64).toNat - 4096, (BitVec.ofNat 64 sp0 : BitVec 64).toNat - 8),
     ((BitVec.ofNat 64 sp0 : BitVec 64).toNat + 8, (BitVec.ofNat 64 sp0 : BitVec 64).toNat + 8 + 8 * n)]
  have hs : (BitVec.ofNat 64 sp0 : BitVec 64).toNat = sp0 := by decide
  have hg : (BitVec.ofNat 64 g0 : BitVec 64).toNat = g0 := by decide
  rw [hs, hg]; simp only [outside_cons, outside_nil, and_true]; unfold g0 sp0; omega

theorem cs_winR (a x y z n : Nat) (hn : n ≤ 3) : LiveSep (calleeStack (callS a x y z) 4096 n) R.rt := by
  intro x' hx
  simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [rt_eq]
  rcases hx with rfl | rfl <;>
    simp only [outside_cons, outside_nil, and_true] <;>
    show (_ ≤ HEAP ∨ HEND ≤ _) ∧ (_ ≤ BUMP ∨ BUMP + 8 ≤ _) ∧ (_ ≤ WBUF ∨ WBUF + 64 ≤ _) <;>
    simp only [callS, s0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF, BitVec.toNat_ofNat] <;> omega

theorem inv_cs (a x y z : Nat) : R.inv 0x1000 [] ((callS a x y z).regs 28).toNat (view R.rt [] (callS a x y z).mem) :=
  inv0

def sMk : State := callS mkA RunArm64.wordT 4 8
def sNo : State := callS noA RunArm64.errT 0 0
def sMv : State := callS mvA (sp0 - 4800) pI 8

theorem site_mk : MakeslicePre 4096 sMk ∧ StackRoom sMk 4096 3 ∧
    LiveAt R mkA [(sMk.regs 0).toNat, (sMk.regs 1).toNat, (sMk.regs 2).toNat] [] 0x1000 (makesliceRound sMk)
      (sMk.regs 28).toNat sMk.mem (calleeStack sMk 4096 3) :=
  ⟨⟨cs_callOK _ _ _ _ 3 (by omega), ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel,
    by decide +kernel⟩, cs_room _ _ _ _ 3 (by omega), trivial, inv_cs _ _ _ _, by decide +kernel,
    fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩

theorem site_no : NewobjectPre 4096 sNo ∧ StackRoom sNo 4096 1 ∧
    LiveAt R noA [(sNo.regs 0).toNat] [] 0x1000 (newobjectRound sNo) (sNo.regs 28).toNat sNo.mem
      (calleeStack sNo 4096 1) :=
  ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel⟩,
    cs_room _ _ _ _ 1 (by omega), trivial, inv_cs _ _ _ _, by decide +kernel, fun r hr => by simp at hr,
    cs_winR _ _ _ _ 1 (by omega)⟩

theorem site_mv : Mem.EqPre 4096 3 sMv ∧
    LiveMemAt R mvA [(sMv.regs 0).toNat, (sMv.regs 1).toNat, (sMv.regs 2).toNat] [] 0x1000 sMv (calleeStack sMv 4096 3) ∧
    Mem.Input sMv 4096 3 (sMv.regs 1).toNat (sMv.regs 2).toNat ∧
    LiveDest R [] sMv 4096 3 (sMv.regs 0).toNat (sMv.regs 2).toNat :=
  ⟨⟨(guardOK_iff _ _).1 (cs_room mvA _ _ _ 3 (by omega)).1, cs_callOK _ _ _ _ 3 (by omega),
      (cs_room mvA _ _ _ 3 (by omega)).2⟩,
    ⟨trivial, inv_cs _ _ _ _, fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩,
    ⟨by decide +kernel, by decide +kernel, by
      simp only [calleeStack, outside_cons, outside_nil, and_true]; decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by simp only [calleeStack, outside_cons, outside_nil, and_true]; decide +kernel,
      Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)⟩⟩

/-- All hypotheses of `correctness` hold together, with every conjunct of its precondition: the toy runtime, an empty live
set, budget `0x1000`, and the call `Run(c, p, 96, 96)` on 96 header bytes whose base length is 1025. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64)
    (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp] s ∧
    RunArm64.Env R L s ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.ErrReqs R b len ∧
    LengthsFail (bytesAt s.mem p.toNat len.toNat) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      (MakeslicePre 4096 s_c ∧ StackRoom s_c 4096 3 ∧
        LiveAt R (Extracted.program.contractAddr "runtime.makeslice") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
          (s_c.regs 2).toNat] L b (makesliceRound s_c) (s_c.regs 28).toNat s_c.mem (calleeStack s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      (Mem.EqPre 4096 3 s_c ∧
        LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
          (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3) ∧
        Mem.Input s_c 4096 3 (s_c.regs 1).toNat (s_c.regs 2).toNat ∧
        LiveDest R L s_c 4096 3 (s_c.regs 0).toNat (s_c.regs 2).toNat)) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      (NewobjectPre 4096 s_c ∧ StackRoom s_c 4096 1 ∧
        LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(s_c.regs 0).toNat] L b (newobjectRound s_c)
          (s_c.regs 28).toNat s_c.mem (calleeStack s_c 4096 1))) :=
  ⟨implAt, R, 0x1000, [], c0, p0, 96, 96, ret, s0, hap, by rw [addr_mk]; exact model_mk, by rw [addr_mv]; exact model_mv,
    by rw [addr_no]; exact model_no, hret, setup, pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2.1, pre.2.2.2.2.2,
    ⟨[], 0x1000, sMk, by rw [addr_mk]; rfl, by rw [addr_mk]; exact site_mk⟩,
    ⟨[], 0x1000, sMv, by rw [addr_mv]; rfl, by rw [addr_mv]; exact site_mv⟩,
    ⟨[], 0x1000, sNo, by rw [addr_no]; rfl, by rw [addr_no]; exact site_no⟩⟩

end FvModexp.Arm64.Run.Witness
