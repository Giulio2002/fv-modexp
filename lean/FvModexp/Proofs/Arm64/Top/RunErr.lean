import FvModexp.Proofs.Arm64.Top.RunErrLib
import FvModexp.Proofs.Arm64.Witness.Stubs
import FvModexp.Proofs.Arm64.Witness.AsmWit

set_option autoImplicit false

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

/-- The receiver's three flags are 1; the input's base-length header is `0x0401 = 1025` (bytes 30, 31); the bump cell
holds `HEAP`; all other bytes outside the read-only data 0. -/
def f0 (a : Nat) : Byte :=
  if a = BUMP + 3 then 0x10 else if a = cR then 1 else if a = cR + 1 then 1 else if a = cR + 2 then 1
    else if a = pI + 30 then 4 else if a = pI + 31 then 1 else 0

/-- The witness bytes: the read-only data of the extraction (`AsmWit.wbytes`: `DataLoaded` is proved once, generically,
by `AsmWit.dataLoaded`), else `f0`. -/
def bytes0 (a : Nat) : Byte := AsmWit.wbytes f0 a

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

theorem dataLoaded : Extracted.program.DataLoaded s0.mem :=
  AsmWit.dataLoaded f0 [⟨sp0 - 4800, 4840, true⟩, ⟨g0, 0x100, false⟩, ⟨cR, 0x200, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv0 : R.inv 0x1000 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_live (m := mem0) (g := (s0.regs 28).toNat) (p0 := HEAP) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro r hr; simp at hr) bytes0_bump (fun i hi hi' => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  show bytes0 i = 0
  rw [show bytes0 i = f0 i from AsmWit.wbytes_high f0 (by simp only [HEAP] at hi; omega)]
  unfold f0
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
    by decide +kernel, by simp only [calleeStack, Outside]; decide +kernel⟩, cs_room _ _ _ _ 3 (by omega), trivial, inv_cs _ _ _ _, by decide +kernel,
    fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩

theorem site_no : NewobjectPre 4096 sNo ∧ StackRoom sNo 4096 1 ∧
    LiveAt R noA [(sNo.regs 0).toNat] [] 0x1000 (newobjectRound sNo) (sNo.regs 28).toNat sNo.mem
      (calleeStack sNo 4096 1) :=
  ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel,
    by simp only [calleeStack, Outside]; decide +kernel⟩,
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

/-- The returning run, exactly as `correctness` states it at the witness. -/
theorem returnsF : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (RunArm64.ErrRet s' ∧
      RunArm64.Frame R 0x1000 (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) [] s0 s') :=
  FvModexp.Arm64.Run.correctness implAt hap R (by rw [addr_mk]; exact model_mk) (by rw [addr_mv]; exact model_mv)
    (by rw [addr_no]; exact model_no) 0x1000 [] c0 p0 96 96 ret hret s0 setup pre

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
          (s_c.regs 28).toNat s_c.mem (calleeStack s_c 4096 1))) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (RunArm64.ErrRet s' ∧
        RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s') :=
  ⟨implAt, R, 0x1000, [], c0, p0, 96, 96, ret, s0, hap, by rw [addr_mk]; exact model_mk, by rw [addr_mv]; exact model_mv,
    by rw [addr_no]; exact model_no, hret, setup, pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2.1, pre.2.2.2.2.2,
    ⟨[], 0x1000, sMk, by rw [addr_mk]; rfl, by rw [addr_mk]; exact site_mk⟩,
    ⟨[], 0x1000, sMv, by rw [addr_mv]; rfl, by rw [addr_mv]; exact site_mv⟩,
    ⟨[], 0x1000, sNo, by rw [addr_no]; rfl, by rw [addr_no]; exact site_no⟩, returnsF⟩

end FvModexp.Arm64.Run.Witness
