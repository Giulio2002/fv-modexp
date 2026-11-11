import FvModexp.Proofs.Arm64.Witness.StubsGrowFin
import FvModexp.Proofs.Arm64.Top.RunIface

/-!
# Shared witness runtime for the Run extraction (arm64)

One `impl` with a stub at every contract address of the Run extraction (`build/x-Run-arm64`), and every live contract
that a row of the Run extraction can assume, proved for the toy runtime `toyR tys ok` with ANY `tys` (`TysOK`) and ANY
`ok` — so a witness picks `ok := fun _ _ => True` and gets `RunIface.Serves` for free (`serves`):

| contract | stub | theorem |
|---|---|---|
| `runtime.memmove` | `Stubs.mvCode` (looping, overlap-safe) | `mv` |
| `runtime.memclrNoHeapPointers` | `Stubs.clCode` (looping) | `cl` |
| `runtime.growslice` (8-byte `[]Word`) | `Stubs.grCode` (Go's growth + size classes) | `gr` |
| `runtime.makeslice` / `runtime.newobject` | Janus `LiveSat.makesliceCodeD` / `newobjectCodeD` | `mk` / `no` |
| `runtime.gcWriteBarrier2/4` | Janus `LiveSat.wbCode` | `wb2` / `wb4` |
| `sync.(*Pool).Get` / `Put` | Janus `PoolSat.getCode` (nil) / `putCode` (drop) | `get` / `put` |
-/

namespace FvModexp.Arm64.WStubs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.LiveSat Janus.Contracts.PoolSat
open FvModexp.Arm64.Stubs (mvCode clCode grCode FetchedAt memmove_live_at memclr_live_at growslice_live_at)

set_option maxRecDepth 100000

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def clA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def noA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wb2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
def wb4A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
def getA : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Get")
def putA : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Put")

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_cl : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = clA := by decide
theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_no : Extracted.program.contractAddr "runtime.newobject" = noA := by decide
theorem addr_wb2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wb2A := by decide
theorem addr_wb4 : Extracted.program.contractAddr "runtime.gcWriteBarrier4" = wb4A := by decide
theorem addr_get : Extracted.program.contractAddr "sync.(*Pool).Get" = getA := by decide
theorem addr_put : Extracted.program.contractAddr "sync.(*Pool).Put" = putA := by decide

/-- The witness runtime's code: one stub per contract address. -/
def impl : List Segment :=
  [{ name := "witness.memmove", base := mvA, words := mvCode },
   { name := "witness.memclr", base := clA, words := clCode },
   { name := "witness.growslice", base := grA, words := grCode },
   { name := "witness.makeslice", base := mkA, words := makesliceCodeD },
   { name := "witness.newobject", base := noA, words := newobjectCodeD },
   { name := "witness.wb2", base := wb2A, words := wbCode },
   { name := "witness.wb4", base := wb4A, words := wbCode },
   { name := "witness.poolget", base := getA, words := getCode },
   { name := "witness.poolput", base := putA, words := putCode }]

theorem hap : ImplApart Extracted.program impl := by decide +kernel

/-- The runtime program the contracts are about. -/
abbrev P : Program := Extracted.program.ofImpl impl

/-- `FetchedAt` by a decided check of every word. -/
theorem fetchedAt_of_check (ws : List Nat) (p : Program) (a : Nat)
    (h : ((List.range ws.length).all fun j => p.fetch (a + 4 * j) == ws[j]? && (p.stubAt (a + 4 * j)).isNone &&
      a + 4 * j != p.exitAddr) = true) : FetchedAt ws p a := by
  intro j w hw
  have hj : j < ws.length := (List.getElem?_eq_some_iff.mp hw).1
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at this
  exact ⟨this.1.1.trans hw, this.1.2, this.2⟩

theorem mv (R : RtInv) : MemmoveLive P mvA 4096 R :=
  memmove_live_at _ _ R (by decide) (fetchedAt_of_check _ _ _ (by decide +kernel))

theorem cl (R : RtInv) : MemclrNoHeapPointersLive P clA 4096 R :=
  memclr_live_at _ _ R (by decide) (fetchedAt_of_check _ _ _ (by decide +kernel))

theorem gr (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) : GrowsliceLiveContract P grA 4096 (toyR tys ok) :=
  growslice_live_at _ _ tys hty ok (by decide) (fetchedAt_of_check _ _ _ (by decide +kernel))

theorem mk (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MakesliceLiveContract P mkA 4096 (toyR tys ok) := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet _ _ s _
  janus_run
  exact finish_makesliceD hty pre

theorem no (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    NewobjectLiveContract P noA 4096 (toyR tys ok) := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet _ _ s _
  janus_run
  exact finish_newobjectD hty pre

theorem wb2 (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    WbLiveContract P wb2A 4096 (toyR tys ok) 2 := by
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
  janus_run
  simpa only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true] using
    wb_post hty (by decide) pre.2.2.1 pre.2.2.2.2

theorem wb4 (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    WbLiveContract P wb4A 4096 (toyR tys ok) 4 := by
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
  janus_run
  simpa only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true] using
    wb_post hty (by decide) pre.2.2.1 pre.2.2.2.2

theorem get (tys : Tys) (ok : Nat → List Nat → Prop) (T : Nat) (Sh : Pool.PoolShape) :
    Pool.PoolGetLive P getA 4096 (toyR tys ok) T Sh :=
  poolGetLive_of_run tys ok _ _ T Sh fun s hpc h30 h30' => by janus_run; exact getFinal_eq s

theorem put (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (T : Nat) (Sh : Pool.PoolShape) :
    Pool.PoolPutLive P putA 4096 (toyR tys ok) T Sh :=
  poolPutLive_of_run tys hty ok _ _ T Sh fun s hpc h30 h30' => by janus_run; rfl

/-- The witness runtime that serves every request: `Serves` holds trivially. -/
theorem serves (tys : Tys) : RunIface.Serves (toyR tys fun _ _ => True) := by
  simp only [RunIface.Serves, toyR]; exact ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial,
    fun _ _ _ _ _ _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

end FvModexp.Arm64.WStubs
