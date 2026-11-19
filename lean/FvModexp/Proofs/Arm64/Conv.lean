import Extracted
import FvModexp.Proofs.Common.Conv

/-!
# Conventions for function summaries (arm64)

See `docs/history/CONVENTIONS-v2.md`. `CallEnv` is the part of every precondition that talks about the Go call
environment (stack, goroutine, read-only data, runtime-owned memory); the numbers `stk` (bytes below `SP`
the call may use: its own frame, the deeper frames, the 4096 bytes of every runtime call) and `above`
(bytes of the caller's argument/spill area above `SP` the function writes) are per function.
-/

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The stack window of a summary: `[SP - stk, SP + above)`. -/
@[reducible] def win (s : State) (stk above : Nat) : List (Nat × Nat) := [(s.sp.toNat - stk, s.sp.toNat + above)]

/-- The two parts of the window a summary may change (arm64): the window without the caller's saved frame pointer
`[SP - 8, SP)` and saved link register `[SP, SP + 8)`, which the caller reloads after the call (NOTES-divmc issue 2). Every
postcondition's `MemFrame` uses `winA`, never `win`. -/
@[reducible] def winA (s : State) (stk above : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - stk, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + above)]

/-- The extraction's read-only data lies outside the runtime-owned ranges (so that `DataLoaded` survives a call:
`FvModexp.dataLoaded_frame`). -/
def RoOut (R : RtInv) : Prop := ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt

/-- The call environment of a summary of a function that needs `stk` bytes of stack below `SP` and
writes `above` bytes above it:
* the stack-growth prologue of every frame falls through (`GuardOK s stk`), `SP` aligned, the window writable;
* the extracted read-only data is loaded;
* the window is outside the runtime-owned ranges, the goroutine's `stackguard0` slot is outside both;
* no live object lies in the window;
* the read-only data lies outside the runtime-owned ranges. -/
def CallEnv (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  GuardOK s stk ∧ StackOK s stk above ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - stk) (stk + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above) ∧ RoOut R

/-- The program of a function proof: the code of the functions `names` plus the runtime stand-in. -/
@[reducible] def prog (names : List String) (impl : List Segment) : Program :=
  (Extracted.program.onlySegments names).link impl

/-- The address of a runtime contract of the extraction. -/
@[reducible] def cA (name : String) : Nat := Extracted.program.contractAddr name

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec

/-- A read-only data object (`x`, `l` inside data object `k`) is apart from every writable range: one `Apart`
fact instead of `janus_data hd [hw]`'s one disjunction per data object (49 of them, which make `omega` slow). -/
theorem apart_of_data {m : Memory} (hd : Extracted.program.DataLoaded m) (k : Nat)
    (hk : k < Extracted.program.data.length) {x l a n : Nat}
    (hin : (Extracted.program.data[k]).base ≤ x ∧
      x + l ≤ (Extracted.program.data[k]).base + (Extracted.program.data[k]).bytes.length)
    (hw : m.accessible a n true = true) : Apart x l a n := by
  have := Janus.Tactic.disjoint_of_dataLoaded hd k hk hw
  unfold Apart; omega

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- The live set apart from the window is apart from its two `winA` parts. -/
theorem liveSep_winA {L : List (Nat × Nat)} {s : State} {stk above : Nat} (h : LiveSep L (win s stk above)) :
    LiveSep L (winA s stk above) := by
  intro r hr
  have := h r hr
  simp only [win, winA, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
  omega

/-- The runtime invariant survives a frame inside the window (which is outside `R.rt`). -/
theorem inv_frame_winA {R : RtInv} {b g : Nat} {L : List (Nat × Nat)} {s : State} {m m' : Memory} {stk above : Nat}
    (hF : MemFrame m m' (winA s stk above)) (hout : Outside (s.sp.toNat - stk) (stk + above) R.rt)
    (hsp : stk ≤ s.sp.toNat) (h8 : 8 ≤ above) (hi : R.inv b L g (view R.rt L m)) : R.inv b L g (view R.rt L m') := by
  refine RtInv.inv_frame' hF (fun r hr => ?_) hi
  simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
  left
  rcases hr with rfl | rfl
  · exact hout.of_sub (Nat.le_refl _) (by simp; omega)
  · exact hout.of_sub (by simp; omega) (by simp; omega)

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- A read-only data object (`x`, `l` inside data object `k`) is outside the runtime-owned ranges. -/
theorem RoOut.out' {R : RtInv} (h : RoOut R) (k : Nat) (hk : k < Extracted.program.data.length) {x l : Nat}
    (hin : (Extracted.program.data[k]).base ≤ x ∧
      x + l ≤ (Extracted.program.data[k]).base + (Extracted.program.data[k]).bytes.length) : Outside x l R.rt :=
  (h _ (List.getElem_mem hk)).of_sub hin.1 hin.2

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- `DataLoaded` after a call whose written ranges `ws` (besides `R.rt`) lie in a writable window `[lo, lo + n)`. -/
theorem dataLoaded_win {R : RtInv} {m0 m : Memory} {ws : List (Nat × Nat)} {lo n : Nat}
    (hd : Extracted.program.DataLoaded m0) (hreg : m.regions = m0.regions) (hro : RoOut R)
    (hf : MemFrame m0 m (R.rt ++ ws)) (hw : m0.accessible lo n true = true)
    (hws : ∀ r ∈ ws, lo ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ lo + n) : Extracted.program.DataLoaded m :=
  dataLoaded_frame hd hreg hro hf fun r hr _ => by
    obtain ⟨h1, h2, h3⟩ := hws r hr
    exact Memory.accessible_mono _ hw h1 (by omega)

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- **`memmove` keeps the read-only data loaded** (with `RoOut R`): the live contract with `DataLoaded` added to its pre-
and postcondition, for `janus_run … calls [MemmoveLive.withData hmv hro]` (the next callee's `CallEnv` needs it). -/
theorem MemmoveLive.withData {p : Program} {a d : Nat} {R : RtInv} (h : MemmoveLive p a d R) (hro : RoOut R)
    (L : List (Nat × Nat)) (b : Nat) :
    Summary p a
      (fun s => (Mem.EqPre d 3 s ∧
        LiveMemAt R a [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s d 3) ∧
        Mem.Input s d 3 (s.regs 1).toNat (s.regs 2).toNat ∧ LiveDest R L s d 3 (s.regs 0).toNat (s.regs 2).toNat) ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' => LiveMemRet R d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)] L b s s'
        (fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) ∧
        Extracted.program.DataLoaded s'.mem) := by
  refine Summary.mono (h L b).regions (fun s hs => hs.1) fun s s' hs ⟨hp, hreg⟩ => ⟨hp, ?_⟩
  obtain ⟨⟨⟨_, ⟨_, _, _, hs1, hs2, hs3, hacc⟩, _⟩, _, _, ⟨hd1, hd2, _, _⟩⟩, hd⟩ := hs
  obtain ⟨junk, f, v, m, ex, ep, rfl, hMF, -, -, -⟩ := hp
  refine dataLoaded_frame hd hreg hro (by rw [List.append_assoc] at hMF; exact hMF) fun r hr _ => ?_
  simp only [calleeStack, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by simp; omega)
  · exact Memory.accessible_mono _ hacc (by simp; omega) (by simp; omega)
  · simpa using hd2

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- `makeslice` (non-zero size) keeps the read-only data loaded. -/
theorem MakesliceLiveContract.posData {p : Program} {a st : Nat} {R : RtInv} (h : MakesliceLiveContract p a st R)
    (hro : RoOut R) (L : List (Nat × Nat)) (b : Nat) :
    Summary p a
      (fun s => ((MakeslicePre st s ∧ StackRoom s st 3 ∧
        LiveAt R a [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
          (s.regs 28).toNat s.mem (calleeStack s st 3)) ∧
        0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat) ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => LiveAllocRet R st 3 (fun ptr => [ptr]) L b (makesliceRound s) (makesliceRound s)
        s s' (fun m ptr => makesliceObj R.rt s m ptr ∧ ApartAll ptr (makesliceRound s) L) ∧
        Extracted.program.DataLoaded s'.mem) := by
  refine Summary.mono (h.pos L b).regions (fun s hs => hs.1) fun s s' hs ⟨hp, hreg⟩ => ⟨hp, ?_⟩
  obtain ⟨⟨⟨⟨⟨_, _, _, hs1, hs2, hs3, hacc⟩, _⟩, _, _⟩, _⟩, hd⟩ := hs
  obtain ⟨ptr, junk, f, v, m, ex, ep, rfl, hMF, -⟩ := hp
  refine dataLoaded_frame hd hreg hro hMF fun r hr _ => ?_
  simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by simp; omega)
  · exact Memory.accessible_mono _ hacc (by simp; omega) (by simp; omega)

/-- `newobject` (non-zero size) keeps the read-only data loaded. -/
theorem NewobjectLiveContract.posData {p : Program} {a st : Nat} {R : RtInv} (h : NewobjectLiveContract p a st R)
    (hro : RoOut R) (L : List (Nat × Nat)) (b : Nat) :
    Summary p a
      (fun s => ((NewobjectPre st s ∧ StackRoom s st 1 ∧
        LiveAt R a [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s st 1)) ∧
        0 < typSize s.mem (s.regs 0).toNat) ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => LiveAllocRet R st 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s)
        s s' (fun m ptr => newobjectObj R.rt s m ptr ∧ ApartAll ptr (newobjectRound s) L) ∧
        Extracted.program.DataLoaded s'.mem) := by
  refine Summary.mono (h.pos L b).regions (fun s hs => hs.1) fun s s' hs ⟨hp, hreg⟩ => ⟨hp, ?_⟩
  obtain ⟨⟨⟨⟨⟨_, _, _, hs1, hs2, hs3, hacc⟩, _⟩, _, _⟩, _⟩, hd⟩ := hs
  obtain ⟨ptr, junk, f, v, m, ex, ep, rfl, hMF, -⟩ := hp
  refine dataLoaded_frame hd hreg hro hMF fun r hr _ => ?_
  simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by simp; omega)
  · exact Memory.accessible_mono _ hacc (by simp; omega) (by simp; omega)

end FvModexp.Arm64
