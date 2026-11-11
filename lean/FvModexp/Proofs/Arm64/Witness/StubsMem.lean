import Janus.Contracts.MemSat
import Janus.Contracts.RelocArm64
import Janus.Contracts.LiveToy
import Janus.Contracts.LiveCall

/-!
# Looping `memmove` / `memclrNoHeapPointers` stubs for the live contracts (arm64), any size

Shared witness stubs (agent top) for the non-vacuity witnesses of every row whose precondition asks the runtime to
serve copies / clears of ANY size up to a bound (`RunIface.Serves R`: `memmove`/`memclr` up to `2^20` bytes). Janus's
live stubs (`LiveStubSlice`, `LiveStubMemmoveUpto`) are straight-line code for pinned sizes; these are byte loops:

* `mvCode` = `nop` + Janus `MemSat.moveCore` (forward copy when `dst ≤ src`, backward otherwise, so overlapping ranges
  are copied correctly), `clCode` = `nop` + `MemSat.clrCore` (byte clear).
* `memmove_live_E0` / `memclr_live_E0`: the live contracts for the stub at `E0 = 2^48`, for the toy runtime with ANY
  `tys` and ANY `ok` (the stub never looks at `ok`; the runtime's invariant is preserved because the destination is
  inside a live object or outside the runtime's ranges: `LiveDest`).
* `memmove_live_at` / `memclr_live_at`: moved to any address `a` of any program that fetches the words there
  (`RelocArm64.summary_transport`, as Janus `ErrorfRealLive`).

The loops are Janus `MemSat.fwd_loop` / `bwd_loop` / `clr_loop` (adapted from Janus v0.2.0 `Janus/Contracts/MemSat.lean`)
re-proved at `E0` with the invariant the live return needs (`FPSR` kept).
-/

namespace FvModexp.Arm64.Stubs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.RelocArm64
open Janus.Contracts.MemSat (moveCore clrCore toNat_add_one toNat_sub_one byte_copy)

/-- Where the stubs are proved (above every admissible return address). -/
def E0 : Nat := 2 ^ 48

/-- The copy (`X0 = dst`, `X1 = src`, `X2 = n`): Janus `MemSat.moveCore` with the backward loop on pre-decremented
pointers (no register-offset addressing, so the code is position independent in the sense of `RelocArm64.RelOK`):
```
      cmp x0, x1
      b.hi bwd
fwd:  cbz x2, done
      ldrb w3, [x1], #1
      strb w3, [x0], #1
      sub x2, x2, #1
      b fwd
bwd:  add x1, x1, x2
      add x0, x0, x2
bwdl: cbz x2, done
      ldrb w3, [x1, #-1]!
      strb w3, [x0, #-1]!
      sub x2, x2, #1
      b bwdl
done: ret
``` -/
def mvCode : List Nat :=
  [0xeb01001f, 0x540000c8, 0xb4000182, 0x38401423, 0x38001403, 0xd1000442, 0x17fffffc,
   0x8b020021, 0x8b020000, 0xb40000a2, 0x385ffc23, 0x381ffc03, 0xd1000442, 0x17fffffc, 0xd65f03c0]
/-- The clear (`X0 = p`, `X1 = n`): Janus `MemSat.clrCore` (`cbz x1, done; strb wzr, [x0], #1; sub x1, x1, #1; b`). -/
def clCode : List Nat := clrCore

abbrev mvProg : Program := codeProg E0 mvCode
abbrev clProg : Program := codeProg E0 clCode

abbrev FWD : Nat := E0 + 8
abbrev BWD : Nat := E0 + 36
abbrev CLH : Nat := E0

/-- What a byte loop keeps, from the entry state `s` to `T`. -/
def Kp (s T : State) : Prop :=
  T.sp = s.sp ∧ T.regs 18 = s.regs 18 ∧ T.regs 28 = s.regs 28 ∧ T.regs 29 = s.regs 29 ∧ T.regs 30 = s.regs 30 ∧
    T.dczid = s.dczid ∧ T.tpidr = s.tpidr ∧ T.fpcr = s.fpcr ∧ T.fpsr = s.fpsr

/-- The end of a copy / clear of `[d, d + n)` started at `s`. -/
def Done (s : State) (d n : Nat) (P : Memory → Prop) (T : State) : Prop :=
  T.pc = s.regs 30 ∧ Kp s T ∧ MemFrame s.mem T.mem [(d, d + n)] ∧ P T.mem

theorem fwd_loop (s : State) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) (hsrc : s.mem.accessible (s.regs 1).toNat (s.regs 2).toNat false = true)
    (hdst : s.mem.accessible (s.regs 0).toNat (s.regs 2).toNat true = true)
    (hle : (s.regs 0).toNat ≤ (s.regs 1).toNat) :
    ∀ k (T : State) (i : Nat), i + k = (s.regs 2).toNat → T.pc = BitVec.ofNat 64 FWD →
      (T.regs 0).toNat = (s.regs 0).toNat + i → (T.regs 1).toNat = (s.regs 1).toNat + i →
      (T.regs 2).toNat = k → Kp s T →
      MemFrame s.mem T.mem [((s.regs 0).toNat, (s.regs 0).toNat + i)] →
      Mem.Copied s.mem T.mem (s.regs 0).toNat (s.regs 1).toNat i →
      ReachesRet mvProg (s.regs 30) T
        (Done s (s.regs 0).toNat (s.regs 2).toNat fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) := by
  have hbs := Memory.accessible_bound _ hsrc
  have hbd := Memory.accessible_bound _ hdst
  intro k
  induction k with
  | zero =>
    intro T i hi hpc h0 h1 h2 ⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩ hf hc
    have h2' : T.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    rw [← h30]
    have h30b' : (T.regs 30).toNat < 2 ^ 48 := by rw [h30]; exact h30b
    have h30a' : (T.regs 30).toNat % 4 = 0 := by rw [h30]; exact h30a
    janus_run
    refine ⟨rfl, (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]), ?_, ?_⟩
    · rw [← hi, Nat.add_zero]; exact hf
    · rw [← hi, Nat.add_zero]; exact hc
  | succ k ih =>
    intro T i hi hpc h0 h1 h2 ⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩ hf hc
    have h2' : T.regs 2 ≠ 0#64 := fun h => by simp [h] at h2
    have hr : T.mem.accessible (T.regs 1).toNat 1 false = true := by
      rw [hf.accessible, h1]; exact Memory.accessible_mono _ hsrc (by omega) (by omega)
    have hw : T.mem.accessible (T.regs 0).toNat 1 true = true := by
      rw [hf.accessible, h0]; exact Memory.accessible_mono _ hdst (by omega) (by omega)
    janus_run until [FWD]
    have e0 : (T.regs 0 + 1#64).toNat = (s.regs 0).toNat + (i + 1) := by
      rw [toNat_add_one (by omega), h0]; omega
    have e1 : (T.regs 1 + 1#64).toNat = (s.regs 1).toNat + (i + 1) := by
      rw [toNat_add_one (by omega), h1]; omega
    refine ih _ (i + 1) (by omega) rfl (by simpa [setReg] using e0) (by simpa [setReg] using e1)
      (by simpa [setReg] using toNat_sub_one h2)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]) ?_ ?_
    · rw [h0]
      refine (hf.mono fun a n h => ?_).writeLE _ (List.mem_singleton_self _) (by simp <;> omega) (by simp <;> omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj
      rw [h0, h1]
      by_cases hji : j = i
      · subst hji; rw [Memory.bytes_writeLE_inside _ (by omega) (by omega)]; exact byte_copy _ _
      · rw [Memory.bytes_writeLE_outside _ (by omega)]; exact hc j (by omega)

theorem bwd_loop (s : State) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hsrc : s.mem.accessible (s.regs 1).toNat (s.regs 2).toNat false = true)
    (hdst : s.mem.accessible (s.regs 0).toNat (s.regs 2).toNat true = true)
    (hlt : (s.regs 1).toNat < (s.regs 0).toNat) :
    ∀ k (T : State), k ≤ (s.regs 2).toNat → T.pc = BitVec.ofNat 64 BWD →
      (T.regs 0).toNat = (s.regs 0).toNat + k → (T.regs 1).toNat = (s.regs 1).toNat + k → (T.regs 2).toNat = k →
      Kp s T →
      MemFrame s.mem T.mem [((s.regs 0).toNat + k, (s.regs 0).toNat + (s.regs 2).toNat)] →
      (∀ j, k ≤ j → j < (s.regs 2).toNat → T.mem.bytes ((s.regs 0).toNat + j) = s.mem.bytes ((s.regs 1).toNat + j)) →
      ReachesRet mvProg (s.regs 30) T
        (Done s (s.regs 0).toNat (s.regs 2).toNat fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) := by
  have hbs := Memory.accessible_bound _ hsrc
  have hbd := Memory.accessible_bound _ hdst
  intro k
  induction k with
  | zero =>
    intro T hk hpc h0 h1 h2 ⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩ hf hc
    have h2' : T.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    rw [← h30]
    have h30b' : (T.regs 30).toNat < 2 ^ 48 := by rw [h30]; exact h30b
    have h30a' : (T.regs 30).toNat % 4 = 0 := by rw [h30]; exact h30a
    janus_run
    refine ⟨rfl, (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]), ?_, ?_⟩
    · simpa using hf
    · intro j hj; exact hc j (Nat.zero_le _) hj
  | succ k ih =>
    intro T hk hpc h0 h1 h2 ⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩ hf hc
    have h2' : T.regs 2 ≠ 0#64 := fun h => by simp [h] at h2
    have e2 := toNat_sub_one h2
    have ea : (T.regs 1 - 1#64).toNat = (s.regs 1).toNat + k := toNat_sub_one (by omega)
    have eb : (T.regs 0 - 1#64).toNat = (s.regs 0).toNat + k := toNat_sub_one (by omega)
    have hr : T.mem.accessible (T.regs 1 - 1#64).toNat 1 false = true := by
      rw [hf.accessible, ea]; exact Memory.accessible_mono _ hsrc (by omega) (by omega)
    have hw : T.mem.accessible (T.regs 0 - 1#64).toNat 1 true = true := by
      rw [hf.accessible, eb]; exact Memory.accessible_mono _ hdst (by omega) (by omega)
    janus_run until [BWD]
    refine ih _ (by omega) rfl (by simpa [setReg] using eb) (by simpa [setReg] using ea)
      (by simpa [setReg] using e2)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]) ?_ ?_
    · refine (hf.mono fun a n h => ?_).writeLE _ (List.mem_singleton_self _) (by simp <;> omega) (by simp <;> omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj1 hj2
      by_cases hji : j = k
      · subst hji; rw [Memory.bytes_writeLE_inside _ (by omega) (by omega),
          show (T.regs 1).toNat - 1 = (s.regs 1).toNat + j by omega,
          show (s.regs 0).toNat + j = (T.regs 0).toNat - 1 by omega]
        exact byte_copy _ _
      · rw [Memory.bytes_writeLE_outside _ (by omega)]; exact hc j (by omega) hj2

theorem clr_loop (s : State) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) (hacc : s.mem.accessible (s.regs 0).toNat (s.regs 1).toNat true = true) :
    ∀ k (T : State) (i : Nat), i + k = (s.regs 1).toNat → T.pc = BitVec.ofNat 64 CLH →
      (T.regs 0).toNat = (s.regs 0).toNat + i → (T.regs 1).toNat = k → Kp s T →
      MemFrame s.mem T.mem [((s.regs 0).toNat, (s.regs 0).toNat + i)] →
      Mem.Zeroed T.mem (s.regs 0).toNat i →
      ReachesRet clProg (s.regs 30) T
        (Done s (s.regs 0).toNat (s.regs 1).toNat fun m => Mem.Zeroed m (s.regs 0).toNat (s.regs 1).toNat) := by
  have hb := Memory.accessible_bound _ hacc
  intro k
  induction k with
  | zero =>
    intro T i hi hpc h0 h1 ⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩ hf hz
    have h1' : T.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    rw [← h30]
    have h30b' : (T.regs 30).toNat < 2 ^ 48 := by rw [h30]; exact h30b
    have h30a' : (T.regs 30).toNat % 4 = 0 := by rw [h30]; exact h30a
    janus_run
    refine ⟨rfl, (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]), ?_, ?_⟩
    · rw [← hi, Nat.add_zero]; exact hf
    · rw [← hi, Nat.add_zero]; exact hz
  | succ k ih =>
    intro T i hi hpc h0 h1 ⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩ hf hz
    have h1' : T.regs 1 ≠ 0#64 := fun h => by simp [h] at h1
    have hw : T.mem.accessible (T.regs 0).toNat 1 true = true := by
      rw [hf.accessible, h0]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
    janus_run until [CLH]
    have e0 : (T.regs 0 + 1#64).toNat = (s.regs 0).toNat + (i + 1) := by
      rw [toNat_add_one (by omega), h0]; omega
    refine ih _ (i + 1) (by omega) rfl (by simpa [setReg] using e0) (by simpa [setReg] using toNat_sub_one h1)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]) ?_ ?_
    · rw [h0]
      refine (hf.mono fun a n h => ?_).writeLE 0 (List.mem_singleton_self _) (by simp <;> omega) (by simp <;> omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj
      rw [h0]
      by_cases hji : j = i
      · subst hji; rw [Memory.bytes_writeLE_inside _ (by omega) (by omega), Nat.zero_div]; rfl
      · rw [Memory.bytes_writeLE_outside _ (by omega)]; exact hz j (by omega)

/-- A loop's end is a live return (no result registers): memory changed only in `[d, d + n)`, a range inside a live
object or outside the runtime's ranges. -/
theorem liveMemRet_done {R : RtInv} {dd nargs b d n : Nat} {L : List (Nat × Nat)} {s T : State} {P : Memory → Prop}
    (h : Done s d n P T) (hdst : InRanges d n L ∨ Outside d n R.rt)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) :
    LiveMemRet R dd nargs [(d, d + n)] L b s T P := by
  obtain ⟨hpc, ⟨hsp, h18, h28, h29, -, hdz, htp, hfc, hfs⟩, hf, hP⟩ := h
  obtain ⟨junk, f, vr, m, ex, ep, hs⟩ := retStateX_intro (res := []) hpc hsp h18 h28 h29 hdz htp hfc hfs
    (fun i hi => absurd hi (by simp))
  have hm : T.mem = m := by rw [hs]; rfl
  rw [hm] at hf hP
  refine ⟨junk, f, vr, m, ex, ep, hs, hf.widen _, ⟨fun a k _ ho => hf.readLE a k ho⟩, ?_, hP⟩
  refine RtInv.inv_frame' hf (fun r hr => ?_) hinv
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Nat.add_sub_cancel_left]
  exact hdst.symm

/-- The tuple of kept fields after straight-line steps that do not touch them. -/
macro "kp_tac" : tactic =>
  `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption | simp [setReg, *]))

/-- **`MemmoveLive` for the looping stub at `E0`**, for every runtime (the stub never reads `R`), with the request
address `a` of `R.ok` free (the stub is moved to `a` by `memmove_live_at`). -/
theorem memmove_sum_E0 (a : Nat) (R : RtInv) (L : List (Nat × Nat)) (b : Nat) : Summary mvProg E0
    (fun s => Mem.EqPre 4096 3 s ∧
      LiveMemAt R a [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
      Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
      LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat)
    (fun s s' => LiveMemRet R 4096 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)] L b s s'
      fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) := by
  intro s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  change ReachesRet _ _ s _
  janus_run until [FWD, BWD]
  · refine Janus.Contracts.MemSat.ReachesRet.weaken ?_ rfl fun T h => liveMemRet_done h hd4 hLm.2.1
    exact bwd_loop s h30a h30b hs2 hd2 (by omega) _ _ (Nat.le_refl _) rfl
      (by simp [setReg, BitVec.toNat_add]; omega) (by simp [setReg, BitVec.toNat_add]; omega) (by simp [setReg]) (by kp_tac)
      (MemFrame.refl _ _) (fun j h1 h2 => absurd h2 (by omega))
  · refine Janus.Contracts.MemSat.ReachesRet.weaken ?_ rfl fun T h => liveMemRet_done h hd4 hLm.2.1
    exact fwd_loop s h30a h30b hs2 hd2 (by omega) _ _ 0 (by simp) rfl (by simp) (by simp) rfl (by kp_tac)
      (MemFrame.refl _ _) (fun j hj => absurd hj (Nat.not_lt_zero _))

/-- **`MemclrNoHeapPointersLive` for the looping stub at `E0`**, for every runtime, request address `a` free. -/
theorem memclr_sum_E0 (a : Nat) (R : RtInv) (L : List (Nat × Nat)) (b : Nat) : Summary clProg E0
    (fun s => Mem.EqPre 4096 2 s ∧
      LiveMemAt R a [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s 4096 2) ∧
      LiveDest R L s 4096 2 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveMemRet R 4096 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 0).toNat (s.regs 1).toNat) := by
  intro s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  change ReachesRet _ _ s _
  refine Janus.Contracts.MemSat.ReachesRet.weaken ?_ rfl fun T h => liveMemRet_done h hd4 hLm.2.1
  exact clr_loop s h30a h30b hd2 _ _ 0 (by simp) hpc (by simp) rfl (by kp_tac)
    (MemFrame.refl _ _) (fun j hj => absurd hj (Nat.not_lt_zero _))

/-! ## At any address of any program -/

/-- The program `p` fetches the words `ws` at `a` (not a stub, not the exit address). -/
def FetchedAt (ws : List Nat) (p : Program) (a : Nat) : Prop :=
  ∀ j w, ws[j]? = some w → p.fetch (a + 4 * j) = some w ∧ p.stubAt (a + 4 * j) = none ∧ a + 4 * j ≠ p.exitAddr

theorem mvCode_ok : CodeOK E0 mvCode = true := by decide +kernel
theorem clCode_ok : CodeOK E0 clCode = true := by decide +kernel

theorem sg_pc {s : State} {d : Nat} (q : BitVec 64) (h : GoABI.StackGuardOK s d) :
    GoABI.StackGuardOK { s with pc := q } d := by
  cases h; constructor <;> assumption

/-- **`MemmoveLive` for the looping stub `mvCode` placed at `a` in `p`**, every runtime `R`. -/
theorem memmove_live_at (p : Program) (a : Nat) (R : RtInv) (hfit : a + 4 * 15 < 2 ^ 64)
    (hf : FetchedAt mvCode p a) : MemmoveLive p a 4096 R := by
  intro L b
  refine summary_transport E0 a mvCode p _ _ (by decide) mvCode_ok (by decide) hfit hf ?_ (fun s q ⟨⟨g, c, o⟩, h2, h3, h4⟩ => ⟨⟨sg_pc q g, c, o⟩, h2, h3, h4⟩)
    (fun s s' q h => by exact h) (memmove_sum_E0 a R L b)
  intro t ht
  have : (t.regs 30).toNat < 2 ^ 48 := ht.1.2.1.2.1
  simp only [E0]; omega

/-- **`MemclrNoHeapPointersLive` for the looping stub `clCode` placed at `a` in `p`**, every runtime `R`. -/
theorem memclr_live_at (p : Program) (a : Nat) (R : RtInv) (hfit : a + 4 * 5 < 2 ^ 64)
    (hf : FetchedAt clCode p a) : MemclrNoHeapPointersLive p a 4096 R := by
  intro L b
  refine summary_transport E0 a clCode p _ _ (by decide) clCode_ok (by decide) hfit hf ?_
    (fun s q ⟨⟨g, c, o⟩, h2, h3⟩ => ⟨⟨sg_pc q g, c, o⟩, h2, h3⟩)
    (fun s s' q h => by exact h) (memclr_sum_E0 a R L b)
  intro t ht
  have : (t.regs 30).toNat < 2 ^ 48 := ht.1.2.1.2.1
  simp only [E0]; omega

end FvModexp.Arm64.Stubs
