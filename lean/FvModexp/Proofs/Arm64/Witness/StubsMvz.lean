import FvModexp.Proofs.Arm64.Witness.Stubs

/-! # Witness stub: `memmove(dst, src, 0)` (arm64)

Adapted from agent/asm-mvz c0f7afc (`StubsMem.memmoveZero_sum_E0`/`memmoveZero_live_at`, `WStubs.mvz`), stated for the
local copy `Janus.Contracts.MemmoveZeroLive` of Janus PR #2's contract (same text; see `Arm64/MemmoveZero.lean`).
Delete when the Janus pin moves to a release with PR #2 and asm's `WStubs.mvz` lands in main. -/

namespace FvModexp.Arm64.Stubs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.RelocArm64 (summary_transport)

/-- A call that changes only registers meets `LiveMemRet` with an empty written range (copied from Janus PR #2
`Janus.Contracts.liveMemRet_noneL`, /srv/janus-mvzero Janus/Contracts/Live.lean:1235). -/
theorem liveMemRet_noneL {R : RtInv} {d nargs b : Nat} {L : List (Nat × Nat)} {s fin : State}
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (hmem : fin.mem = s.mem) (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) :
    LiveMemRet R d nargs [] L b s fin fun _ => True := by
  obtain ⟨junk, f, vr, m, ex, ep, hs⟩ := retStateX_intro (res := []) hpc hsp h18 h28 h29 hdz htp hfc hfs
    (fun i hi => absurd hi (by simp))
  have hm : m = s.mem := by
    have := congrArg State.mem hs
    simp only [retStateX] at this
    rw [← hmem]; exact this.symm ▸ rfl
  subst hm
  exact ⟨junk, f, vr, _, ex, ep, hs, MemFrame.refl _ _, LiveFrame.refl _ _ _, hinv, trivial⟩

/-- `MemmoveZeroLive` for the looping stub at `E0` (`n = 0`: both directions reach `ret` through `cbz x2`, no memory
access), for every runtime, request address `a` free. -/
theorem memmoveZero_sum_E0 (a : Nat) (R : RtInv) (L : List (Nat × Nat)) (b : Nat) : Summary mvProg E0
    (fun s => (s.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s ∧
      LiveMemAt R a [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3))
    (fun s s' => LiveMemRet R 4096 3 [] L b s s' fun _ => True) := by
  intro s hpc ⟨h0, ⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm⟩
  have h2 : s.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
  change ReachesRet _ _ s _
  janus_run [h2]
  all_goals exact liveMemRet_noneL rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hLm.2.1

/-- `MemmoveZeroLive` for the looping stub `mvCode` placed at `a` in `p`, every runtime `R`. -/
theorem memmoveZero_live_at (p : Program) (a : Nat) (R : RtInv) (hfit : a + 4 * 15 < 2 ^ 64)
    (hf : FetchedAt mvCode p a) : MemmoveZeroLive p a 4096 R := by
  intro L b
  refine summary_transport E0 a mvCode p _ _ (by decide) mvCode_ok (by decide) hfit hf ?_
    (fun s q ⟨h0, ⟨g, c, o⟩, h3⟩ => ⟨h0, ⟨sg_pc q g, c, o⟩, h3⟩)
    (fun s s' q h => by exact h) (memmoveZero_sum_E0 a R L b)
  intro t ht
  have : (t.regs 30).toNat < 2 ^ 48 := ht.2.1.2.1.2.1
  simp only [E0]; omega

end FvModexp.Arm64.Stubs

namespace FvModexp.Arm64.WStubs

open Janus Janus.Arm64 Janus.Contracts

/-- `memmove(dst, src, 0)` on the witness stub, any runtime. -/
theorem mvz (R : RtInv) : MemmoveZeroLive P mvA 4096 R :=
  Stubs.memmoveZero_live_at _ _ R (by decide) (fetchedAt_of_check _ _ _ (by decide +kernel))

end FvModexp.Arm64.WStubs
