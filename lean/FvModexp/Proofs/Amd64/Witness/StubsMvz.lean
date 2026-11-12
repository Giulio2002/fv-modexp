import FvModexp.Proofs.Amd64.Witness.Stubs

/-! # Witness stub: `memmove(dst, src, 0)` (amd64)

Adapted from agent/asm c0f7afc (`WStubs.mvz`, amd64), stated for the local copy `Janus.Contracts.MemmoveZeroLive64` of
Janus PR #2's contract (same text; see `Amd64/MemmoveZero.lean`), with a local copy of PR #2's `liveMemRet_none64L`
(/srv/janus-mvzero Janus/Contracts/LiveAmd64.lean:455). Delete on the re-pin to a Janus release with PR #2. -/

namespace FvModexp.Amd64.WStubs

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- A call that changes only registers meets `LiveMemRet64` with an empty written range (copy of Janus PR #2
`Janus.Contracts.liveMemRet_none64L`). -/
theorem liveMemRet_none64L {R : RtInv} {d nargs b : Nat} {L : List (Nat × Nat)} {s fin : State}
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hmem : fin.mem = s.mem) (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) :
    LiveMemRet64 R d nargs [] L b s fin fun _ => True := by
  obtain ⟨junk, f, x, yh, m, zh, kr, hs⟩ := retState64_intro (res := []) hrip h4 h5 h14 hx hfs hdf hmx
    (by simp) (by simp) (by simp) hx87 hfw
  have hm : m = s.mem := by
    have := congrArg State.mem hs
    simp only [retState64] at this
    rw [← hmem]; exact this.symm ▸ rfl
  subst hm
  exact ⟨junk, f, x, yh, _, zh, kr, hs, MemFrame.refl _ _, LiveFrame.refl _ _ _, hinv, trivial⟩

set_option maxRecDepth 20000 in
/-- `memmove(dst, src, 0)` (`MemmoveZeroLive64`): the stub returns at its `n = 0` test, reading only its return
address. -/
theorem mvz (R : RtInv) : MemmoveZeroLive64 P mvA 4096 R := by
  intro L b s hpc ⟨h0, ⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hLm⟩
  have h1 : s.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  janus64_run [h1]
  refine liveMemRet_none64L ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hLm.2.1
  all_goals simp [retAddrOf, setRegF, hdf]

end FvModexp.Amd64.WStubs
