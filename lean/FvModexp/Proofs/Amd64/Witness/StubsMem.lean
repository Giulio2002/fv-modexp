import Janus.Contracts.MemSatAmd64
import Janus.Contracts.LiveSatAmd64
import Janus.Contracts.LiveCall

/-!
# `memmove` / `memclrNoHeapPointers` stubs for the live contracts (amd64), any size — generic part

Shared witness stubs (agent asm; amd64 twin of `FvModexp.Arm64.Stubs` / `Arm64/Witness/StubsMem.lean`). The stubs are
Janus's `MemSatAmd64.memmoveCode` (`REP MOVSB` forward when `dst ≤ src`, `STD; REP MOVSB; CLD` backward otherwise, so
overlapping ranges are copied correctly; any size) and `MemSatAmd64.memclrCode` (`REP STOSB`, any size). `REP MOVSB` /
`STD` are not `RelocAmd64.RelOK` (and the live contracts do not bound the return address below a stub address), so the
amd64 stubs are proved in place at their contract address (`FvModexp.Amd64.WStubs.mv`/`cl`); this file has the
extraction-free part: a copy / clear that changed memory only in `[d, d + n)` is a live return (`liveMemRet64_frame`).
-/

namespace FvModexp.Amd64.Stubs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- **A copy / clear's end is a live return** (amd64): `retState64` without result registers, memory changed only in
`[d, d + n)`, a range inside a live object or outside the runtime's ranges. -/
theorem liveMemRet64_frame {R : RtInv} {dd nargs b d n : Nat} {L : List (Nat × Nat)} {s fin : State}
    {P : Memory → Prop} (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hf : MemFrame s.mem fin.mem [(d, d + n)]) (hdst : InRanges d n L ∨ Outside d n R.rt)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (hP : P fin.mem) :
    LiveMemRet64 R dd nargs [(d, d + n)] L b s fin P := by
  obtain ⟨junk, f, x, yh, m, zh, kr, hs⟩ := retState64_intro (res := []) hrip h4 h5 h14 hx hfs hdf hmx
    (by simp) (by simp) (by simp) hx87 hfw
  have hm : fin.mem = m := by rw [hs]; rfl
  rw [hm] at hf hP
  refine ⟨junk, f, x, yh, m, zh, kr, hs, hf.widen _, ⟨fun a k _ ho => hf.readLE a k ho⟩, ?_, hP⟩
  refine RtInv.inv_frame' hf (fun r hr => ?_) hinv
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Nat.add_sub_cancel_left]
  exact hdst.symm

end FvModexp.Amd64.Stubs
