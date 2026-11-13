import FvModexp.Proofs.Amd64.NatQ.DivOneRel
import FvModexp.Proofs.Amd64.NatQ.DivMBase

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u` (`(*Int).Mod`'s call), `len v = 1`: entry → `CALL nat.divW` → `AtV` (top s39)

Twin of Arm64/NatQ/DivMOneA.lean's `one1G` part: `one1M` = `one1G` (DivZOneA) from `PFM` (the prologue reads only the
call environment, the stack arguments and `v`'s facts).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `nat.divW`'s entry (`len v = 1`), from `PFM` (`(*Int).Mod`'s call, possibly empty dividend) -/
theorem one1M (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vc : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = z2)
    (h8 : s.regs 8 = z2l) (h9 : s.regs 9 = z2c)
    (hp : PFM R b dc L u ul uc v 1 vc s)
    (Q : State → Prop)
    (k : ∀ X : State, AtV zp.toNat zl.toNat zc.toNat z2.toNat z2c.toNat u ul uc v s X →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have r1 := hp.su; have r2 := hp.sul; have r3 := hp.suc; have r4 := hp.sv; have r5 := hp.svl; have r6 := hp.svc
  obtain ⟨-, hvacc, hv48, -, hvw⟩ := hp.vo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  clear hp
  janus64_run [r1, r2, r3, r4, r5, r6] until [divWE]
  refine k _
    { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, a0 := ?_, a3 := ?_, a1 := ?_,
      a7 := ?_, a6 := ?_, a8 := ?_, a9 := ?_, rc := ?_, mf := ?qF, reg := ?qR, bp := ?_, s5 := ?_, s7 := ?_ }
  case qF => unfold proW; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals first | exact hx15 | exact hdf | (janus64_simp; omega) | rfl

end FvModexp.Amd64.Q.NatDiv
