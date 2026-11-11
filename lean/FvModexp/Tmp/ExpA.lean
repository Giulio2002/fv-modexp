import FvModexp.Proofs.Arm64.Int.IntASCall

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem expA (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State)
    (Q : State → Prop)
    (hpc : s.pc = BitVec.ofNat 64 0x1b0910) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (h0 : s.regs 0 = BitVec.ofNat 64 z) (h1 : s.regs 1 = BitVec.ofNat 64 x) (h2 : s.regs 2 = BitVec.ofNat 64 y)
    (hpre : Pre R b L z x y s) (hn : hNeg s.mem x = hNeg s.mem y) :
    ReachesRet (LibIntAS.program.link impl) (s.regs 30) s Q := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, hx, hy, hza, hz48, hzo, -⟩ := hpre'
  obtain ⟨hnx, hxa, hx48, hxo, -⟩ := hx
  obtain ⟨hny, hya, hy48, hyo, -⟩ := hy
  simp only [win, outside_cons, outside_nil, and_true] at hxo hyo hzo
  unfold Apart at hga
  have hxv : x < 2 ^ 64 := by omega
  have hyv : y < 2 ^ 64 := by omega
  have hzv : z < 2 ^ 64 := by omega
  janus_run until [0x1b2dc0, 0x1b3350]
  trace_state
  all_goals sorry

end FvModexp.Arm64.IntAS
