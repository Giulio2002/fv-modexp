import FvModexp.Proofs.Arm64.NatQ.SqrMakeAD

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/SqrMakeA1.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `make_alloc`: entry → the `makeslice` CALL (`AA`), every allocating path
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc_head (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ S : State, AA s S W st xp xl xc → ReachesRet (LibSqr.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s Q := by
  obtain ⟨hce, hsw, -, -, -, hxlc, hxc40, hxl12, -, hxh, -, hzc40, hzl, -, -, -, -, -, -, -, -⟩ := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, hx48⟩ := hxh (by omega)
  have hzl' : 0 < zc.toNat → zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 := fun h => (hzl h).2.2.2
  clear hzl hxh hsw
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega)] until [cA "runtime.makeslice"]
  all_goals
    refine hK _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?F, ?_⟩
    case F => simp only [winA]; janus_frame
    all_goals try janus_simp
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.Q.NatSqr
