import FvModexp.Proofs.Arm64.Nat.MulMakeAD

set_option autoImplicit false

/-!
# `nat.mul` (arm64), `make_alloc`: entry → the `makeslice` CALL (`AA`), every allocating path
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc_head (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ S : State, AA s S W st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s Q := by
  obtain ⟨hce, hmw, -, -, -, ⟨⟨hxlc, hxc40, hxl12, -, hxh, -⟩, ⟨hylc, hyc40, hyl12, -, hyh, -⟩,
    ⟨hzc40, hzl, -, -, -, -⟩, -⟩, -, -, -⟩ := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hce
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  obtain ⟨-, hx48⟩ := hxh (by omega)
  obtain ⟨-, hy48⟩ := hyh (by omega)
  have hzl' : 0 < zc.toNat → zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 := fun h => (hzl h).2.2.2
  clear hzl hxh hyh hmw
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega), toInt_small yl (by omega)] until [cA "runtime.makeslice"]
  all_goals
    refine hK _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?F, ?_⟩
    case F => simp only [winA]; janus_frame
    all_goals try janus_simp
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.NatMul
