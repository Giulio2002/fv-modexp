import FvModexp.Proofs.Arm64.NatQ.MulMakeAD

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/MulMakeA1.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), `make_alloc`: entry → the `makeslice` CALL (`AA`), every allocating path
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the 4 paths' join `0x1baf0c` (`R2 = z`, the old capacity or `0` after an alias) → the `makeslice` CALL (`AA`) -/
theorem alloc_join (impl : List Segment) (W : Nat) (st xp xl xc yp yl yc : BitVec 64) (s : State) (Q : State → Prop)
    (hK : ∀ S : State, AA s S W st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (s.regs 30) S Q)
    (hW : 4608 ≤ W) (hb' : W ≤ s.sp.toNat) (hal : s.sp.toNat % 16 = 0) (ha : s.sp.toNat + 88 ≤ 2 ^ 48)
    (hxl12 : xl.toNat ≤ 2 ^ 12) (hyl12 : yl.toNat ≤ 2 ^ 12)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 0x1baf0c) (hsp : T.sp = s.sp - 256#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 264#64) (h18 : T.regs 18 = s.regs 18)
    (r2 : (T.regs 2).toNat < xl.toNat + yl.toNat) (r3 : T.regs 3 = st) (r4 : T.regs 4 = xp) (r5 : T.regs 5 = xl) (r6 : T.regs 6 = xc)
    (r7 : T.regs 7 = yp) (r8 : T.regs 8 = yl) (r9 : T.regs 9 = yc)
    (hF : MemFrame s.mem T.mem (winA s W 88)) (hreg : T.mem.regions = s.mem.regions)
    (hacc : T.mem.accessible (s.sp.toNat - W) (W + 88) true = true)
    (mlr : T.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (mfp : T.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) T Q := by
  janus_run [toInt_small (T.regs 2) (by omega), toInt_small xl (by omega), toInt_small yl (by omega)] until [cA "runtime.makeslice"]
  refine hK _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?F, ?_⟩
  case F => simp only [winA] at hF ⊢; janus_frame
  all_goals try janus_simp
  all_goals first | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc_head (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
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
  have hacc0 := hw
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega), toInt_small yl (by omega)] until [0x1baf0c]
  all_goals
    refine alloc_join impl W st xp xl xc yp yl yc s Q hK hW hb' hal ha (by omega) (by omega) _ ?_ ?_ ?_ ?_ ?_
      ?r2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?F ?_ ?acc ?_ ?_
    case F => simp only [winA]; janus_frame
    case acc => janus_simp; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
    case r2 => janus_simp; omega
    all_goals try janus_simp
    all_goals try omega

end FvModexp.Arm64.Q.NatMul
