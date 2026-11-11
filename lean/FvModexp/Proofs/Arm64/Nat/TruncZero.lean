import FvModexp.Proofs.Arm64.Nat.TruncMain

/-!
# `nat.trunc` (arm64): the empty result with an empty `z` (`cap z = 0`, `min(len x, w) = 0`; then `z = x` by the
precondition, so Go's `copy` skips `memmove`): `return z[:0]`, memory changed only in the window
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (liveFrame_of_memFrame)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Trunc

theorem post0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n : Nat} {s : State}
    (hpre : Pre R b L zp zl zc x xl n s) (hzc : zc = 0) (hk : EvenHyp.truncNeed xl n = 0)
    {M' : Memory} (hF : MemFrame s.mem M' (winA s 4208 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 1 = BitVec.ofNat 64 0) (h2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    Post R b L zp zc x xl n s s' := by
  subst hm hzc
  obtain ⟨⟨⟨_, ⟨_, hb', _, _⟩, _, hout, _, _, hLs, _⟩, _, _, _, _, _, _, _, _, hinv⟩, _, _⟩ := hpre
  have hv : natVal s.mem x xl % 2 ^ n = 0 := by
    have : xl = 0 ∨ n = 0 := by unfold EvenHyp.truncNeed at hk; omega
    rcases this with h | h
    · subst h; simp
    · subst h; simp [Nat.mod_one]
  refine ⟨zp, 0, 0, h0, h1, h2, L, b, ⟨by rw [natVal_zero, hv], Or.inl rfl, Nat.le_refl _, by decide,
    by simp [NatLive], fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩, fun h => absurd h (by omega),
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_frame_winA hF hout hb' (by omega) hinv⟩, ?_, ?_⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := winA s 4208 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 n)
    (hzc : zc = 0) (hk : EvenHyp.truncNeed xl n = 0) (hzx : zp = x) (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh2 : (BitVec.ofNat 64 n + 63#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (wOf n) := by rw [TruncMath.rot6, hsh]
  subst hzc hzx
  unfold EvenHyp.truncNeed at hk
  by_cases hx0 : xl = 0
  · subst hx0
    by_cases hn0 : n = 0
    · subst hn0
      janus_run [hsh, hsh2]
      refine post0 hpre rfl (by unfold EvenHyp.truncNeed; omega) ?hF _ rfl ?_ ?_ ?_
      case hF => simp only [winA]; janus_frame
      all_goals janus_simp
    · have hwp : 0 < wOf n := by unfold wOf; omega
      have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
      janus_run [hsh, hsh2, hwm]
      refine post0 hpre rfl (by unfold EvenHyp.truncNeed; omega) ?hF _ rfl ?_ ?_ ?_
      case hF => simp only [winA]; janus_frame
      all_goals janus_simp
  · have hn0 : n = 0 := by omega
    subst hn0
    janus_run [hsh, hsh2]
    refine post0 hpre rfl (by unfold EvenHyp.truncNeed; omega) ?hF _ rfl ?_ ?_ ?_
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

end FvModexp.Arm64.Trunc
