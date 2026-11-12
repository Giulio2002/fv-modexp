import FvModexp.Proofs.Amd64.Nat.TruncDefs

/-!
# `nat.trunc` (amd64): the empty result with an empty `z` (`cap z = 0`, `min(len x, w) = 0`; then `z = x` by the
precondition, so Go's `copy` skips `memmove`): `return z[:0]`, memory changed only in the window.
`n = 0`: main path (`w = 0`), reuse, no mask, empty norm loop; `len x = 0 < w`: `set` path, reuse, `RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (liveFrame_of_memFrame inv_win)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

theorem post0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n : Nat} {s : State}
    (hpre : Pre R b L zp zl zc x xl n s) (hzc : zc = 0) (hk : EvenHyp.truncNeed xl n = 0)
    {M' : Janus.Arm64.Memory} (hF : MemFrame s.mem M' (win s 4192 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 0) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (hfs : s'.fsBase = s.fsBase) :
    PostI R b L zp zc x xl n s s' := by
  subst hm hzc
  obtain ⟨⟨⟨_, ⟨hb', _, _⟩, _, _, hout, _, _, hLs, _⟩, _, _, _, _, _, _, _, _, hinv⟩, _, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hb'
  have hv : natVal s.mem x xl % 2 ^ n = 0 := by
    have : xl = 0 ∨ n = 0 := by unfold EvenHyp.truncNeed at hk; omega
    rcases this with h | h
    · subst h; simp
    · subst h; simp [Nat.mod_one]
  refine ⟨hfs, zp, 0, 0, h0, h1, h2, L, b, ⟨by rw [natVal_zero, hv], Or.inl rfl, Nat.le_refl _, by decide,
    by simp [NatLive], fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩, fun h => absurd h (by omega),
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_win hF hout hb' hinv⟩, ?_, ?_⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := win s 4192 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc n) (hzc : zc = 0) (hk : EvenHyp.truncNeed xl n = 0) (hzx : zp = x)
    (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hwa, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh' := shr_w' n hn20
  have hxm : xl % 18446744073709551616 = xl := Nat.mod_eq_of_lt (by omega)
  subst hzc hzx
  unfold EvenHyp.truncNeed at hk
  by_cases hn0 : n = 0
  · subst hn0
    have hw0 : wOf 0 = 0 := rfl
    rw [hw0] at hsh hsh'
    have hr0' : BitVec.ofNat 64 0 &&& 63#64 = 0#64 := rfl
    janus64_run [hsh, hsh', hxm, hr0', BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post0 hpre rfl (by unfold EvenHyp.truncNeed; omega) ?hF _ rfl ?_ ?_ ?_ ?_⟩
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
  · have hx0 : xl = 0 := by omega
    subst hx0
    have hwp : 0 < wOf n := by unfold wOf; omega
    have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
    janus64_run [hsh, hsh', hwm, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post0 hpre rfl (by unfold EvenHyp.truncNeed; omega) ?hF _ rfl ?_ ?_ ?_ ?_⟩
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Trunc
