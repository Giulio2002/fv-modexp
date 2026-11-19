import FvModexp.Proofs.Amd64.Nat.RshDefs

/-!
# `nat.rsh` (amd64): `len x ≤ s/64` (`n ≤ 0`): `return z[:0]` (`TESTQ BX; JLE`; `XORL BX, BX`; `RET`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (liveFrame_of_memFrame inv_win)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

theorem post0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl sh : Nat} {s : State}
    (hpre : Pre R b L zp zl zc x xl sh s) (hq : xl ≤ sh / 64)
    {M' : Janus.Arm64.Memory} (hF : MemFrame s.mem M' (win s 4248 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 0) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (hfs : s'.fsBase = s.fsBase) :
    PostI R b L zp zc x xl sh s s' := by
  subst hm
  obtain ⟨⟨_, ⟨hb', _, _⟩, _, _, hout, _, _, hLs, _⟩, _, hzl, ⟨hz40, hzL, _⟩,
    ⟨_, _, _, _, hxw⟩, _, _, _, _, _, _, hinv⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hb'
  have hv : natVal s.mem x xl / 2 ^ sh = 0 := by
    apply Nat.div_eq_of_lt
    exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hfs, zp, 0, zc, h0, h1, h2, L, b, ⟨by rw [natVal_zero, hv], Or.inl rfl, Nat.zero_le _, hz40, ?_,
    fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp only [need]; omega)⟩, fun h => absurd h (by simp only [need]; omega),
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_win hF hout hb' hinv⟩, ?_, ?_⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzL hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := win s 4248 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc sh) (hsh0 : 0 < sh) (hsh : sh < 2 ^ 64) (hq : xl ≤ sh / 64)
    (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hq2 : BitVec.ofNat 64 sh >>> 6 = BitVec.ofNat 64 (sh / 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  have hs0 := ofNat_ne0 sh hsh0 hsh
  by_cases hqe : sh / 64 = xl
  · have hv : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = 0#64 := by rw [hqe]; simp
    janus64_run [hq2, hs0, hv, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post0 hpre hq ?hF _ rfl ?_ ?_ ?_ ?_⟩
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
  · have hv : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (2 ^ 64 - (sh / 64 - xl)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hm1 : (2 ^ 64 - (sh / 64 - xl)) % 18446744073709551616 = 2 ^ 64 - (sh / 64 - xl) := Nat.mod_eq_of_lt (by omega)
    have hge : (9223372036854775808 ≤ 2 ^ 64 - (sh / 64 - xl)) = True := by simp only [eq_iff_iff, iff_true]; omega
    have hne : (2 ^ 64 - (sh / 64 - xl) = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    janus64_run [hq2, hs0, hv, hm1, hge, hne, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post0 hpre hq ?hF _ rfl ?_ ?_ ?_ ?_⟩
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Rsh
