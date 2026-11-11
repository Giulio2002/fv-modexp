import FvModexp.Proofs.Arm64.Nat.RshDefs
import FvModexp.Proofs.Arm64.Nat.LshFin

/-!
# `nat.rsh` (arm64): the empty result (`0 < s`, `len x ≤ s/64`: `return z[:0]`, `+0x24c`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (liveFrame_of_memFrame)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

theorem post0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl sh : Nat} {s : State}
    (hpre : Pre R b L zp zl zc x xl sh s) (hq : xl ≤ sh / 64)
    {M' : Memory} (hF : MemFrame s.mem M' (winA s 4240 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 1 = BitVec.ofNat 64 0) (h2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    Post R b L zp zc x xl sh s s' := by
  subst hm
  obtain ⟨⟨_, ⟨_, hb', _, _⟩, _, hout, _, _, hLs, _⟩, _, hzl, ⟨hz40, hzL, _⟩,
    ⟨_, _, _, _, hxw⟩, _, _, _, _, _, _, hinv⟩ := hpre
  have hv : natVal s.mem x xl / 2 ^ sh = 0 := by
    apply Nat.div_eq_of_lt
    exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨zp, 0, zc, h0, h1, h2, L, b, ⟨by rw [natVal_zero, hv], Or.inl rfl, Nat.zero_le _, hz40, ?_,
    fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp only [need]; omega)⟩, fun h => absurd h (by simp only [need]; omega),
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_frame_winA hF hout hb' (by omega) hinv⟩, ?_, ?_⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzL hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := winA s 4240 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 sh)
    (hsh0 : 0 < sh) (hsh : sh < 2 ^ 64) (hq : xl ≤ sh / 64) (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, -⟩ := hpre'
  have hq1 := Lsh.lsr6 sh hsh
  have hq2 := Lsh.shr6 sh hsh
  have hs0 : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  by_cases hqe : sh / 64 = xl
  · have hv : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = 0#64 := by rw [hqe]; simp
    janus_run [hq1, hq2, hs0, hv]
    refine post0 hpre hq ?hF _ rfl ?_ ?_ ?_
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · have hv : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (2 ^ 64 - (sh / 64 - xl)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hle : (BitVec.ofNat 64 (2 ^ 64 - (sh / 64 - xl))).toInt ≤ (0#64).toInt := by
      rw [toInt64_cond, toInt64_cond]; simp only [BitVec.toNat_ofNat]
      rw [if_neg (by omega), if_pos (by decide)]; omega
    have hle2 : (BitVec.ofNat 64 (2 ^ 64 - (sh / 64 - xl))).toInt ≤ 0 := hle
    have hm1 : (2 ^ 64 - (sh / 64 - xl)) % 18446744073709551616 = 2 ^ 64 - (sh / 64 - xl) := Nat.mod_eq_of_lt (by omega)
    have hlt : (2 ^ 64 - (sh / 64 - xl) < 9223372036854775808) = False := by simp only [eq_iff_iff, iff_false]; omega
    janus_run [hq1, hq2, hs0, hv, hle, hle2, hm1, hlt]
    refine post0 hpre hq ?hF _ rfl ?_ ?_ ?_
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

end FvModexp.Arm64.Rsh
