import FvModexp.Proofs.Arm64.Exp.SubMod2NGAlloc

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: `J3G` → `J4G`, the loop `for uint(len(z))*_W < n { z = append(z, 0) }`
(nat.go:1748) with the `growslice` path (agent infra)

At the test (`+0x260`) `z = (p, l, c)` (`X0..X2`): exit when `n ≤ 64 l` (then `l = ⌈n/64⌉`); otherwise `l + 1 ≤ c`
stores a zero limb at `z[l]` (`+0x258`), else `growslice(p, l + 1, c, 1, Word)` (`+0x280`, `c = l`) returns a fresh
array holding the old limbs, and the zero limb is stored there. `g` counts the growths (budget `b - g · gA n`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-- the difference the loop carries -/
@[reducible] def dD (s : State) (zp zl yp yl n : Nat) : Nat := natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n

/-- the loop invariant at the test `+0x260` -/
@[reducible] def AI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s S : State)
    (p l c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat) : Prop :=
  S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) ∧ S.regs 28 = s.regs 28 ∧ S.regs 18 = s.regs 18 ∧
    S.regs 0 = BitVec.ofNat 64 p ∧ S.regs 1 = BitVec.ofNat 64 l ∧ S.regs 2 = BitVec.ofNat 64 c ∧
    S.regs 9 = BitVec.ofNat 64 n ∧ Fw s S.mem zp zl zc yp n ∧ Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 ∧
    NatLive S.mem R L3 p c ∧ CurA R L zp zc p c ∧ c < 2 ^ 40 ∧ l ≤ c ∧ l ≤ W n ∧ g ≤ l ∧
    (W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) ∧ natVal S.mem p l = dD s zp zl yp yl n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `growslice` entry (`c = l < ⌈n/64⌉`) to the next test, with the fresh array -/
theorem gstep (impl : List Segment) {R : RtInv}
    (hgr : GrowsliceLiveContract (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {p l c g : Nat} {L3 : List (Nat × Nat)} {b3 : Nat}
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (cA "runtime.growslice"))
    (hsp : T.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : T.regs 28 = s.regs 28) (h18 : T.regs 18 = s.regs 18)
    (h0 : (T.regs 0).toNat = p) (h1 : (T.regs 1).toNat = l + 1) (h2 : (T.regs 2).toNat = c)
    (h3 : (T.regs 3).toNat = 1) (h4 : (T.regs 4).toNat = wT) (h30 : T.regs 30 = BitVec.ofNat 64 1806228)
    (hfw : Fw s T.mem zp zl zc yp n) (hrt : Rt R (b - g * gA n) L s zp zc n 3 T.mem L3 b3)
    (hlv : NatLive T.mem R L3 p c) (hcur : CurA R L zp zc p c) (hcl : c = l) (hlW : l + 1 ≤ W n) (hg : g ≤ l)
    (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) (hv : natVal T.mem p l = dD s zp zl yp yl n)
    (K : ∀ (S' : State) (p' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), S'.pc = BitVec.ofNat 64 1806192 →
      AI R b L zp zl zc yp yl n s S' p' (l + 1) c' (g + 1) L' b' → GoalG impl R b L zp zl zc yp yl n s S') :
    GoalG impl R b L zp zl zc yp yl n s T := by
  have hzW : zc < W n := Nat.lt_of_not_le fun h => by
    have := (hgz h).2.1; omega
  have hcG : costG n ≤ b := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 hzW
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have hal : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hout := hpre.1.2.2.2.1
  simp only [A] at hout
  have hround : growsliceRound T = 8 * growCap8 (l + 1) c := by simp only [growsliceRound, h1, h2]
  have hgr8 := growRoundG (N := l + 1) (c := c) (n := n) (by omega) hlW
  obtain ⟨hbr, hbud⟩ := bud_grow (r := 8 * growCap8 (l + 1) c) hcG (by omega) hrt.2.2.2.2.1 hgr8
  have hspT : T.sp.toNat = s.sp.toNat - 144 := by rw [hsp, BitVec.toNat_ofNat]; omega
  unfold GoalG
  refine ReachesRet.call_regions (hgr L3 b3) hpc
    (gcallG hpre hrt hlv hcl hlW hbr T rfl hsp h28 h0 h1 h2 h3 h4 h30) fun S1 hpc1 hpost hrg1 => ?_
  obtain ⟨ptr, junk, f1, v1, m1, ex1, ep1, hs1, hMF, hLF, ⟨hobj, hapL⟩, hapS, hinv1⟩ := hpost
  subst hs1
  rw [hround] at hapL hinv1
  simp only [growsliceObj, Fresh, h1, h2, h3] at hobj
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, hcopy, -⟩ := hobj
  simp only [calleeStack, hspT] at hMF
  rw [h28] at hinv1
  have hgcl := le_growCap8 (l + 1) c
  have hgcb := growCapG_lt (N := l + 1) (c := c) (n := n) (by omega) hlW hn15
  have hrt1 := rt_alloc (B' := b - (g + 1) * gA n) hrt hal hrg1 hMF hLF hpin hapL hbud hinv1
  have hfw1 := fw_alloc hal hout hfw hMF
  have r224 : m1.readLE (s.sp.toNat - 144 + 224) 8 = n := by
    rw [show s.sp.toNat - 144 + 224 = s.sp.toNat + 80 by omega]; exact hfw1.2.2.2.2.2.2
  have hval1 : natVal m1 ptr.toNat l = natVal T.mem p l := by
    refine natVal_copy fun i hi => ?_
    rw [← h0]; exact hcopy i (by omega)
  have hpw := fresh_win hout hpin
  have hS1 : T.regs 1 = BitVec.ofNat 64 (l + 1) := by rw [← h1, Expmc.bv_ofNat_toNat]
  have esp : (BitVec.ofNat 64 (s.sp.toNat - 144)).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_ofNat]; omega
  have hacc1 : m1.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by
    rw [hMF.accessible, hrt.2.1.accessible]; exact hpre.1.2.1.2.2.2
  obtain ⟨hal16, hb', ha', -⟩ := hpre.1.2.1
  simp only [A] at ha'
  have hcurN : CurA R L zp zc ptr.toNat (growCap8 (l + 1) c) := Or.inr ⟨hpin, fresh_of hrt.2.2.2.1 hapL⟩
  have hlvN : NatLive m1 R (L3 ++ [(ptr.toNat, ptr.toNat + 8 * growCap8 (l + 1) c)]) ptr.toNat (growCap8 (l + 1) c) :=
    fun _ => ⟨hal8 (Or.inr (by omega)), Or.inl (inRanges_snoc _ _ _), hpacc, hp48⟩
  rw [h2] at *
  janus_run [r224, hS1, esp] until [1806192]
  refine K _ ptr.toNat (growCap8 (l + 1) c) (L3 ++ [(ptr.toNat, ptr.toNat + 8 * growCap8 (l + 1) c)])
    (b3 - 8 * growCap8 (l + 1) c) ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try janus_simp
  · exact fw_fstore hfw1 (by omega) hal
  · exact rt_cstore hrt1 hcurN hlvN (by omega) (by omega)
  · exact natLive_store hlvN _ _ _
  · exact hcurN
  · exact hgcb
  · exact hgcl
  · exact hlW
  · exact hg
  · exact fun h => by omega
  · rw [natVal_store_top _ _ _ _ (by decide), hval1, hv]; simp

end FvModexp.Arm64.SubMod2N
