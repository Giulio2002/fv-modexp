import FvModexp.Proofs.Amd64.NatQ.DivLargeShA

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeShB.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `shift ≠ 0` (natdiv.go:615), `AtS1` (`fn + 0x37c`) through `lshVU(u[:il], uIn, shift)` → `AtS2`

`XORPS X15, X15; MOVQ FS:-8, R14`; `AX = [RSP + 16] = il`, `CX = [SP' + 0x78] = C`; `CMPQ AX, CX; JA panic` (not
taken); ABI0 arguments `z = (P, il, C)`, `x = (ip, il, [RSP + 24])`, `s = [SP' + 0x80] = shift`; `CALL lshVU.abi0`
(`+0x3e1`) → return `+0x3e6` (`AtS2`; the carry in the result word `0x38(SP') = RSP - 248`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- after `lshVU(u[:il], uIn, shift)` (pure): the argument stores (`M1`, inside `[RSP - 312, RSP - 248)`) and
`lshVU`'s write set (`u[:il]` at `P`, the result word `RSP - 248`) → `MemU`, `UArr`, the values -/
theorem sh2_post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C sh : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtS1 R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S)
    {M1 w : Janus.Arm64.Memory} (hf1 : MemFrame S.mem M1 [((s.regs 4).toNat - 312, (s.regs 4).toNat - 248)])
    (hq1 : natVal w P il = natVal M1 ip il * 2 ^ sh % 2 ^ (64 * il))
    (hq2 : w.readLE ((s.regs 4).toNat - 312 + 64) 8 = natVal M1 ip il * 2 ^ sh / 2 ^ (64 * il))
    (hq3 : MemFrame M1 w [(P, P + 8 * il), ((s.regs 4).toNat - 312 + 64, (s.regs 4).toNat - 312 + 72)])
    (hinv1 : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk w)) :
    MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C sh w ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C w ∧
      natVal w t vl = natVal s.mem vp vl * 2 ^ sh ∧ 2 ^ 63 ≤ w.readLE (t + 8 * (vl - 1)) 8 ∧
      natVal w P il = natVal s.mem ip il * 2 ^ sh % 2 ^ (64 * il) ∧
      w.readLE ((s.regs 4).toNat - 248) 8 = natVal s.mem ip il * 2 ^ sh / 2 ^ (64 * il) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hU := hS.ua
  have hcap := hU.cap; have hpw := hU.pw; have hpvt := hU.pvt
  unfold Apart at hpvt
  have hLs := lsep_of hE hS.ext2
  have hLL : ∀ a n, InRanges a n L → InRanges a n Lk := fun a n h => hS.ext2.inRanges_old (hE.ext.inRanges_old h)
  have htw := hl.tw; have hiw := hl.iw
  have hF : MemFrame S.mem w (R.rt ++ [((s.regs 4).toNat - 312, (s.regs 4).toNat - 240)] ++ [(P, P + 8 * il)]) :=
    (mfTrans hf1 hq3).mono fun a n ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      refine ⟨by omega, ho.2, by omega⟩
  obtain ⟨hJ2, hUJ2⟩ := MemU.call hE hS.mem hU hF
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only; omega)
    (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega)
    ⟨fun a n hin ho => by
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at ho
      rw [hq3.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega),
        hf1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]⟩ hLL hinv1
  have hI1 : natVal M1 ip il = natVal s.mem ip il := by
    unfold natVal
    rw [hf1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hS.is _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hvt : ∀ o n, o + n ≤ 8 * vl → w.readLE (t + o) n = S.mem.readLE (t + o) n := fun o n h => by
    rw [hq3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hf1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  refine ⟨hJ2, hUJ2, ?_, ?_, by rw [hq1, hI1], by rw [show (s.regs 4).toNat - 248 = (s.regs 4).toNat - 312 + 64 by omega, hq2, hI1]⟩
  · have := hvt 0 (8 * vl) (by omega)
    simp only [Nat.add_zero] at this
    unfold natVal; rw [this]; exact hS.vval
  · rw [hvt _ _ (by omega)]; exact hS.vtop

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
theorem shB (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtS1 R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S) (Q : State → Prop)
    (k : ∀ T, AtS2 R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hil9 := hl.il9; have hvil := hl.vil
  have hi48 := hl.i48
  have hMU := hS.mem
  have hM := hMU.mem
  have m1 := hM.ilS; have m2 := hM.ipS; have m3 := hMU.sC; have m4 := hMU.sP; have m5 := hMU.ssh
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have hfs := hS.fs; have hdf := hS.df
  have hsh1 := hS.sh1; have hsh63 := hS.sh63
  have hU := hS.ua
  have hc40 := hU.c40; have hcap := hU.cap; have hp48 := hU.p48; have hpw := hU.pw
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hE.pre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg hal
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hSacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hSacc]; exact hg2
  have htacc : S.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hSacc]; exact htr
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
  have hgrd := hMU.grd
  -- `lshVU`'s precondition facts (callee `RSP = RSP - 312`; `z = P`, `x = ip`, `n = il`)
  have hLs := lsep_of hE hS.ext2
  have hzH : Held R Lk P (8 * il) := hU.pheld.sub (by omega) (by omega)
  have hzacc : S.mem.accessible P (8 * il) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hU.pacc (by omega) (by omega)
  have hxacc : S.mem.accessible ip (8 * il) false = true := by rw [hSacc]; exact hE.pre.io.2.1
  have hiw := hl.iw
  have hro : Outside ((s.regs 4).toNat - 312 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hga := hE.pre.ce.2.2.2.2.2.1
  unfold Apart at hga
  have hzg : Apart P (8 * il) ((s.regs 14).toNat + 16) 8 := by
    have h := hU.pg; unfold Apart at h ⊢; omega
  have hzt : Apart P (8 * il) (s.fsBase.toNat - 8) 8 := by
    have h := hU.pt; unfold Apart at h ⊢; omega
  have hrg : Apart ((s.regs 4).toNat - 312 + 64) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hrt : Apart ((s.regs 4).toNat - 312 + 64) 8 (s.fsBase.toNat - 8) 8 := by
    have h := htw; unfold Apart at h ⊢; omega
  have hzr : Apart P (8 * il) ((s.regs 4).toNat - 312) 72 := by unfold Apart; omega
  have hxr : Apart ip (8 * il) ((s.regs 4).toNat - 312 + 64) 8 := by unfold Apart; omega
  have halx : ip ≤ P ∨ Apart P (8 * il) ip (8 * il) := by
    rcases hU.pi with e | e
    · left; omega
    · right; unfold Apart at e ⊢; omega
  have hra : (6221062 : Nat) < 2 ^ 47 := by decide
  have hinv := hM.inv
  have hfsN : S.fsBase.toNat = s.fsBase.toNat := by rw [hfs]
  have hrt' : (s.regs 4).toNat - 312 + 64 + 8 ≤ S.fsBase.toNat - 8 ∨ S.fsBase.toNat - 8 ≤ (s.regs 4).toNat - 312 + 56 := by
    rw [hfsN]; have h := hrt; unfold Apart at h; omega
  janus64_run [m1, m2, m3, m4, m5, htS, hfs, hgrd, ite_self] until [shRet2] calls [lshvu impl hap R bk Lk]
  rename_i w _ _ hq hinv1 hgd _
  have e312 : (s.regs 4 - 312#64).toNat = (s.regs 4).toNat - 312 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  obtain ⟨q1, q2, q3⟩ := lshQ (z := P) (n := il) (x := ip) (r := sh)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)) hq
  simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e312] at q1 q2 q3
  obtain ⟨hJ2, hUJ2, hT, htop, huv, hcy⟩ := sh2_post hE hS (by janus_frame) q1 q2 q3 hinv1
  refine k _ ⟨?pc, ?sp, ?r5, ?fs, ?df, hJ2, hUJ2, hS.ext2, hS.bud2, hsh1, hsh63, hT, htop, huv, hcy, ?reg⟩
  all_goals (try janus64_simp)
  case reg =>
    rw [hrg1]; (try simp only [Janus.Arm64.Memory.regions_writeLE]); exact hS.reg
  all_goals first | exact hfs | exact hdf

end FvModexp.Amd64.Q.DivLarge
