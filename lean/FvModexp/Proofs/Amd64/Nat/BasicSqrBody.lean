import FvModexp.Proofs.Amd64.Nat.BasicSqrStep
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (amd64): the second half of a loop iteration — the `addMulVVWW.abi0` call, `t[2i] = c`, back to the head
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.BasicSqr

/-- the `CALL addMulVVWW.abi0` of the loop body -/
abbrev callMV : Nat := segAddr Extracted.program fn + 0x287

/-- the continuation at the loop head (iteration `i`) -/
def HeadK (impl : List Amd64.Segment) (R : RtInv) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (Q : State → Prop) (i : Nat) : Prop :=
  ∀ S : State, S.rip = BitVec.ofNat 64 head → S.regs 4 = s.regs 4 - 192#64 → S.regs 5 = s.regs 4 - 8#64 →
    S.regs 14 = s.regs 14 → S.fsBase = s.fsBase → S.xmm 15 = 0#128 → S.df = false →
    S.regs 0 = BitVec.ofNat 64 i → S.regs 3 = BitVec.ofNat 64 (2 * xl.toNat) →
    S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat) → S.regs 7 = xl → S.regs 6 = xp → S.regs 8 = BitVec.ofNat 64 t →
    S.regs 9 = zl → S.regs 10 = zp →
    Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 i S.mem →
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) S Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `addMulVVWW` returned (state `S2`, memory `W`): `t[2i] = c`, back to the head -/
theorem body3 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (Q : State → Prop)
    (i : Nat) (hiy : i < xl.toNat) (hx48 : 16 * xl.toNat < 2 ^ 40) (ht48 : t + 16 * xl.toNat ≤ 2 ^ 48)
    (htb : 8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48)
    (hk : HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q (i + 1)) (W : Memory)
    (hI2 : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 (i + 1)
      (W.writeLE (t + 16 * i) 8 (W.readLE ((s.regs 4).toNat - 104) 8)))
    (w56 : W.readLE ((s.regs 4).toNat - 56) 8 = i) (w64 : W.readLE ((s.regs 4).toNat - 64) 8 = 2 * i)
    (w72 : W.readLE ((s.regs 4).toNat - 72) 8 = 16 * i) (w88 : W.readLE ((s.regs 4).toNat - 88) 8 = 2 * xl.toNat)
    (w80 : W.readLE ((s.regs 4).toNat - 80) 8 = 2 * xl.toNat) (w48 : W.readLE ((s.regs 4).toNat - 48) 8 = t)
    (w16 : W.readLE ((s.regs 4).toNat + 16) 8 = zp.toNat) (w24 : W.readLE ((s.regs 4).toNat + 24) 8 = zl.toNat)
    (w40 : W.readLE ((s.regs 4).toNat + 40) 8 = xp.toNat) (w48' : W.readLE ((s.regs 4).toNat + 48) 8 = xl.toNat)
    (wtl : W.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat)
    (hwacc2 : W.accessible (t + 16 * i) 8 true = true)
    (S2 : State) (hpc : S2.rip = BitVec.ofNat 64 (callMV + 5)) (hsp : S2.regs 4 = s.regs 4 - 192#64)
    (h5 : S2.regs 5 = s.regs 4 - 8#64) (hfs : S2.fsBase = s.fsBase) (hdf : S2.df = false) (hm : S2.mem = W) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) S2 Q := by
  have hfs8 : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  janus64_run [hm, w56, w64, w72, w88, w80, w48, w16, w24, w40, w48', wtl, hfs, hfs8,
    mod64_of_lt (t + 16 * i) (by omega)] until [head]
  have wr : ∀ a, ((s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 8) ∨
      ((s.regs 4).toNat + 16 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) →
      (W.writeLE (t + 16 * i) 8 (W.readLE ((s.regs 4).toNat - 104) 8)).readLE a 8 = W.readLE a 8 :=
    fun a ha => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  all_goals sorry

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the rest of an iteration, from the call (state `S1`, memory = the head's `M` with the two `z` words and the
frame stores): the call, `t[2i] = c`, back to the head. -/
theorem body2 (impl : List Amd64.Segment) (R : RtInv)
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) (Q : State → Prop)
    (i : Nat) (hi1 : 1 ≤ i) (hiy : i < xl.toNat) (M : Memory)
    (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 i M)
    (hk : HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q (i + 1))
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 callMV) (hsp : S1.regs 4 = s.regs 4 - 192#64)
    (h5 : S1.regs 5 = s.regs 4 - 8#64) (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = false)
    (hF : MemFrame M S1.mem [(zp.toNat + 16 * i, zp.toNat + 16 * i + 16),
      ((s.regs 4).toNat - 192, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 72, (s.regs 4).toNat - 48)])
    (hz0 : S1.mem.readLE (zp.toNat + 16 * i) 8 =
      (s.mem.readLE (xp.toNat + 8 * i) 8 * s.mem.readLE (xp.toNat + 8 * i) 8) % 2 ^ 64)
    (hz1 : S1.mem.readLE (zp.toNat + 16 * i + 8) 8 =
      s.mem.readLE (xp.toNat + 8 * i) 8 * s.mem.readLE (xp.toNat + 8 * i) 8 / 2 ^ 64)
    (f1 : S1.mem.readLE ((s.regs 4).toNat - 192) 8 = t + 8 * i)
    (f2 : S1.mem.readLE ((s.regs 4).toNat - 184) 8 = i)
    (f3 : S1.mem.readLE ((s.regs 4).toNat - 168) 8 = t + 8 * i)
    (f4 : S1.mem.readLE ((s.regs 4).toNat - 144) 8 = xp.toNat)
    (f5 : S1.mem.readLE ((s.regs 4).toNat - 120) 8 = s.mem.readLE (xp.toNat + 8 * i) 8)
    (f6 : S1.mem.readLE ((s.regs 4).toNat - 112) 8 = 0)
    (f7 : S1.mem.readLE ((s.regs 4).toNat - 56) 8 = i)
    (f8 : S1.mem.readLE ((s.regs 4).toNat - 64) 8 = 2 * i)
    (f9 : S1.mem.readLE ((s.regs 4).toNat - 72) 8 = 16 * i)
    (hinv1 : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S1.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) S1 Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hxacc := hpre.xacc; have hx48 := hpre.x48; have hadx := hpre.adx
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM
  have hacc : ∀ a n v, S1.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF.accessible, mfr.accessible]
  have htacc : S1.mem.accessible (t + 8 * i) (8 * i) true = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hscr.acc (by omega) (by omega)
  have htacc' := Janus.Arm64.Memory.accessible_weaken _ htacc
  have hxacc' : S1.mem.accessible xp.toNat (8 * i) false = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hwacc : S1.mem.accessible ((s.regs 4).toNat - 200) 104 true = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hadx' : S1.mem.accessible adxAddr 1 false = true := by rw [hacc]; exact hadx
  have hty : t + 8 * i = xp.toNat ∨ Apart (t + 8 * i) (8 * i) xp.toNat (8 * i) := by
    right; unfold Apart; have := hl.tx; omega
  have htr' : Apart (t + 8 * i) (8 * i) ((s.regs 4).toNat - 200) 104 := by unfold Apart; have := hl.tw; omega
  have htH : Held R L1 (t + 8 * i) (8 * i) := hscr.held.sub (by omega) (by omega)
  have hro : Outside ((s.regs 4).toNat - 104) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hro2 : Outside ((s.regs 4).toNat - 200) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg' : Apart (t + 8 * i) (8 * i) ((s.regs 14).toNat + 16) 8 := by unfold Apart; have := hl.gt; omega
  have htt : Apart (t + 8 * i) (8 * i) (s.fsBase.toNat - 8) 8 := by unfold Apart; have := hl.ft; omega
  have hrg : Apart ((s.regs 4).toNat - 104) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have hrt : Apart ((s.regs 4).toNat - 104) 8 (s.fsBase.toNat - 8) 8 := by unfold Apart at htw ⊢; omega
  have htaccs : s.mem.accessible (t + 8 * i) (8 * i) true = true := by rw [← hacc]; exact htacc
  have htaccs' := Janus.Arm64.Memory.accessible_weaken _ htaccs
  have hxaccs : s.mem.accessible xp.toNat (8 * i) false = true := by rw [← hacc]; exact hxacc'
  have e8 : (s.regs 4).toNat - 200 + 8 = (s.regs 4).toNat - 192 := by omega
  have e16 : (s.regs 4).toNat - 200 + 16 = (s.regs 4).toNat - 184 := by omega
  have e32 : (s.regs 4).toNat - 200 + 32 = (s.regs 4).toNat - 168 := by omega
  have e56 : (s.regs 4).toNat - 200 + 56 = (s.regs 4).toNat - 144 := by omega
  have e80 : (s.regs 4).toNat - 200 + 80 = (s.regs 4).toNat - 120 := by omega
  have e88 : (s.regs 4).toNat - 200 + 88 = (s.regs 4).toNat - 112 := by omega
  rw [← e8] at f1; rw [← e16] at f2; rw [← e32] at f3; rw [← e56] at f4; rw [← e80] at f5; rw [← e88] at f6
  clear hpre hscr hl
  janus64_run [f1, f2, f3, f4, f5, f6, hfs] until [callMV + 5] calls [hMV' b1 L1]
  rename_i w _ _ hval hFw hinvw hgd htl
  have e96 : (s.regs 4).toNat - 200 + 96 = (s.regs 4).toNat - 104 := by omega
  have e104 : (s.regs 4).toNat - 200 + 104 = (s.regs 4).toNat - 96 := by omega
  rw [e96, e104] at hFw; rw [e96] at hval
  have hxw' : natVal (S1.mem.writeLE ((s.regs 4).toNat - 200) 8 6231852) xp.toNat i = natVal S1.mem xp.toNat i :=
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by have := hE.lay.xw; omega)
  rw [hxw'] at hval
  have hFw' : MemFrame S1.mem w [(t + 8 * i, t + 8 * i + 8 * i), ((s.regs 4).toNat - 200, (s.regs 4).toNat - 192),
      ((s.regs 4).toNat - 104, (s.regs 4).toNat - 96)] :=
    MemFrame.trans (MemFrame.of_writeLE (rs := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192)]) S1.mem 6231852
      (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)) hFw fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h.2.1, h.1, h.2.2⟩
  have hinvw' := hinvw
  have htw := hE.lay.tw; have hzw := hE.lay.zw
  have rdw : ∀ a, ((s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 72) ∨
      ((s.regs 4).toNat - 48 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 8) ∨
      ((s.regs 4).toNat + 16 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → w.readLE a 8 = M.readLE a 8 := by
    intro a ha
    rw [hFw'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have rdS : ∀ a, (s.regs 4).toNat - 72 ≤ a → a + 8 ≤ (s.regs 4).toNat - 48 → w.readLE a 8 = S1.mem.readLE a 8 := by
    intro a h1 h2
    rw [hFw'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have w56 := (rdS _ (by omega) (by omega)).trans f7
  have w64 := (rdS _ (by omega) (by omega)).trans f8
  have w72 := (rdS _ (by omega) (by omega)).trans f9
  have w88 := (rdw _ (by omega)).trans m3
  have w80 := (rdw _ (by omega)).trans m4
  have w48 := (rdw _ (by omega)).trans m5
  have w16 := (rdw _ (by omega)).trans m10
  have w24 := (rdw _ (by omega)).trans m11
  have w40 := (rdw _ (by omega)).trans m13
  have w48' := (rdw _ (by omega)).trans m14
  have wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    have := hE.lay.fw; have := hE.lay.ft; have := hE.lay.fz; have := hE.lay.fs
    rw [hFw'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m19
  have hwacc2 : w.accessible (t + 16 * i) 8 true = true := by
    rw [hFw'.accessible, hacc]
    exact Janus.Arm64.Memory.accessible_mono _ hE.scr.acc (by omega) (by omega)
  have hI2 := inv_step hE hi1 hiy hI hF hz0 hz1 hFw' hval hinvw
  refine body3 impl R b L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q i hiy (by omega) ht48 htb hk w hI2
    w56 w64 w72 w88 w80 w48 w16 w24 w40 w48' wtl hwacc2 _ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals janus64_simp

end FvModexp.Amd64.BasicSqr
