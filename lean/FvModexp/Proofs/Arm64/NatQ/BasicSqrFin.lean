import FvModexp.Proofs.Arm64.NatQ.BasicSqrVV
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# [Q-form copy of Arm64/Nat/BasicSqrFin.lean — TIGHT COSTS, divmc s34] `basicSqr` (arm64): after the loop (`i = n`, natmul.go:131-133)

`t[2n-1] = lshVU(t[1:2n-1], t[1:2n-1], 1)` (`lshVU.abi0`), `addVV(z, z, t)` (`addVV.abi0`), the deferred
`stk.restore(…)` (an indirect `CALL (R0)` of the closure `basicSqr.deferwrap1`, `Restore.sum`), the epilogue.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.Q.BasicSqr

variable {H : Nat}

abbrev callLsh : Nat := segAddr Extracted.program fn + 0x218

/-- `lshVU`'s postcondition with the frame words of the call state known -/
theorem lshQ {C : State} {m : Memory} {z n : Nat} (hz : C.mem.readLE (C.sp.toNat + 8) 8 = z)
    (hn : C.mem.readLE (C.sp.toNat + 16) 8 = n) (hx : C.mem.readLE (C.sp.toNat + 32) 8 = z)
    (hs : C.mem.readLE (C.sp.toNat + 56) 8 = 1) (h : LshVUSum.Q C m) :
    natVal m z n = (natVal C.mem z n * 2) % 2 ^ (64 * n) ∧
      m.readLE (C.sp.toNat + 64) 8 = (natVal C.mem z n * 2) / 2 ^ (64 * n) ∧
      MemFrame C.mem m [(z, z + 8 * n), (C.sp.toNat + 64, C.sp.toNat + 72)] := by
  unfold LshVUSum.Q at h
  rw [hz, hn, hx, hs, Nat.pow_one] at h
  exact h
abbrev retVV : Nat := segAddr Extracted.program fn + 0x260

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- from the `CALL lshVU.abi0` (state `C`, memory = the head's `M` with the frame stores) to the `CALL addVV.abi0` -/
theorem fin2 (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hE : Env R b H L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (M : Memory) (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat M)
    (C : State) (hpc : C.pc = BitVec.ofNat 64 callLsh) (hsp : C.sp = s.sp - 208#64) (h28 : C.regs 28 = s.regs 28)
    (h29 : C.regs 29 = s.sp - 216#64) (h18 : C.regs 18 = s.regs 18)
    (hF : MemFrame M C.mem [(s.sp.toNat - 200, s.sp.toNat - 144), (s.sp.toNat - 56, s.sp.toNat - 48)])
    (k1 : C.mem.readLE (s.sp.toNat - 208 + 8) 8 = t + 8)
    (k2 : C.mem.readLE (s.sp.toNat - 208 + 16) 8 = 2 * xl.toNat - 2)
    (k3 : C.mem.readLE (s.sp.toNat - 208 + 32) 8 = t + 8)
    (k4 : C.mem.readLE (s.sp.toNat - 208 + 56) 8 = 1)
    (k5 : C.mem.readLE (s.sp.toNat - 56) 8 = 2 * xl.toNat - 1)
    (hinvC : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 C.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) C fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b H L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hbig := hE.big
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
  have htacc : s.mem.accessible (t + 8) (8 * (2 * xl.toNat - 2)) true = true :=
    Memory.accessible_mono _ hscr.acc (by omega) (by omega)
  have htacc' := Memory.accessible_weaken _ htacc
  have htH : Held R L1 (t + 8) (8 * (2 * xl.toNat - 2)) := hscr.held.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 208 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg : Apart (t + 8) (8 * (2 * xl.toNat - 2)) ((s.regs 28).toNat + 16) 8 := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have := (hpre.starr h0).2; unfold Apart at this ⊢; have := hpre.stok.2.2.2.2.2.1; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have hrg : Apart (s.sp.toNat - 208 + 64) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have htr : Apart (t + 8) (8 * (2 * xl.toNat - 2)) (s.sp.toNat - 208 + 64) 8 := by
    unfold Apart; have := hl.tw; omega
  have hle : t + 8 ≤ t + 8 := Nat.le_refl _
  clear hpre hscr
  janus_run [k1, k2, k3, k4] until [callLsh + 4] calls [hLsh b1 L1]
  rename_i w hq hinvw _
  have e208 : (s.sp - 208#64).toNat = s.sp.toNat - 208 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨q1, q2, q3⟩ := lshQ (z := t + 8) (n := 2 * xl.toNat - 2) (by simp only [e208]; exact k1)
    (by simp only [e208]; exact k2) (by simp only [e208]; exact k3) (by simp only [e208]; exact k4) hq
  rw [e208, show s.sp.toNat - 208 + 64 = s.sp.toNat - 144 by omega] at q2 q3
  rw [show s.sp.toNat - 208 + 72 = s.sp.toNat - 136 by omega] at q3
  have htw := hl.tw; have hzw := hl.zw
  have rdw : ∀ a, (s.sp.toNat - 136 ≤ a ∧ a + 8 ≤ s.sp.toNat - 56) ∨ (s.sp.toNat - 48 ≤ a ∧ a + 8 ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → w.readLE a 8 = M.readLE a 8 := by
    intro a ha
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have w56 : w.readLE (s.sp.toNat - 56) 8 = 2 * xl.toNat - 1 := by
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact k5
  have w88 := (rdw _ (by omega)).trans m3
  have w80 := (rdw _ (by omega)).trans m4
  have w48 := (rdw _ (by omega)).trans m6
  have w16 := (rdw _ (by omega)).trans m11
  have w24 := (rdw _ (by omega)).trans m12
  have w32 := (rdw _ (by omega)).trans m13
  have hwacc : w.accessible (t + 8 * (2 * xl.toNat - 1)) 8 true = true := by
    rw [q3.accessible, hF.accessible, mfr.accessible]
    exact Memory.accessible_mono _ hE.scr.acc (by omega) (by omega)
  janus_run [w56, w88, w80, w48, w16, w24, w32, mod64_of_lt (t + 8 * (2 * xl.toNat - 1)) (by omega)] until [callVV]
  have htv := tval hE hI hF q1 q2 q3
  refine fin3 impl R hVV b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE M hI _ ?_ ?_ ?_ ?_ ?_ ?qF ?_ ?_ ?_ ?_ ?qT ?qI hl4 hl48
  case qF => janus_frame
  case qT =>
    show Memory.readLE _ _ _ = _
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [show t + (2 * xl.toNat - 1) * 8 = t + 8 * (2 * xl.toNat - 1) by omega]
    exact htv
  case qI =>
    refine RtInv.inv_frame' (ws := [(t + 8 * (2 * xl.toNat - 1), t + 8 * (2 * xl.toNat - 1) + 8),
      (s.sp.toNat - 200, s.sp.toNat - 128)]) (by janus_frame) (fun r hr => ?_) hinvw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hE.scr.held.sub (a := t + 8 * (2 * xl.toNat - 1)) (n := 8) (by omega) (by omega)
      rcases this with h | h
      · right; simpa using h
      · left; simpa using h
    · left; exact hout.of_sub (by omega) (by omega)
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem fin1 (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hE : Env R b H L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 head) (hsp : S.sp = s.sp - 208#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 216#64) (h18 : S.regs 18 = s.regs 18) (r0 : S.regs 0 = BitVec.ofNat 64 t)
    (r2 : S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat)) (r3 : S.regs 3 = xl) (r6 : S.regs 6 = xl)
    (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat S.mem) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b H L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hbig := hE.big
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
  have htacc : s.mem.accessible (t + 8) (8 * (2 * xl.toNat - 2)) true = true :=
    Memory.accessible_mono _ hscr.acc (by omega) (by omega)
  have htacc' := Memory.accessible_weaken _ htacc
  have htH : Held R L1 (t + 8) (8 * (2 * xl.toNat - 2)) := hscr.held.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 208 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg : Apart (t + 8) (8 * (2 * xl.toNat - 2)) ((s.regs 28).toNat + 16) 8 := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have := (hpre.starr h0).2; unfold Apart at this ⊢; have := hpre.stok.2.2.2.2.2.1; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have hrg : Apart (s.sp.toNat - 208 + 64) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have htr : Apart (t + 8) (8 * (2 * xl.toNat - 2)) (s.sp.toNat - 208 + 64) 8 := by
    unfold Apart; have := hl.tw; omega
  have hneg : (0#64 - (BitVec.ofNat 64 (2 * xl.toNat) - 1#64)).getLsbD 63 = true := by
    apply getLsbD63_true
    have e : (BitVec.ofNat 64 (2 * xl.toNat) - 1#64).toNat = 2 * xl.toNat - 1 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [BitVec.toNat_sub, e, BitVec.toNat_ofNat]; omega
  clear hpre hscr
  janus_run [hneg, and8_or, and8_or', m3, m4, m5, m6, toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 xl.toNat) (by simp; omega)]
    until [callLsh]
  refine fin2 impl R hLsh b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hVV hE hl4 hl48 S.mem hI _ ?_ ?_ ?_ ?_ ?_ ?F ?_ ?_ ?_ ?_ ?_ ?inv
  case F => janus_frame
  case inv =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 200, s.sp.toNat - 144), (s.sp.toNat - 56, s.sp.toNat - 48)])
      (by janus_frame) (fun r hr => ?_) minv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals janus_simp

end FvModexp.Arm64.Q.BasicSqr
