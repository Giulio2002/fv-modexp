import FvModexp.Proofs.Arm64.NatQ.SqrNorm
import FvModexp.Proofs.Common.BitLemmas

/-!
# [Q-form copy of Arm64/Nat/SqrOne.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `n = 1`: `z = z.make(2); z[1], z[0] = mulWW(d, d); return z.norm()` (natmul.go:78-82)

`one_tail`: from the `norm1` loop entry (`+0x344`) with `p[0:2] = d²` to the return (`post_of` with no scratch);
`one_reuse` (`cap z ≥ 2`) and `one_alloc` (`makeslice(Word, 2, 6)`): the entry to `norm1`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem one_tail (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat}
    {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp xl xc s p c L1 b1 M) (hx1 : xl = 1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hnorm1) (r0 : S.regs 0 = BitVec.ofNat 64 p)
    (r1 : S.regs 1 = BitVec.ofNat 64 2) (r2 : S.regs 2 = BitVec.ofNat 64 c) (hsp : S.sp = s.sp - 176#64)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 184#64) (h18 : S.regs 18 = s.regs 18)
    (hF2 : MemFrame M S.mem (winA s W 64 ++ [(p, p + 16)])) (hv : natVal S.mem p 2 = natVal s.mem xp xl * natVal s.mem xp xl)
    (hr1 : S.mem.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat)
    (hr2 : S.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st xp xl xc s s' := by
  subst hx1
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpst := hJ.pst (by omega)
  have hstk := hJ.stk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF2.accessible, hJ.F.accessible]
  have hsacc : S.mem.accessible (s.sp.toNat - 184) 184 true = true := by
    rw [hacc]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hpacc' : S.mem.accessible p (8 * 2) false = true := by
    rw [hF2.accessible]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  refine norm1 impl s S.mem p c 2 (natVal s.mem xp 1 * natVal s.mem xp 1) _ (fun s' n' hF3 q0 q1 q2 hn' hv' hnn =>
    post_of hJ (MemFrame.refl _ _) hv
      (LiveExt.refl R L1) (k := 0) (Or.inr ⟨Nat.le_refl _, by
        simp only [stCap]; exact hF2.readLE _ _ (by
          simp only [winA, outside_append, outside_cons, outside_nil, and_true]; unfold Apart at hpst; omega)⟩)
      (by unfold sqrCQ; simp)
      (RtInv.inv_frame' hF2 (fun r hr => by
        simp only [winA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · left; exact hout.of_sub (by omega) (by omega)
        · left; exact hout.of_sub (by omega) (by omega)
        simp only [Nat.add_sub_cancel_left]
        rcases hph with h | h
        · exact Or.inr (h.sub (Nat.le_refl _) (by omega))
        · exact Or.inl (h.of_sub (Nat.le_refl _) (by omega))) hJ.inv)
      (stackBack_keep hstk hF2 (by
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]; unfold Apart at hpst; omega)
        (LiveExt.refl R L1))
      (hF2.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h.1.2, h.2.1⟩)
      ⟨fun a n hin ho => hF2.readLE a n (by
        have := outside_of_liveSep hin hJ.lsep
        simp only [win, winA, outside_append, outside_cons, outside_nil, and_true] at ho this ⊢
        exact ⟨⟨by omega, by omega⟩, ho.1⟩)⟩
      (hF3.mono fun a n h => by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
      q0 q1 q2 (by omega) (by rw [hv', hv]) hnn)
    hJ.cap (by omega) (by omega) hpacc' hr1 hr2 hal (by omega) (by omega) hsacc hl4 hl48 2 S (Nat.le_refl _) hpc r1 r0
    r2 hsp h28 h29 h18 rfl hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem one_reuse (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : xl.toNat = 1)
    (hz : 2 ≤ zc.toNat) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s fun s' =>
      Kept s s' ∧ SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, -, -, -, hxacc, -, hxw, hzc40, hzl, hzw, -, -, -, -, -, -, -⟩ := hpre'
  have hxw := hxw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨hz8, -, hzacc, hz48⟩ := hzl (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  have hxl1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl1
  janus_run [toInt_small zc (by omega), toInt_small (BitVec.ofNat 64 2) (by decide)] until [hnorm1]
  refine one_tail impl (core_reuse (M := s.mem) hpre (by simp; omega) (MemFrame.refl _ _)) (by simp) _ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ (by simp only [winA, List.cons_append, List.nil_append]; janus_frame) ?qV ?_ ?_ hl4 hl48
  case qV =>
    have e1 : ∀ m : Memory, natVal m zp.toNat 2 = m.readLE zp.toNat 8 + 2 ^ 64 * m.readLE (zp.toNat + 8) 8 := by
      intro m; simp only [natVal]; rw [show 8 * 2 = 8 + 8 by rfl, Memory.readLE_add]
    rw [e1]
    janus_simp
    show _ = s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8
    generalize s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8 = q
    have := Nat.mod_add_div q 18446744073709551616; omega
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem one_alloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : xl.toNat = 1)
    (hz : zc.toNat < 2) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s fun s' =>
      Kept s s' ∧ SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hsw, hsv, -, hty, -, -, -, hxacc, -, hxw, hzc40, -, -, -, -, -, -, -, hcost, hinv⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxw := hxw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hxl1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl1
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, 2, 6] := hsv.1 _ _ _ (by decide)
  have hmc : sqrCQ (1#64).toNat = allocCost (8 * 6) := by
    unfold sqrCQ makeB; simp
  replace hcost := hcost.2
  have hbl := blockSize_le_allocCost (8 * 6) true
  have hbs : blockSize (8 * 6) true ≤ b := by omega
  have hwt : Apart NatAdd.wordT 16 (s.sp.toNat - W) (W + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  janus_run [toInt_small zc (by omega), toInt_small (BitVec.ofNat 64 2) (by decide)] until [hnorm1]
    calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
  have hpw : Apart (s.sp.toNat - W) (W + 64) ptr.toNat 48 := by assumption
  unfold Apart at hpw
  have hmb : makeB (2 * (1#64).toNat) = allocCost (8 * 6) := by unfold makeB; simp
  refine one_tail impl (core_alloc (c := 6) hpre ?hF (fun a n h => by
      simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega) hLF hMF hAp hIn (by omega)
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
      (by decide) (by rw [hmb]; unfold allocCost; omega) (by simp) (by decide) (by decide) (Or.inl (by simp; omega)))
    (by simp) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [winA, List.cons_append, List.nil_append]; janus_frame) ?qV ?qR1 ?qR2
    hl4 hl48
  case hF => simp only [winA]; janus_frame
  case qV =>
    have e1 : ∀ m : Memory, natVal m ptr.toNat 2 = m.readLE ptr.toNat 8 + 2 ^ 64 * m.readLE (ptr.toNat + 8) 8 := by
      intro m; simp only [natVal]; rw [show 8 * 2 = 8 + 8 by rfl, Memory.readLE_add]
    rw [e1]
    janus_simp
    show _ = s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8
    generalize s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8 = q
    have := Nat.mod_add_div q 18446744073709551616; omega
  case qR1 =>
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hMF.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
    janus_simp
  case qR2 =>
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hMF.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
    janus_simp
  all_goals janus_simp

end FvModexp.Arm64.Q.NatSqr
