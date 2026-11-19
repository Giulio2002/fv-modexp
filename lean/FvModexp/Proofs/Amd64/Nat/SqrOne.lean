import FvModexp.Proofs.Amd64.Nat.SqrNorm
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.sqr` (amd64), `n = 1`: `z = z.make(2); z[1], z[0] = mulWW(d, d); return z.norm()` (natmul.go:78-82)

`one_tail`: from the `norm1` loop entry (`0x5f13ae`, `AX = 2`, `BX = p`, `CX = cap`) with `p[0:2] = d²` to the return
(`post_of` with no scratch); `one_reuse` (`cap z ≥ 2`, `CMPQ CX, $2; JGE 0x5f106f`): the entry to `norm1`. The
`makeslice(Word, 2, 6)` path is `SqrOneA.one_alloc`. Twin of the arm64 module.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem one_tail (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat}
    {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hx1 : xl = 1)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hnorm1) (r0 : S.regs 0 = BitVec.ofNat 64 2)
    (r3 : S.regs 3 = BitVec.ofNat 64 p) (r1 : S.regs 1 = BitVec.ofNat 64 c) (hsp : S.regs 4 = s.regs 4 - 168#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hx15 : S.xmm 15 = s.xmm 15)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df)
    (hF2 : MemFrame M S.mem (win s W 64 ++ [(p, p + 16)])) (hv : natVal S.mem p 2 = natVal s.mem xp xl * natVal s.mem xp xl)
    (hr1 : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ SPost R b L W zp zc st xp xl xc s s' := by
  subst hx1
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, -, -⟩ := hce
  simp only [regSP] at hb' ha hw
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpst := hJ.pst (by omega)
  have hstk := hJ.stk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF2.accessible, hJ.F.accessible]
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 168) 176 true = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hpacc' : S.mem.accessible p (8 * 2) false = true := by
    rw [hF2.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  refine norm1 impl s S.mem p c 2 (natVal s.mem xp 1 * natVal s.mem xp 1) _
    (fun s' n' hF3 q0 q1 q2 qfs qdf hn' hv' hnn =>
    post_of hJ (MemFrame.refl _ _) hv
      (LiveExt.refl R L1) (k := 0) (Nat.le_refl _) (by unfold sqrC; simp)
      (RtInv.inv_frame' hF2 (fun r hr => by
        simp only [win, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · left; exact hout.of_sub (by omega) (by omega)
        simp only [Nat.add_sub_cancel_left]
        rcases hph with h | h
        · exact Or.inr (h.sub (Nat.le_refl _) (by omega))
        · exact Or.inl (h.of_sub (Nat.le_refl _) (by omega))) hJ.inv)
      (stackBack_keep hstk hF2 (by
        simp only [win, outside_append, outside_cons, outside_nil, and_true]; unfold Apart at hpst; omega)
        (LiveExt.refl R L1))
      (hF2.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h.1.2, h.2.1⟩)
      ⟨fun a n hin ho => hF2.readLE a n (by
        have := outside_of_liveSep hin hJ.lsep
        simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho this ⊢
        exact ⟨this, ho.1⟩)⟩
      (hF3.mono fun a n h => by simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega)
      qfs qdf q0 q1 q2 (by omega) (by rw [hv', hv]) hnn)
    hJ.cap (by omega) (by omega) hpacc' hr1 hr2 hal (by omega) (by omega) hsacc hra 2 S (Nat.le_refl _) hpc r0 r3
    r1 hsp h14 h5 hx15 hfs hdf rfl hv

theorem natVal_two (m : Memory) (p : Nat) : natVal m p 2 = m.readLE p 8 + 2 ^ 64 * m.readLE (p + 8) 8 := by
  simp only [natVal]; rw [show 8 * 2 = 8 + 8 by rfl, Janus.Arm64.Memory.readLE_add]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem one_reuse (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0fe0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : xl.toNat = 1)
    (hz : 2 ≤ zc.toNat) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) s fun s' =>
      Kept s s' ∧ SPost R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, -, -, -, hxacc, -, hxw, hzc40, hzl, hzw, -, -, -, -, -, -, -⟩ := hpre'
  have hxw := hxw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨hz8, -, hzacc, hz48⟩ := hzl (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  have hxl1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl1
  janus64_run [BitVec.msb_eq_decide, toInt_small zc (by omega)] until [hnorm1]
  refine one_tail impl (core_reuse (M := s.mem) hpre (by simp; omega) (MemFrame.refl _ _)) (by simp) _ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [win, List.cons_append, List.nil_append]; janus_frame) ?qV ?_ ?_ hra
  case qV =>
    rw [natVal_two]
    janus64_simp
    show _ = s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8
    generalize s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8 = q
    have := Nat.mod_add_div q 18446744073709551616; omega
  all_goals janus64_simp

end FvModexp.Amd64.NatSqr
