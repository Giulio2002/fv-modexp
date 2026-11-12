import FvModexp.Proofs.Arm64.Nat.DrsFin

/-!
# `divRecursiveStep` (arm64): entry → after `u = u.norm(); v = v.norm()` (composition, no execution of its own)

`entry`: `pro0` → `norm1` (`u.norm()`) → `pro1` → `norm2` (`v.norm()`, which keeps `n = len v` since the top word is
`≥ 2^63`: `norm_v`) → `AtE2` with the normalised `len u = ul' ≤ ul` (`U` unchanged, `NatNorm`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW)

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → `AtE2` -/
theorem entry (impl : List Segment) (R : RtInv) (a : Args) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1ba3a0)
    (hE : Entry a s) {c : Nat} (hpre : DrsPreW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat
      a.ul.toNat a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat s) (hW : 30608 ≤ a.W) (Q : State → Prop)
    (k : ∀ (P : State) (ul' : Nat), AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat
      a.vp.toNat a.vl.toNat a.vc.toNat a.d.toNat → ul' ≤ a.ul.toNat →
      natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat → NatNorm s.mem a.up.toNat ul' →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) s Q := by
  obtain ⟨hce, -, hgl, -, -, hul, huc, hvlc, hvc, hv2, -, htop, -, -, -, ⟨hua, hu48, -, huo, -⟩,
    ⟨hva, hv48, -, hvo, -⟩, -, -, -, ⟨⟨-, -, hsta, hst48, -⟩, hsto, -⟩, -⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hce'
  obtain ⟨-, -, -, h40, -, -, -, hgacc, -, hgw, -⟩ := hgl
  replace h40 : s.mem.readLE 7147136 8 = 40 := h40
  replace hgacc : s.mem.accessible 7147136 32 false = true := hgacc
  replace hgw : Outside 7147136 32 (win s a.W 96) := hgw
  obtain ⟨h30a, h30b, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
  simp only [win, outside_cons, outside_nil, and_true] at huo hvo hsto hgw
  refine pro0 impl s a.W hpc hce (by omega) Q fun P hpc0 hF hR hs1 hs2 hs3 hd hb => ?_
  have hPm : MemFrame s.mem P.mem (fw s) := hF.fr
  have hrd : ∀ p n, p + n ≤ s.sp.toNat - a.W ∨ s.sp.toNat + 96 ≤ p → P.mem.readLE p n = s.mem.readLE p n :=
    fun p n h => hPm.readLE p n (fw_out (W := a.W) (by omega) (by simp only [win, outside_cons, outside_nil, and_true]; omega))
  have hacc : ∀ p n w, P.mem.accessible p n w = s.mem.accessible p n w := fun p n w => hPm.accessible p n w
  have hU : ∀ n, n ≤ a.ul.toNat → natVal P.mem a.up.toNat n = natVal s.mem a.up.toNat n := fun n hn => by
    unfold natVal; exact hrd _ _ (by omega)
  have hV : ∀ n, n ≤ a.vl.toNat → natVal P.mem a.vp.toNat n = natVal s.mem a.vp.toNat n := fun n hn => by
    unfold natVal; exact hrd _ _ (by omega)
  refine norm1 impl (s.regs 30) P.mem a.up.toNat a.ul.toNat (natVal P.mem a.up.toNat a.ul.toNat) P Q ?_ (by omega)
    hu48 (by rw [hacc]; exact Memory.accessible_read_of_write _ hua)
    (by rw [hR 4 (by omega), e4, bv_ofNat_toNat]) a.ul.toNat P (Nat.le_refl _) hpc0 (by rw [hR 5 (by omega), e5, bv_ofNat_toNat])
    rfl (fun _ _ _ _ => rfl) rfl rfl
  intro s1 ul' hpc1 hm1 h51 hsp1 hS1 hle1 hv1 hN1
  refine pro1 impl (s.regs 30) s1 ul' a.uc.toNat hpc1 h51
    (by rw [hS1 6 (by decide) (by decide) (by decide), hR 6 (by omega), e6, bv_ofNat_toNat]) (by omega) huc Q ?_
  intro P2 hpc2 hm2 hsp2 hR2
  refine norm2 impl (s.regs 30) P.mem a.vp.toNat a.vl.toNat (natVal P.mem a.vp.toNat a.vl.toNat) P2 Q ?_ (by omega)
    hv48 (by rw [hacc]; exact hva)
    (by rw [hR2 7 (by decide) (by decide), hS1 7 (by decide) (by decide) (by decide), hR 7 (by omega), e7, bv_ofNat_toNat])
    a.vl.toNat P2 (Nat.le_refl _) hpc2
    (by rw [hR2 8 (by decide) (by decide), hS1 8 (by decide) (by decide) (by decide), hR 8 (by omega), e8, bv_ofNat_toNat])
    rfl (fun _ _ _ _ => rfl) (by rw [hm2, hm1]) rfl
  intro s2 vl' hpc3 hm3 h83 hsp3 hS3 hle3 hv3 hN3
  have hvl' : vl' = a.vl.toNat := by
    refine norm_v (M := P.mem) (by omega) ?_ hle3 hv3
    rw [hrd _ _ (by omega)]; exact htop
  subst hvl'
  have hm : s2.mem = P.mem := hm3
  have hreg : ∀ j, j ≤ 10 → j ≠ 5 → j ≠ 8 → s2.regs j = s.regs j := fun j hj h5 h8 => by
    rw [hS3 j h8 (by omega) (by omega), hR2 j (by omega) (by omega), hS1 j h5 (by omega) (by omega), hR j hj]
  have hsp : s2.sp = P.sp := by rw [hsp3, hsp2, hsp1]
  have hFr : Fr s s2 := by
    refine ⟨by rw [hsp]; exact hF.sp, ?_, ?_, ?_, by rw [hm]; exact hF.reg, by rw [hm]; exact hF.fr,
      by rw [hm]; exact hF.lr, by rw [hm]; exact hF.fp⟩
    · rw [hS3 28 (by decide) (by decide) (by decide), hR2 28 (by decide) (by decide),
        hS1 28 (by decide) (by decide) (by decide)]; exact hF.r28
    · rw [hS3 29 (by decide) (by decide) (by decide), hR2 29 (by decide) (by decide),
        hS1 29 (by decide) (by decide) (by decide)]; exact hF.r29
    · rw [hS3 18 (by decide) (by decide) (by decide), hR2 18 (by decide) (by decide),
        hS1 18 (by decide) (by decide) (by decide)]; exact hF.r18
  have hspn : s2.sp.toNat = s.sp.toNat - 400 := by
    rw [hFr.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  refine k s2 ul' ⟨hpc3, hFr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvlc, hvc, by omega, ?_, ?_, hspn,
    by omega, by omega, ?_, ?_, hst48, hal, ?_, by omega⟩ hle1 ?_ ?_
  · rw [hreg 0 (by omega) (by omega) (by omega), e0, bv_ofNat_toNat]
  · rw [hreg 1 (by omega) (by omega) (by omega), e1, bv_ofNat_toNat]
  · rw [hreg 2 (by omega) (by omega) (by omega), e2, bv_ofNat_toNat]
  · rw [hreg 3 (by omega) (by omega) (by omega), e3, bv_ofNat_toNat]
  · rw [hreg 4 (by omega) (by omega) (by omega), e4, bv_ofNat_toNat]
  · rw [hS3 5 (by decide) (by decide) (by decide), hR2 5 (by decide) (by decide)]; exact h51
  · rw [hreg 6 (by omega) (by omega) (by omega), e6, bv_ofNat_toNat]
  · rw [hreg 7 (by omega) (by omega) (by omega), e7, bv_ofNat_toNat]
  · exact h83
  · rw [hreg 9 (by omega) (by omega) (by omega), e9, bv_ofNat_toNat]
  · rw [hreg 10 (by omega) (by omega) (by omega), e10, bv_ofNat_toNat]
  · rw [hm, hrd _ _ (by omega)]; exact h40
  · rw [hm, hacc]; exact Memory.accessible_mono _ hgacc (by omega) (by omega)
  · rw [hm, hacc]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [hm, hacc]; exact Memory.accessible_read_of_write _ hsta
  · rw [hm, hrd _ _ (by omega)]
  · rw [← hU ul' hle1, hv1, hU _ (Nat.le_refl _)]
  · rcases Nat.eq_zero_or_pos ul' with h0 | h0
    · exact Or.inl h0
    · rcases hN1 with h | h
      · exact Or.inl h
      · right; rw [← hrd _ _ (by omega)]; exact h

end FvModexp.Arm64.DivRec
