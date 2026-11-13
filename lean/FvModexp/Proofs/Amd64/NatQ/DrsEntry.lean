import FvModexp.Proofs.Amd64.NatQ.DrsAt
import FvModexp.Proofs.Amd64.NatQ.DrsFin

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): entry → the dispatch (`pro0 → norm1 → pro1 → norm2 → pro2`)

`u = u.norm()`, `v = v.norm()` (natdiv.go:754-755); `v`'s length is kept (its top word is `≥ 2^63`, `DrsPreW.vtop`).
Twin of Arm64/NatQ/DrsEntry.lean `entry`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `AtE2` -/
theorem entry (impl : List Amd64.Segment) (R : RtInv) (a : Args) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5ef880)
    (hE : Entry a s) {c : Nat} (hpre : DrsPreW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat
      a.up.toNat a.ul.toNat a.uc.toNat a.vp a.vl a.vc s) (hW : 400 ≤ a.W) (Q : State → Prop)
    (k : ∀ (P : State) (ul' : Nat), AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat
      a.vp a.vl a.vc a.d.toNat → ul' ≤ a.ul.toNat →
      natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat → NatNorm s.mem a.up.toNat ul' →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) P Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) s Q := by
  have hce := hpre.ce
  have hua := hpre.ua
  have hva := hpre.va
  have hulc := hpre.ulc
  have huc := hpre.uc40
  have hvlc := hpre.vlc
  have hvc := hpre.vc40
  have hv2 := hpre.v2
  have htop := hpre.vtop
  have hvpS := hpre.vpS
  have hvlS := hpre.vlS
  have hvcS := hpre.vcS
  clear hpre
  obtain ⟨hra, hx15, hdf, e0, e3, e1, e7, e6, e8, e9, e10⟩ := hE
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  obtain ⟨hua1, hu48, -, huo, -⟩ := hua
  obtain ⟨hva1, hv48, -, hvo, -⟩ := hva
  simp only [win, outside_cons, outside_nil, and_true] at huo hvo
  refine pro0 impl s a.W (retAddrOf s) hpc hx15 hdf hce hW Q fun P hpc0 hF hx0 hR hs32 hs64 hd16 hd297 => ?_
  have hPm : MemFrame s.mem P.mem (fw s) := hF.fr
  have hacc : ∀ p n w, P.mem.accessible p n w = s.mem.accessible p n w := fun p n w => hPm.accessible p n w
  have hU : ∀ n, n ≤ a.ul.toNat → natVal P.mem a.up.toNat n = natVal s.mem a.up.toNat n := fun n hn =>
    natVal_frame hPm (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)
  have hV : ∀ n, n ≤ a.vl → natVal P.mem a.vp n = natVal s.mem a.vp n := fun n hn =>
    natVal_frame hPm (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)
  have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hF.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hwP : P.mem.accessible ((s.regs 4).toNat + 8) 24 false = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hrS : ∀ j, j ≠ 4 → j ≠ 5 → j ≠ 12 → P.regs j = s.regs j := hR
  refine norm1 impl (retAddrOf s) P.mem a.up.toNat a.ul.toNat (natVal P.mem a.up.toNat a.ul.toNat) P Q ?_
    (by omega) hu48 (by rw [hacc]; exact Janus.Arm64.Memory.accessible_read_of_write _ hua1)
    (by rw [hrS 6 (by decide) (by decide) (by decide), e6, bv_ofNat_toNat]) a.ul.toNat P (Nat.le_refl _) hpc0
    (by rw [hrS 8 (by decide) (by decide) (by decide), e8, bv_ofNat_toNat]) ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩ rfl rfl
  intro s1 ul' hpc1 hm1 h81 hS1 hle1 hv1 hN1
  have hs14 : s1.regs 4 = P.regs 4 := hS1.1 4 (by decide) (by decide)
  have hsp1 : (s1.regs 4).toNat = (s.regs 4).toNat - 392 := by rw [hs14, hspP]
  have e190' : (s.regs 4).toNat - 392 + 0x190 = (s.regs 4).toNat + 8 := by omega
  have e1a0 : (s.regs 4).toNat - 392 + 0x1a0 = (s.regs 4).toNat + 24 := by omega
  have hac1 : P.mem.accessible ((s.regs 4).toNat + 8) 16 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hwP (by omega) (by omega)
  have hac2 : P.mem.accessible ((s.regs 4).toNat + 24) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hwP (by omega) (by omega)
  refine pro1 impl (retAddrOf s) s1 Q hpc1 ?_ (by rw [hsp1, hm1, e190']; exact hac1) (by omega) ?_
  · rw [h81, hS1.1 9 (by decide) (by decide), hrS 9 (by decide) (by decide) (by decide), e9,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  intro P2 hpc2 hm2 h22 h112 hR2 hfs2 hdf2 hx2
  have hm2' : P2.mem = P.mem := hm2.trans hm1
  have e190 : (s1.regs 4).toNat + 0x190 = (s.regs 4).toNat + 8 := by omega
  have e198 : (s1.regs 4).toNat + 0x198 = (s.regs 4).toNat + 16 := by omega
  rw [e190, hm1, hF.vp, hvpS] at h22
  rw [e198, hm1, hF.vl, hvlS] at h112
  refine norm2 impl (retAddrOf s) P.mem a.vp a.vl (natVal P.mem a.vp a.vl) P2 Q ?_ (by omega) hv48
    (by rw [hacc]; exact hva1) h22 a.vl P2 (Nat.le_refl _) hpc2 h112 ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩ hm2' rfl
  intro s2 vl' hpc3 hm3 h113 hS3 hle3 hv3 hN3
  have hvl' : vl' = a.vl := by
    refine norm_v (M := P.mem) (by omega) ?_ hle3 hv3
    rw [hPm.readLE _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)]; exact htop
  subst hvl'
  have hs24 : s2.regs 4 = P.regs 4 := by
    rw [hS3.1 4 (by decide) (by decide), hR2 4 (by decide) (by decide), hs14]
  have hsp2 : (s2.regs 4).toNat = (s.regs 4).toNat - 392 := by rw [hs24, hspP]
  have hm3' : s2.mem = P.mem := hm3
  refine pro2 impl (retAddrOf s) s2 Q hpc3 ?_ (by rw [hsp2, hm3', e1a0]; exact hac2) (by omega) ?_
  · rw [h113, hsp2, hm3', e1a0, hF.vc, hvcS,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hvlc
  intro P3 hpc4 hm4 h124 hR4 hfs4 hdf4 hx4
  have hm : P3.mem = P.mem := hm4.trans hm3'
  rw [hsp2, hm3', e1a0, hF.vc, hvcS] at h124
  -- registers other than R2, R8, R11, R12 come from `P`
  have hreg : ∀ j, j ≠ 2 → j ≠ 8 → j ≠ 11 → j ≠ 12 → P3.regs j = P.regs j := fun j h2 h8 h11 h12 => by
    rw [hR4 j h12, hS3.1 j h11 h12, hR2 j h2 h11, hS1.1 j h8 h2]
  have hFr : Fr s P3 := hF.congr hm (hreg 4 (by decide) (by decide) (by decide) (by decide))
    (hreg 5 (by decide) (by decide) (by decide) (by decide)) (hreg 14 (by decide) (by decide) (by decide) (by decide))
    (by rw [hfs4, hS3.2.1, hfs2, hS1.2.1]) (by rw [hdf4, hS3.2.2.1, hdf2, hS1.2.2.1])
  have hrs : ∀ j, j ≤ 10 → j ≠ 2 → j ≠ 4 → j ≠ 5 → j ≠ 8 → P3.regs j = s.regs j := fun j hj h2 h4 h5 h8 => by
    rw [hreg j h2 h8 (by omega) (by omega), hrS j h4 h5 (by omega)]
  refine k P3 ul' ⟨hpc4, hFr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hle1 ?_ ?_
  · rw [hx4, hS3.2.2.2, hx2, hS1.2.2.2]; exact hx0
  · rw [hrs 0 (by omega) (by omega) (by omega) (by omega) (by omega), e0, bv_ofNat_toNat]
  · rw [hrs 3 (by omega) (by omega) (by omega) (by omega) (by omega), e3, bv_ofNat_toNat]
  · rw [hrs 1 (by omega) (by omega) (by omega) (by omega) (by omega), e1, bv_ofNat_toNat]
  · rw [hrs 7 (by omega) (by omega) (by omega) (by omega) (by omega), e7, bv_ofNat_toNat]
  · rw [hrs 6 (by omega) (by omega) (by omega) (by omega) (by omega), e6, bv_ofNat_toNat]
  · rw [hR4 8 (by decide), hS3.1 8 (by decide) (by decide), hR2 8 (by decide) (by decide)]; exact h81
  · rw [hrs 9 (by omega) (by omega) (by omega) (by omega) (by omega), e9, bv_ofNat_toNat]
  · rw [hrs 10 (by omega) (by omega) (by omega) (by omega) (by omega), e10, bv_ofNat_toNat]
  · rw [hR4 2 (by decide), hS3.1 2 (by decide) (by decide)]; exact h22
  · rw [hR4 11 (by decide)]; exact h113
  · exact h124
  · rw [hm]; exact hs32.trans (by rw [e0])
  · rw [hm]; exact hs64.trans (by rw [e6])
  · rw [hm]; exact hd16
  · rw [hm]; exact hd297
  · rw [← hU ul' hle1, hv1, hU _ (Nat.le_refl _)]
  · rcases Nat.eq_zero_or_pos ul' with h0 | h0
    · exact Or.inl h0
    · rcases hN1 with h | h
      · exact Or.inl h
      · right; rw [← hPm.readLE _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)]; exact h

end FvModexp.Amd64.Q.DivRec
