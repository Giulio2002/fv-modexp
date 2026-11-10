import FvModexp.Proofs.Arm64.Nat.SetBytesByte

/-! # `nat.setBytes` (arm64): the word loop (`+0xbc`), then `byteLoop` or `normLoop` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SetBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem wordLoop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat)
    (hbl : bl.toNat < 2 ^ 40) (hbl0 : 0 < bl.toNat)
    (hsp : 4160 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 48) true = true)
    (hbacc : s.mem.accessible bp.toNat bl.toNat false = true) (hbp : bp.toNat + bl.toNat ≤ 2 ^ 48) :
    ∀ k (S : State) (m : Memory) (P N C I K : BitVec 64), I.toNat = 8 * k + I.toNat % 8 → I.toNat + 8 * K.toNat = bl.toNat →
      P.toNat = p → N.toNat = nW bl → C.toNat = c →
      Mid R b L zp zc bp bl s ret p c L' b' m →
      natVal m p K.toNat = beVal s.mem (bp.toNat + I.toNat) (8 * K.toNat) →
      S.pc = BitVec.ofNat 64 hWord → S.sp = s.sp - 64#64 → S.regs 0 = P → S.regs 1 = N → S.regs 2 = C →
      S.regs 3 = bp → S.regs 4 = I → S.regs 5 = bl → S.regs 6 = K →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zc bp bl s s') := by
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  have hnW : 1 ≤ nW bl := by unfold nW; omega
  intro k
  induction k with
  | zero =>
    intro S m P N C I K hI hIK hP hN hC hmid hval hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr28 hr18 hm
    have hmid' := hmid
    obtain ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid'
    unfold Apart at hpb hpw
    have hc0 : 0 < c := by omega
    simp only [nW] at hN hnc
    janus_run until [hByte, hNorm]
    · have hK : K.toNat = nW bl := by unfold nW; omega
      refine normLoop impl R b L zp zc bp bl ret hret s p c L' b' m hmid hc0 hbl ⟨hs1, hs2, hs3⟩ hw (nW bl) _ P N C
        (by unfold nW; omega) (Nat.le_refl _) hP hC ?_ (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
        (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      rw [← hK, hval, show I.toNat = 0 by omega, Nat.add_zero, show 8 * K.toNat = bl.toNat by omega]
    · have hK : K.toNat = nW bl - 1 := by unfold nW; omega
      refine byteLoop impl R b L zp zc bp bl ret hret s p c L' b' m hmid hbl ⟨hs1, hs2, hs3⟩ hw hbacc hbp I.toNat
        ⟨by omega, by omega⟩ (by rw [← hK]; omega) (by rw [← hK]; exact hval) I.toNat _ P N C I 0#64 0#64 rfl
        (Nat.le_refl _) hP (by unfold nW; omega) hC (by simp) (by simp)
        (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
        (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
  | succ k ih =>
    intro S m P N C I K hI hIK hP hN hC hmid hval hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr28 hr18 hm
    have hmid' := hmid
    obtain ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid'
    unfold Apart at hpb hpw
    simp only [nW] at hN hnc
    janus_run until [hWord]
    have hv8 : revContainersNat 8 1 (s.mem.readLE (bp.toNat + (I.toNat - 8)) 8) =
        beVal s.mem (bp.toNat + (I.toNat - 8)) 8 := revContainers_readLE8 _ _
    have hst := Mid.store hmid (revContainersNat 8 1 (s.mem.readLE (bp.toNat + (I.toNat - 8)) 8))
      (a := P.toNat + 8 * K.toNat) (by omega) (by omega)
    refine ih _ _ P N C (I - 8#64) (K + 1#64) (by janus_simp; omega) (by janus_simp; omega) hP hN hC hst ?_
      (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    have e1 : (I - 8#64).toNat = I.toNat - 8 := by janus_simp
    have e2 : (K + 1#64).toNat = K.toNat + 1 := by janus_simp
    rw [e1, e2, hP, natVal_store_top _ _ _ _ (by rw [hv8]; exact Nat.lt_of_lt_of_le (beVal_lt _ _ _) (by decide)),
      hval, hv8, beVal_word_step, show bp.toNat + (I.toNat - 8) + 8 = bp.toNat + I.toNat by omega]

end FvModexp.Arm64.SetBytes
