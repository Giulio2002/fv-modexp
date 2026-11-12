import FvModexp.Proofs.Arm64.Nat.SetBytesNorm

set_option autoImplicit false

/-! # `nat.setBytes` (arm64): the byte loop (`+0x140`) and the top limb store, then `normLoop` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SetBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem byteLoop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (m : Memory)
    (hmid : Mid R b L zp zc bp bl s ret p c L' b' m) (hbl : bl.toNat < 2 ^ 40 ∧ CapB zc.toNat c)
    (hsp : 4160 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 48) true = true)
    (hbacc : s.mem.accessible bp.toNat bl.toNat false = true) (hbp : bp.toNat + bl.toNat ≤ 2 ^ 48)
    (i0 : Nat) (hi0 : 0 < i0 ∧ i0 < 8) (hq : 8 * (nW bl - 1) + i0 = bl.toNat)
    (hlow : natVal m p (nW bl - 1) = beVal s.mem (bp.toNat + i0) (8 * (nW bl - 1))) :
    ∀ k (S : State) (P N C I SH D : BitVec 64), I.toNat = k → k ≤ i0 → P.toNat = p → N.toNat = nW bl → C.toNat = c →
      SH.toNat = 8 * (i0 - k) → D.toNat = beVal s.mem (bp.toNat + k) (i0 - k) →
      S.pc = BitVec.ofNat 64 hByte → S.sp = s.sp - 64#64 → S.regs 0 = P → S.regs 1 = N → S.regs 2 = C →
      S.regs 3 = bp → S.regs 4 = I → S.regs 5 = bl → S.regs 6 = SH → S.regs 7 = D →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zc bp bl s s') := by
  have hmid' := hmid
  obtain ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid'
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  unfold Apart at hpb hpw
  have hnW : 1 ≤ nW bl := by unfold nW; omega
  intro k
  induction k with
  | zero =>
    intro S P N C I SH D hI hk hP hN hC hSH hD hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr28 hr18 hm
    have hN1 : 1 ≤ N.toNat := by rw [hN]; exact hnW
    janus_run until [hNorm]
    have hst := Mid.store hmid D.toNat (a := P.toNat + 8 * (N.toNat - 1)) (by omega) (by omega)
    refine normLoop impl R b L zp zc bp bl ret hret s p c L' b' _ hst (by omega) hbl ⟨hs1, hs2, hs3⟩ hw (nW bl) _ P N C
      hN (Nat.le_refl _) hP hC ?_ (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      (by janus_simp) (by janus_simp) (by janus_simp)
    have e : nW bl = (nW bl - 1) + 1 := by omega
    have hDlt : D.toNat < 2 ^ 64 := D.isLt
    rw [hP, hN]
    generalize nW bl - 1 = q at e hlow hq
    rw [e, natVal_store_top _ _ _ _ hDlt, hlow, hD, Nat.add_zero, Nat.sub_zero]
    conv => rhs; rw [← hq, Nat.add_comm (8 * _) i0]
    rw [beVal_top]
  | succ k ih =>
    intro S P N C I SH D hI hk hP hN hC hSH hD hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr28 hr18 hm
    janus_run until [hByte]
    refine ih _ P N C (I - 1#64) (SH + 8#64)
      (D ||| if SH.toNat < 64 then BitVec.ofNat 64 (s.mem.readLE (bp.toNat + (I.toNat - 1)) 1 * 2 ^ (SH.toNat % 64))
        else 0#64) (by janus_simp; omega) (by omega) hP hN hC ?_ ?_
      (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    · janus_simp; omega
    · rw [hI] at *
      have := byte_or_step s.mem (bp.toNat + k) (i0 - (k + 1)) (by omega) D SH (by omega)
        (by rw [hD]; congr 1)
      rw [show k + 1 - 1 = k by omega, this]; congr 1; omega

end FvModexp.Arm64.SetBytes
