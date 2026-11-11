import FvModexp.Proofs.Amd64.Nat.SetBytesNorm

/-! # `nat.setBytes` (amd64): the byte loop (`+0x133`) and the top limb store, then `normLoop` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.SetBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem byteLoop (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (m : Janus.Arm64.Memory)
    (hmid : Mid R b L zp zc bp bl s ret p c L' b' m) (hbl : bl.toNat < 2 ^ 40)
    (hsp : 4160 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 48 ≤ 2 ^ 48 ∧ (s.regs 4).toNat % 8 = 0)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4160) (4160 + 48) true = true)
    (hbacc : s.mem.accessible bp.toNat bl.toNat false = true) (hbp : bp.toNat + bl.toNat ≤ 2 ^ 48)
    (i0 : Nat) (hi0 : 0 < i0 ∧ i0 < 8) (hq : 8 * (nW bl - 1) + i0 = bl.toNat)
    (hlow : natVal m p (nW bl - 1) = beVal s.mem (bp.toNat + i0) (8 * (nW bl - 1))) :
    ∀ k (S : State) (P N C I SH D : BitVec 64), I.toNat = k → k ≤ i0 → P.toNat = p → N.toNat = nW bl → C.toNat = c →
      SH.toNat = 8 * (i0 - k) → D.toNat = beVal s.mem (bp.toNat + k) (i0 - k) →
      S.rip = BitVec.ofNat 64 hByte → S.regs 4 = s.regs 4 - 48#64 → S.regs 0 = P → S.regs 3 = N → S.regs 1 = C →
      S.regs 7 = bp → S.regs 6 = I → S.regs 2 = bl → S.regs 8 = SH → S.regs 9 = D →
      S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = m →
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
    intro S P N C I SH D hI hk hP hN hC hSH hD hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr14 hx15 hfs hdf hm
    have hN1 : 1 ≤ N.toNat := by rw [hN]; exact hnW
    janus64_run [BitVec.msb_eq_decide] until [hNorm]
    have hst := Mid.store hmid D.toNat (a := P.toNat + N.toNat * 8 - 8) (by omega) (by omega)
    refine normLoop impl R b L zp zc bp bl ret hret s p c L' b' _ hst (by omega) hbl ⟨hs1, hs2, hs3⟩ hw (nW bl) _ P N C
      hN (Nat.le_refl _) hP hC ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case refine_1 =>
      have e : nW bl = (nW bl - 1) + 1 := by omega
      have hDlt : D.toNat < 2 ^ 64 := D.isLt
      rw [hP, hN, show p + nW bl * 8 - 8 = p + 8 * (nW bl - 1) by omega]
      generalize nW bl - 1 = q at e hlow hq
      rw [e, natVal_store_top _ _ _ _ hDlt, hlow, hD, Nat.add_zero, Nat.sub_zero]
      conv => rhs; rw [← hq, Nat.add_comm (8 * _) i0]
      rw [beVal_top]
    all_goals first | exact hfs | exact hdf | janus64_simp
  | succ k ih =>
    intro S P N C I SH D hI hk hP hN hC hSH hD hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr14 hx15 hfs hdf hm
    janus64_run [BitVec.msb_eq_decide] until [hByte]
    all_goals first
      | refine ih _ P N C (I - 1#64) (SH + 8#64)
          (D ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (s.mem.readLE (I.toNat + bp.toNat - 1) 1))) <<<
            (SH.toNat % 64) &&& if SH.toNat < 64 then 18446744073709551615#64 else 0#64))
          ?_ (by omega) hP hN hC ?_ ?v1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        case v1 =>
          rw [hI, show k + 1 + bp.toNat - 1 = bp.toNat + k by omega]
          rw [byte_or_step64 s.mem (bp.toNat + k) (i0 - (k + 1)) (by omega) D SH (by omega) (by rw [hD]; congr 1)]
          congr 1; omega
      | refine ih _ P N C (I - 1#64) (SH + 8#64)
          (D ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (s.mem.readLE (I.toNat + bp.toNat - 1) 1))) &&&
            if SH.toNat < 64 then 18446744073709551615#64 else 0#64))
          ?_ (by omega) hP hN hC ?_ ?v0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        case v0 =>
          rw [hI, show k + 1 + bp.toNat - 1 = bp.toNat + k by omega]
          rw [byte_or_step64_zero s.mem (bp.toNat + k) (i0 - (k + 1)) D SH (by omega) (by janus_assumption) (by omega)
            (by rw [hD]; congr 1)]
          congr 1; omega
    all_goals try (janus64_simp; done)
    all_goals try exact hdf
    all_goals janus64_simp; omega

end FvModexp.Amd64.SetBytes
