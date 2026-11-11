import FvModexp.Proofs.Arm64.Nat.SetBytesDefs

/-! # `nat.setBytes` (arm64): the `nat.norm` loop and the return (`+0xf8` to `RET`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SetBytes

/-- The postcondition from the loop facts at the return. -/
theorem post_intro {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc bp bl : BitVec 64} {s : State} {ret p c : Nat}
    {L' : List (Nat × Nat)} {b' : Nat} {m : Memory} (hmid : Mid R b L zp zc bp bl s ret p c L' b' m) (hc0 : 0 < c)
    (s' : State) (j : Nat) (hm : s'.mem = m) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 1).toNat = j)
    (h2 : (s'.regs 2).toNat = c) (hv : natVal m p j = beVal s.mem bp.toNat bl.toNat) (hn : NatNorm m p j)
    (hjn : j ≤ nW bl) : Post R b L zp zc bp bl s s' := by
  obtain ⟨-, -, -, hnc, hp8, hp48, hpacc, -, -, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid
  subst hm
  exact ⟨p, j, c, h0, h1, h2, hv, hn, by omega, hjn, L', b', hext, hb', hinv,
    fun _ => ⟨hp8, hpheld, hpacc, hp48⟩, hor, hfr, hlf⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem normLoop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (m : Memory)
    (hmid : Mid R b L zp zc bp bl s ret p c L' b' m) (hc0 : 0 < c) (hbl : bl.toNat < 2 ^ 40)
    (hsp : 4160 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 48) true = true) :
    ∀ k (S : State) (P J C : BitVec 64), J.toNat = k → k ≤ nW bl → P.toNat = p → C.toNat = c →
      natVal m p k = beVal s.mem bp.toNat bl.toNat →
      S.pc = BitVec.ofNat 64 hNorm → S.sp = s.sp - 64#64 → S.regs 0 = P → S.regs 1 = J → S.regs 2 = C →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zc bp bl s s') := by
  obtain ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  intro k
  induction k with
  | zero =>
    intro S P J C hJ hk hP hC hval hpc hsp hr0 hr1 hr2 hr28 hr18 hm
    janus_run [hm1, hm2]
    all_goals (refine post_intro ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ hc0 _ 0 rfl ?_ ?_ ?_ (by simpa using hval) (Or.inl rfl) (Nat.zero_le _))
    all_goals janus_simp
    all_goals omega
  | succ k ih =>
    intro S P J C hJ hk hP hC hval hpc hsp hr0 hr1 hr2 hr28 hr18 hm
    janus_run [hm1, hm2] until [hNorm]
    · refine ih _ P (J - 1#64) C (by janus_simp; omega) (by omega) hP hC ?_ (by janus_simp) (by janus_simp) (by janus_simp)
        (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      have h := (by janus_assumption : m.readLE (P.toNat + 8 * (J.toNat - 1)) 8 = 0)
      rw [hP, hJ] at h
      rw [← natVal_zero_top m p k (by simpa using h)]; exact hval
    · have h := (by janus_assumption : ¬m.readLE (P.toNat + 8 * (J.toNat - 1)) 8 = 0)
      rw [hP, hJ] at h
      refine post_intro ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ hc0 _ (k + 1) rfl ?_ ?_ ?_ hval (Or.inr (by simpa using h)) hk
      all_goals janus_simp
      all_goals omega

end FvModexp.Arm64.SetBytes
