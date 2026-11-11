import FvModexp.Proofs.Amd64.Nat.SetBytesDefs

/-! # `nat.setBytes` (amd64): the `nat.norm` loop and the return (`+0xeb` to `RET`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.SetBytes

/-- The postcondition from the loop facts at the return. -/
theorem post_intro {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc bp bl : BitVec 64} {s : State} {ret p c : Nat}
    {L' : List (Nat × Nat)} {b' : Nat} {m : Janus.Arm64.Memory} (hmid : Mid R b L zp zc bp bl s ret p c L' b' m) (hc0 : 0 < c)
    (s' : State) (j : Nat) (hfs' : s'.fsBase = s.fsBase) (hdf' : s'.df = s.df) (hm : s'.mem = m) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 3).toNat = j)
    (h2 : (s'.regs 1).toNat = c) (hv : natVal m p j = beVal s.mem bp.toNat bl.toNat) (hn : NatNorm m p j)
    (hjn : j ≤ nW bl) : Post R b L zp zc bp bl s s' := by
  obtain ⟨-, -, -, hnc, hp8, hp48, hpacc, -, -, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid
  subst hm
  exact ⟨hfs', hdf', p, j, c, h0, h1, h2, hv, hn, by omega, hjn, L', b', hext, hb', hinv,
    fun _ => ⟨hp8, hpheld, hpacc, hp48⟩, hor, hfr, hlf⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normLoop (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (m : Janus.Arm64.Memory)
    (hmid : Mid R b L zp zc bp bl s ret p c L' b' m) (hc0 : 0 < c) (hbl : bl.toNat < 2 ^ 40)
    (hsp : 4160 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 48 ≤ 2 ^ 48 ∧ (s.regs 4).toNat % 8 = 0)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4160) (4160 + 48) true = true) :
    ∀ k (S : State) (P J C : BitVec 64), J.toNat = k → k ≤ nW bl → P.toNat = p → C.toNat = c →
      natVal m p k = beVal s.mem bp.toNat bl.toNat →
      S.rip = BitVec.ofNat 64 hNorm → S.regs 4 = s.regs 4 - 48#64 → S.regs 0 = P → S.regs 3 = J → S.regs 1 = C →
      S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zc bp bl s s') := by
  obtain ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := hmid
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  intro k
  induction k with
  | zero =>
    intro S P J C hJ hk hP hC hval hpc hsp hr0 hr1 hr2 hr14 hx15 hfs hdf hm
    janus64_run [hm1, hm2, BitVec.msb_eq_decide]
    all_goals (refine post_intro ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ hc0 _ 0 ?_ ?_ rfl ?_ ?_ ?_ (by simpa using hval) (Or.inl rfl) (Nat.zero_le _))
    all_goals first | exact hdf | janus64_simp
    all_goals first | exact hdf | omega
  | succ k ih =>
    intro S P J C hJ hk hP hC hval hpc hsp hr0 hr1 hr2 hr14 hx15 hfs hdf hm
    janus64_run [hm1, hm2, BitVec.msb_eq_decide] until [hNorm]
    case h =>
      refine ih _ P (J - 1#64) C ?_ (by omega) hP hC ?v ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      case v =>
        have h := (by janus_assumption : m.readLE (P.toNat + J.toNat * 8 - 8) 8 = 0)
        rw [hP, hJ, show p + (k + 1) * 8 - 8 = p + 8 * k by omega] at h
        rw [← natVal_zero_top m p k h]; exact hval
      all_goals first | exact hdf | janus64_simp
      all_goals first | exact hdf | omega
    case hq =>
      have h := (by janus_assumption : ¬m.readLE (P.toNat + J.toNat * 8 - 8) 8 = 0)
      rw [hP, hJ, show p + (k + 1) * 8 - 8 = p + 8 * (k + 1 - 1) by omega] at h
      refine post_intro ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ hc0 _ (k + 1) ?_ ?_ rfl ?_ ?_ ?_ hval (Or.inr h) hk
      all_goals first | exact hdf | janus64_simp
      all_goals first | exact hdf | omega

end FvModexp.Amd64.SetBytes
