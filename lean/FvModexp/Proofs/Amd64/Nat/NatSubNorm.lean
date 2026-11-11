import FvModexp.Proofs.Amd64.Nat.NatSubDefs

/-!
# `nat.sub` (amd64): the `z.norm()` loop and the return (`+0x301`, `TESTQ SI, SI`; `SI = i`, `AX = p`)

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]` (cap reloaded from `0x58(RSP') = RSP - 56`). Memory is unchanged.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSub

abbrev hNorm : Nat := segAddr Extracted.program fn + 0x301

/-- The register part of the postcondition of every `nat.add` segment (what `Ensures.toSummaryIn` keeps). -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

theorem natVal_drop_zero {M : Janus.Arm64.Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Amd64.Segment) (s : State) (M : Janus.Arm64.Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → (s'.regs 0).toNat = p → (s'.regs 3).toNat = n' →
      (s'.regs 1).toNat = c → s'.fsBase = s.fsBase → s'.df = false → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hr3 : M.readLE ((s.regs 4).toNat - 56) 8 = c) (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 4288 ≤ (s.regs 4).toNat)
    (hsp1 : (s.regs 4).toNat + 80 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 4288) (4288 + 80) true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hNorm → S.regs 6 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 4 = s.regs 4 - 144#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = false → S.mem = M → natVal M p i = V →
      ReachesRet (LibNatSub.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h2 h0 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hr3, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 rfl ?_ ?_ ?_ ?_ rfl (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc h2 h0 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hr3, key, BitVec.msb_eq_decide] until [hNorm]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) rfl rfl ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) rfl ?_ ?_ ?_ ?_ rfl hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hx15 | omega

end FvModexp.Amd64.NatSub
