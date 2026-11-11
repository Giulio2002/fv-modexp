import FvModexp.Proofs.Amd64.Nat.MulAddWWDefs

/-!
# `nat.mulAddWW` (amd64): the inlined `z.norm()` loop and the return (`+0x166`, `TESTQ CX, CX`; `CX = i`, `SI = p`)

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]` (cap reloaded from `0x48(RSP') = RSP - 32`). Memory is unchanged.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (natVal_drop_zero)

namespace FvModexp.Amd64.MulAddWW

abbrev hNorm : Nat := segAddr Extracted.program fn + 0x166

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Amd64.Segment) (s : State) (M : Janus.Arm64.Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → (s'.regs 0).toNat = p → (s'.regs 3).toNat = n' →
      (s'.regs 1).toNat = c → s'.fsBase = s.fsBase → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hr3 : M.readLE ((s.regs 4).toNat - 32) 8 = c) (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 4208 ≤ (s.regs 4).toNat)
    (hsp1 : (s.regs 4).toNat + 72 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 4208) (4208 + 72) true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hNorm → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 6 = BitVec.ofNat 64 p → S.regs 4 = s.regs 4 - 104#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = false → S.mem = M → natVal M p i = V →
      ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h6 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hr3, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfin _ 0 rfl ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hx15 | exact hdf | omega
  | succ i ih =>
    intro S hi hpc h1 h6 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hr3, key, BitVec.msb_eq_decide] until [hNorm]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by first | rfl | exact hdf | (janus64_simp; done) | (janus64_simp; exact hdf)) rfl ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfin _ (i + 1) rfl ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hx15 | exact hdf | omega

end FvModexp.Amd64.MulAddWW
