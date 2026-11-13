import FvModexp.Proofs.Amd64.NatQ.SqrRel

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/SqrNorm.lean — TIGHT COSTS, divmc s38] `nat.sqr` (amd64): the four inlined `z.norm()` loops and the returns

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]`; the result is stored to `0x70..0x87(SP')` (`SP' = RSP - 168`, i.e.
`[RSP - 56, RSP - 32)`) and returned in `AX, BX, CX`. `norm1` (after `n = 1`, `0x5f13ae`: `AX = i`, `BX = p`, `CX = cap`),
`normM` (after `basicMul`, `0x5f136b`: `BX = i`, `AX = p`, cap reloaded from `0x50(SP') = RSP - 88`), `normS` / `normK`
(after `basicSqr` / `karatsubaSqr`, `0x5f1300` / `0x5f128f`: `CX = i`, `BX = p`, cap from `0x50(SP')`, defer flag byte
`0x4f(SP') = RSP - 89` clear). Twin of the arm64 module.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

abbrev hnorm1 : Nat := 0x5f13ae

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm1 (impl : List Amd64.Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' → s'.regs 1 = BitVec.ofNat 64 c →
      s'.fsBase = s.fsBase → s'.df = s.df → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 168 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 168) 176 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hnorm1 → S.regs 0 = BitVec.ofNat 64 i →
      S.regs 3 = BitVec.ofNat 64 p → S.regs 1 = BitVec.ofNat 64 c → S.regs 4 = s.regs 4 - 168#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = M →
      natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hp0 hcr hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hdf | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc hi0 hp0 hcr hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, key, BitVec.msb_eq_decide] until [hnorm1]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by janus64_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hdf | exact hx15 | omega

abbrev hnormM : Nat := 0x5f136b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normM (impl : List Amd64.Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' → s'.regs 1 = BitVec.ofNat 64 c →
      s'.fsBase = s.fsBase → s'.df = s.df → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hr3 : M.readLE ((s.regs 4).toNat - 88) 8 = c)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 168 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 168) 176 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hnormM → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 4 = s.regs 4 - 168#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = M →
      natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hr3, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hdf | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hr3, key, BitVec.msb_eq_decide] until [hnormM]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by janus64_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hdf | exact hx15 | omega

abbrev hnormS : Nat := 0x5f1300

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normS (impl : List Amd64.Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' → s'.regs 1 = BitVec.ofNat 64 c →
      s'.fsBase = s.fsBase → s'.df = s.df → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hr3 : M.readLE ((s.regs 4).toNat - 88) 8 = c) (hb : M.readLE ((s.regs 4).toNat - 89) 1 = 0)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 168 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 168) 176 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hnormS → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 3 = BitVec.ofNat 64 p → S.regs 4 = s.regs 4 - 168#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = M →
      natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hr3, hb, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hdf | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hr3, hb, key, BitVec.msb_eq_decide] until [hnormS]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by janus64_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hdf | exact hx15 | omega

abbrev hnormK : Nat := 0x5f128f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normK (impl : List Amd64.Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' → s'.regs 1 = BitVec.ofNat 64 c →
      s'.fsBase = s.fsBase → s'.df = s.df → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hr3 : M.readLE ((s.regs 4).toNat - 88) 8 = c) (hb : M.readLE ((s.regs 4).toNat - 89) 1 = 0)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 168 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 168) 176 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hnormK → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 3 = BitVec.ofNat 64 p → S.regs 4 = s.regs 4 - 168#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = M →
      natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hr3, hb, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hdf | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hr3, hb, key, BitVec.msb_eq_decide] until [hnormK]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by janus64_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hdf | exact hx15 | omega

end FvModexp.Amd64.Q.NatSqr
