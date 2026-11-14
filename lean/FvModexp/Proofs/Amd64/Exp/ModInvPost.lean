import FvModexp.Proofs.Amd64.Exp.ModInvPostS

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the round's `zz = zz.trunc(zz, e)` calls (agent infra s57; twin of
`Arm64/Exp/ModInvPost`'s `callT1` / `callT2`)

`callT`: at `nat.trunc`'s entry (`RSP_c = RSP - 232`, return address `pcv` at `[RSP_c]`, `zz = (q, ql, qc)` in
`RAX, RBX, RCX` and `RDI, RSI, R8`, `e` in `R9`) with `Mid` at the entry memory, a continuation over the return state
(`zz` truncated in place: `trunc` never reallocates since `truncNeed ql e ≤ ql ≤ qc`) gives the goal. The joins `S2`
(after the first `trunc`) and `S4` (after the second) are instances, used by the segments.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callT (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (i : Nat) (hi : i < 0x610)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    {e : Nat} (he : e ≤ 2 ^ 20) {p l c q ql qc : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {S' : State}
    (hmid : Mid R kc L s zp zc st xp xl xc n S'.mem L1 b1 p l c q ql qc)
    (hql : ql ≤ 2 * NW n + 2) (hnq : NatNorm S'.mem q ql) (hbT : makeCost (truncNeed ql e) ≤ b1)
    (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232)) (h5 : S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (habi : Abi s S') (hpc : S'.rip = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc))
    (hrd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + i)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h3 : S'.regs 3 = BitVec.ofNat 64 ql) (h1 : S'.regs 1 = BitVec.ofNat 64 qc)
    (h7 : S'.regs 7 = BitVec.ofNat 64 q) (h6 : S'.regs 6 = BitVec.ofNat 64 ql) (h8 : S'.regs 8 = BitVec.ofNat 64 qc)
    (h9 : S'.regs 9 = BitVec.ofNat 64 e)
    (K : ∀ (s' : State) (L' : List (Nat × Nat)) (b' ql' : Nat), s'.rip = BitVec.ofNat 64 (0x5ea8c0 + i) →
      s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) → s'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) →
      Abi s s' → Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l c q ql' qc → SlotsKept s S'.mem s'.mem →
      natVal s'.mem p l = natVal S'.mem p l → s'.regs 0 = BitVec.ofNat 64 q → s'.regs 3 = BitVec.ofNat 64 ql' →
      s'.regs 1 = BitVec.ofNat 64 qc → natVal s'.mem q ql' = natVal S'.mem q ql % 2 ^ e → NatNorm s'.mem q ql' →
      ql' ≤ truncNeed ql e → b1 - makeCost (truncNeed ql e) ≤ b' → stkR H s'.mem st = stkR H S'.mem st →
      Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s') :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S' := by
  have hK := sp_K hpre
  have hS' := spN hsp
  obtain ⟨h14, hfs, hx15, hdf⟩ := habi
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnw : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hmid' := hmid
  obtain ⟨-, hrt, -, hzz, -, -, hqlc, -, hqc⟩ := hmid'
  have hzz' := hzz
  obtain ⟨qc40, qp64, -⟩ := hzz'
  unfold Goal
  refine truncCall hap hns htr b1 (L := L1) (ra_mi hap hnf i hi) hpc hrd (by rw [hx15, hx0]) (by rw [hdf, hdf0])
    h0 h3 h1 h7 h6 h8 h9 qp64 (by omega) (by omega) qp64 (by omega) (by omega)
    (truncPre_mi hpre hmid hS' h14 hfs rfl hkT (by omega) he (by omega) hbT) (Or.inl hnq) (Or.inl rfl) ?_
  intro s' hpc' hsp' h5' h14' hx15' hreg hpost
  obtain ⟨hfs', hdf', q', ql', qc', e0, e3, e1, L', b', ⟨hv, hN, hlc', hc40', hlive', hre, -⟩, -, ⟨hLE, hbud', hinv'⟩,
    hF', hLF'⟩ := hpost
  obtain ⟨eq1, eq2⟩ := hre (Nat.le_trans (Nat.min_le_left _ _) hqlc)
  subst q' qc'
  rw [h14] at hinv'
  obtain ⟨hF2, hLF2, hsb, hain, -, hcap⟩ := nostk hpre hrt hS' hkT haT hzz hF' hLF' hLE
  have hlt : ql' ≤ truncNeed ql e := by
    rcases Nat.eq_zero_or_pos ql' with h | h
    · omega
    · have hlo := FvModexp.SubMod2N.natVal_lower _ _ _ hN h
      have hup : natVal S'.mem q ql % 2 ^ e < 2 ^ (64 * truncNeed ql e) := by
        simp only [truncNeed]
        rcases Nat.le_total ql ((e + 63) / 64) with hm | hm
        · rw [Nat.min_eq_left hm]
          exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (natVal_lt _ _ _)
        · rw [Nat.min_eq_right hm]
          exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos e))
            (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hv] at hlo
      have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 (Nat.lt_of_le_of_lt hlo hup)
      omega
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hmid hS' hkT haT hreg hF2 hLF2 hLE hinv' hsb hain hlive' hc40' qp64
    (Or.inl ⟨rfl, rfl⟩) (fun h => absurd ⟨rfl, rfl⟩ h) hlc' hqc
  exact K s' L' b' ql' hpc' (by rw [hsp']; exact sp_ret hsp (by omega)) (h5'.trans h5)
    ⟨h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15, hdf'.trans hdf⟩ mid2 hsl hzv2 e0 e3 e1 hv hN hlt hbud'
    (stkR_congr hcap)

end

end FvModexp.Amd64.ModInv
