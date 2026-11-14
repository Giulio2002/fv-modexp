import FvModexp.Proofs.Amd64.Exp.ModInvPostS

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the round's `z = z.lsh(z, 1)` call (agent infra s57; twin of
`Arm64/Exp/ModInvPostS`'s `callLsh`)

`callLsh`: at `nat.lsh`'s entry (`RSP_c = RSP - 232`, return address at `[RSP_c]`, `z = (p, l, c)` in `RAX, RBX, RCX`
and `RDI, RSI, R8`, shift `1` in `R9`) with `Mid` at the entry memory, a continuation over the return state (the new
`z = (p', l', c')`, `zz` kept with its words) gives the goal (used by the segment ending in `S5`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callLsh (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (i : Nat) (hi : i < 0x610)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    {p l c q ql qc : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {S' : State}
    (hmid : Mid R kc L s zp zc st xp xl xc n S'.mem L1 b1 p l c q ql qc)
    (hl0 : 0 < l) (hl : l ≤ NW n + 1) (hbL : makeCost (l + 1 / 64 + 1) ≤ b1)
    (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232)) (h5 : S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (habi : Abi s S') (hpc : S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Lsh.fn))
    (hrd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + i)
    (h0 : S'.regs 0 = BitVec.ofNat 64 p) (h3 : S'.regs 3 = BitVec.ofNat 64 l) (h1 : S'.regs 1 = BitVec.ofNat 64 c)
    (h7 : S'.regs 7 = BitVec.ofNat 64 p) (h6 : S'.regs 6 = BitVec.ofNat 64 l) (h8 : S'.regs 8 = BitVec.ofNat 64 c)
    (h9 : S'.regs 9 = BitVec.ofNat 64 1)
    (K : ∀ (s' : State) (L' : List (Nat × Nat)) (b' p' l' c' : Nat), s'.rip = BitVec.ofNat 64 (0x5ea8c0 + i) →
      s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) → s'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) →
      Abi s s' → Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p' l' c' q ql qc → SlotsKept s S'.mem s'.mem →
      (∀ k, k ≤ qc → s'.mem.readLE q (8 * k) = S'.mem.readLE q (8 * k)) →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c' →
      natVal s'.mem p' l' = natVal S'.mem p l * 2 → NatNorm s'.mem p' l' → l' ≤ l + 1 →
      b1 - makeCost (l + 1 / 64 + 1) ≤ b' → stkR H s'.mem st = stkR H S'.mem st →
      Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s') :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S' := by
  have hK := sp_K hpre
  have hS' := spN hsp
  obtain ⟨h14, hfs, hx15, hdf⟩ := habi
  have hmid' := hmid
  obtain ⟨-, hrt, hz, -, -, hlc, -, hnc, -⟩ := hmid'
  have hz' := hz
  obtain ⟨zc40, zp64, -⟩ := hz'
  unfold Goal
  refine lshCall hap hns hls b1 (L := L1) (ra_mi hap hnf i hi) hpc hrd (by rw [hx15, hx0]) (by rw [hdf, hdf0])
    h0 h3 h1 h7 h6 h8 h9 zp64 (by omega) (by omega) zp64 (by omega) (by decide)
    (lshPre_mi hpre hmid hS' h14 hfs rfl hkL (by omega) hl hbL) (by decide) hl0 ?_
  intro s' hpc' hsp' h5' h14' hx15' hreg hpost
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, L', b', ⟨hv, hN, hlc', hc40', hlive', hre, hfr⟩, hcap', ⟨hLE, hbud', hinv'⟩,
    hF', hLF'⟩ := hpost
  rw [h14] at hinv'
  obtain ⟨hF2, hLF2, hsb, hain, hw0, hcap⟩ := nostk hpre hrt hS' hkL haL hz hF' hLF' hLE
  have hof : (p' = p ∧ c' = c) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1) := by
    rcases Nat.lt_or_ge c (l + 1 / 64 + 1) with h | h
    · exact Or.inr (hfr h (by have := hcap' h; omega))
    · exact Or.inl (hre h)
  have hc' : NW n + 1 ≤ c' := by
    rcases Nat.lt_or_ge c (l + 1 / 64 + 1) with h | h
    · have := hcap' h; omega
    · obtain ⟨-, rfl⟩ := hre h; exact hnc
  have hp' : p' < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | -
    · exact zp64
    · have := (hlive' (by omega)).2.2.2; omega
  have hll : l' ≤ l + 1 := by
    refine len_le hN ?_
    rw [hv, Nat.pow_one, show 64 * (l + 1) = 64 * l + 1 * 64 by omega, Nat.pow_add]
    have := natVal_lt S'.mem p l
    have : 2 ≤ 2 ^ (1 * 64) := Nat.le_trans (by decide) (Nat.le_refl _)
    exact Nat.mul_lt_mul_of_lt_of_le (natVal_lt _ _ _) (by decide) (by decide)
  obtain ⟨mid2, hq2, hsl⟩ := after_z hpre hmid hS' hkL haL hreg hF2 hLF2 hLE hinv' hsb hain hlive' hc40' hp' hof
    (fun _ _ _ h => absurd ⟨hw0, hcap⟩ h) hlc' hc'
  exact K s' L' b' p' l' c' hpc' (by rw [hsp']; exact sp_ret hsp (by omega)) (h5'.trans h5)
    ⟨h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15, hdf'.trans hdf⟩ mid2 hsl hq2 e0 e3 e1
    (by rw [hv, Nat.pow_one]) hN hll hbud' (stkR_congr hcap)

end

end FvModexp.Amd64.ModInv
