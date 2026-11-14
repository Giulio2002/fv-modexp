import FvModexp.Proofs.Amd64.Exp.ModInvBuild
import FvModexp.Proofs.Amd64.Exp.ModInvAfter
import FvModexp.Proofs.Amd64.Exp.ModInvSegC

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the round's `zz = zz.sqr(stk, z)` call (agent infra s57; twin of
`Arm64/Exp/ModInvPostS`'s `callSqr`)

`callSqr`: at `nat.sqr`'s entry (`RSP_c = RSP - 232`, the return address `pcv` at `[RSP_c]`, `zz = (q, ql, qc)` in
`RAX, RBX, RCX`, `stk` in `RDI`, `z = (p, l, c)` in `RSI, R8, R9`) with the round facts `Mid` at the entry memory, the
join `S1` at `pcv` gives the goal. Callee: divmc's `Q.NatSqr.ens` shape (`SqrE`, window `kS ≤ kc`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    {pcv : Nat} {Ex : Nat → Memory → Prop} {E Kx : Nat → Nat}

/-- `RSP_c + 8` (the return state's `RSP`) -/
theorem sp_ret {S' : State} (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232))
    (hK : 232 ≤ (s.regs 4).toNat) : S'.regs 4 + 8 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) := by
  rw [hsp]; apply BitVec.eq_of_toNat_eq
  have := (s.regs 4).isLt
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e8]; omega

theorem spN {S' : State} (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232)) :
    (S'.regs 4).toNat = (s.regs 4).toNat - 232 := by
  rw [hsp]; have := (s.regs 4).isLt; exact tN (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callSqr (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    (hsm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a')
    (i : Nat) (hi : i < 0x610) (hpcv : pcv = 0x5ea8c0 + i)
    (k1 : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) (hx0 : s.xmm 15 = 0)
    (hdf0 : s.df = false) {j p l c q ql qc : Nat} {L1 : List (Nat × Nat)} {b1 Zv : Nat} {S' : State}
    (hmid : Mid R kc L s zp zc st xp xl xc n S'.mem L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (Kx j) ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s S'.mem M' → Ex j M') (hzs : ZS s S'.mem p l c) (hzv : natVal S'.mem p l = Zv)
    (hl : l ≤ zB n j) (hb : b - spent sqrC mulC xl n j + stkR H S'.mem st ≤ b1)
    (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232)) (h5 : S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (habi : Abi s S') (hpc : S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatSqr.fn))
    (hrd : S'.mem.readLE (S'.regs 4).toNat 8 = pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h3 : S'.regs 3 = BitVec.ofNat 64 ql) (h1 : S'.regs 1 = BitVec.ofNat 64 qc)
    (h7 : S'.regs 7 = BitVec.ofNat 64 st) (h6 : S'.regs 6 = BitVec.ofNat 64 p) (h8 : S'.regs 8 = BitVec.ofNat 64 l)
    (h9 : S'.regs 9 = BitVec.ofNat 64 c) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S' := by
  subst hpcv
  have hK := sp_K hpre
  have hS' := spN hsp
  obtain ⟨h14, hfs, hx15, hdf⟩ := habi
  have hl0 := len_pos hcong hzv
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnw : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hl' : l ≤ NW n + 1 := Nat.le_trans hl (zB_le hjn)
  have hst : st < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.1; omega
  have hmc : sqrCQ l ≤ sqrC (zB n j) := hsm _ _ hl
  have hmid' := hmid
  obtain ⟨-, -, ⟨zc40, zp64, -⟩, ⟨qc40, qp64, -⟩, -, hlc, hqlc, hnc, hqc⟩ := hmid'
  unfold Goal
  refine sqrCall hap hns hsq H (b1 + 0) (L := L1) (ra_mi hap hnf i hi) hpc hrd (by rw [hx15, hx0])
    (by rw [hdf, hdf0]) h0 h3 h1 h7 h6 h8 h9 qp64 (by omega) hst zp64 (by omega) (by omega) ?_ ?_
  · rw [Nat.add_zero]
    exact sqrPre_mi hpre hmid hS' h14 hfs rfl hkS (by unfold sqrW ksqrW at hkS1 ⊢; omega) hl'
      (bud_ok0 hb hbud (m := sqrC (zB n j)) (by simp only [roundCost]; omega) hmc)
  intro s' hpc' hsp' h5' h14' hx15' hreg hpost
  rw [Nat.add_zero] at hpost
  obtain ⟨hfs', hdf', q', ql', qc', e0, e3, e1, hv', hn', hlc', hl2, hc40', L', b', hLE, hbud', hinv', hlive', hof,
    hstkA, -, hsb, hF', hLF'⟩ := hpost
  rw [h14] at hinv'
  have hqc' : 0 < qc' := by
    rcases hof with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hqc
    · omega
  have hq' : q' < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | -
    · exact qp64
    · have := (hlive' hqc').2.2.2; omega
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hmid hS' hkS (by decide) hreg hF' hLF' hLE hinv' hsb.1 hsb.2 hlive' hc40'
    hq' (hof.imp id fun h => h.2) (fun h1 h2 h3 _ => hstkA h1 h2 h3) hlc' hqc'
  exact k1 s' j p l c q' ql' qc' L' b' Zv ⟨⟨hpre⟩, hn, by rw [hsp']; exact sp_ret hsp (by omega), h5'.trans h5,
    ⟨h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15, hdf'.trans hdf⟩, ⟨mid2⟩, hj1, hjn, hbud, hcong⟩ hpc'
    (hex _ hsl) (zs_keep hsl (by omega) hzs) (hzv2.trans hzv) hl0 hl e0 e3 e1 (by rw [hv', hzv]) hn' (by omega)
    (bud_step0 hb hbud' hmc)

end

end FvModexp.Amd64.ModInv
