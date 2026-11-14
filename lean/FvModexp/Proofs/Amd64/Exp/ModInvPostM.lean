import FvModexp.Proofs.Amd64.Exp.ModInvPostS
import FvModexp.Proofs.Amd64.NatQ.MulW64

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the round's `zz = zz.mul(stk, zz, x[:k])` call (agent infra s58; twin of
`Arm64/Exp/ModInvPostM`'s `callMul`)

`callMul`: at `nat.mul`'s entry (`RSP_c = RSP - 232`, the return address `pcv` at `[RSP_c]`, `zz = (q, ql, qc)` in
`RAX, RBX, RCX` (output) and `RSI, R8, R9` (first operand), `stk` in `RDI`, `y = x[:k] = (xp, k, xc)` with
`k = min (Kx j) xl` on the stack at `RSP_c + 8 / 16 / 24`, stored by the caller) with `S2`'s facts and the round
facts `Mid` at the entry memory, the join `S3` at `pcv` gives the goal. Callee: asm's `Q.DivRec.MulHypQE` (window
`kM ≤ kc`, `mulWX64 ≤ kM`, which covers every `nat.mul` window on operands of at most `2^12` words).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    {pcv : Nat} {Ex : Nat → Memory → Prop} {E Kx : Nat → Nat}

theorem len2 {a b c d e : Nat} (h : a ≤ b + c) (h1 : b ≤ e) (h2 : c ≤ d) (h3 : d ≤ e) : a ≤ 2 * e := by omega

theorem len2' {b c d e : Nat} (h1 : b ≤ e) (h2 : c ≤ d) (h3 : d ≤ e) : b + c ≤ 2 * e + 2 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callMul (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c)
    (i : Nat) (hi : i < 0x610) (hpcv : pcv = 0x5ea8c0 + i)
    (k3 : S3 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) (hx0 : s.xmm 15 = 0)
    (hdf0 : s.df = false) {j p l c q ql qc : Nat} {L1 : List (Nat × Nat)} {b1 Zv : Nat} {S' : State}
    (hmid : Mid R kc L s zp zc st xp xl xc n S'.mem L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (Kx j) ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s S'.mem M' → Ex j M') (hzs : ZS s S'.mem p l c) (hzv : natVal S'.mem p l = Zv)
    (hl0 : 0 < l) (hl : l ≤ zB n j) (hv : natVal S'.mem q ql = Zv * Zv % 2 ^ E j) (hql : ql ≤ NW n)
    (hKx : Kx j ≤ NW n) (hKx1 : 1 ≤ Kx j) (hqK : ql ≤ Kx j)
    (hb : b - spent sqrC mulC xl n j - P2 sqrC n j + stkR H S'.mem st ≤ b1)
    (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232)) (h5 : S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (habi : Abi s S') (hpc : S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatMul.fn))
    (hrd : S'.mem.readLE (S'.regs 4).toNat 8 = pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h3 : S'.regs 3 = BitVec.ofNat 64 ql) (h1 : S'.regs 1 = BitVec.ofNat 64 qc)
    (h7 : S'.regs 7 = BitVec.ofNat 64 st) (h6 : S'.regs 6 = BitVec.ofNat 64 q) (h8 : S'.regs 8 = BitVec.ofNat 64 ql)
    (h9 : S'.regs 9 = BitVec.ofNat 64 qc)
    (hy0 : S'.mem.readLE ((S'.regs 4).toNat + 8) 8 = xp)
    (hy1 : S'.mem.readLE ((S'.regs 4).toNat + 16) 8 = min (Kx j) xl)
    (hy2 : S'.mem.readLE ((S'.regs 4).toNat + 24) 8 = xc) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S' := by
  subst hpcv
  have hK := sp_K hpre
  have hS' := spN hsp
  obtain ⟨h14, hfs, hx15, hdf⟩ := habi
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnw : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hst : st < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.2.2.2.1; omega
  have hxc : xc < 2 ^ 40 := hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl : xl ≤ 2 ^ 12 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1; omega
  have hkx : min (Kx j) xl ≤ xl := Nat.min_le_right _ _
  have hmc : mulCQ ql (min (Kx j) xl) ≤ mulC (Kx j) (min (Kx j) xl) := hmm _ _ _ hqK
  have hmW : mulW64 ql (min (Kx j) xl) ≤ kM :=
    Nat.le_trans (mulW64_le_X (by omega) (by omega)) hkM1
  have hmid' := hmid
  obtain ⟨-, -, -, ⟨qc40, qp64, -⟩, -, -, hqlc, -, hqc⟩ := hmid'
  unfold Goal
  refine mulCall hap hns hmu H b1 (L := L1) (ra_mi hap hnf i hi) hpc hrd (by rw [hx15, hx0]) (by rw [hdf, hdf0])
    h0 h3 h1 h7 h6 h8 h9 qp64 (by omega) hst qp64 (by omega) (by omega) hy0 hy1 hy2 ?_ ?_
  · exact mulPre_mi hpre hmid hS' h14 hfs rfl hkM hmW hkx (len2' hql (Nat.min_le_left _ _) hKx)
      (bud_ok hb hbud (m := mulC (Kx j) (min (Kx j) xl)) (by simp only [roundCost, P2, P1]; omega) hmc)
  intro s' hpc' hsp' h5' h14' hx15' hreg hpost
  obtain ⟨hfs', hdf', q', ql', qc', e0, e3, e1, hv', hn', hlc', -, hc40', L', b', hLE, hbud', hinv', hlive', hof,
    hstkA, -, hsb, hF', hLF'⟩ := hpost
  rw [h14] at hinv'
  have hqc' : 0 < qc' := by
    rcases hof with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hqc
    · have : 0 < xl := hpre.2.2.2.2.2.2.2.2.2.1
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one
        (Nat.le_min.2 ⟨hKx1, this⟩)) (Nat.le_add_left _ _)) h
  have hq' : q' < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | -
    · exact qp64
    · have := (hlive' hqc').2.2.2; omega
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hmid hS' hkM (by decide) hreg hF' hLF' hLE hinv' hsb.1 hsb.2 hlive' hc40'
    hq' (hof.imp id fun h => h.2) (fun h1 h2 h3 _ => hstkA h1 h2 h3) hlc' hqc'
  have hxv : natVal S'.mem xp (min (Kx j) xl) = natVal s.mem xp (min (Kx j) xl) :=
    x_val hpre hmid.2.1 hkx
  have hv2 : natVal s'.mem q' ql' = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) := by
    rw [hv', hv, hxv]
  have hlen : ql' ≤ 2 * NW n := by
    exact len2 (len_le_mul hn' hv' (x := ql) (y := min (Kx j) xl) (natVal_lt _ _ _) (natVal_lt _ _ _)) hql
      (Nat.min_le_left _ _) hKx
  exact k3 s' j p l c q' ql' qc' L' b' Zv ⟨⟨hpre⟩, hn, by rw [hsp']; exact sp_ret hsp (by omega), h5'.trans h5,
    ⟨h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15, hdf'.trans hdf⟩, ⟨mid2⟩, hj1, hjn, hbud, hcong⟩ hpc'
    (hex _ hsl) (zs_keep hsl (by omega) hzs) (hzv2.trans hzv) hl0 hl e0 e3 e1 hv2 hn' hlen
    (bud_step hb hbud' hmc)

end

end FvModexp.Amd64.ModInv
