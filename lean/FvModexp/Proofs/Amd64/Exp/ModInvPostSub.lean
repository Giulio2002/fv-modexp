import FvModexp.Proofs.Amd64.Exp.ModInvPostS

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `z = z.subMod2N(z, zz, e)` (agent infra s58; twin of
`Arm64/Exp/ModInvPostSub`'s `callSub`)

`callSub`: at `subMod2N`'s entry (`RSP_c = RSP - 232`, the return address `pcv` at `[RSP_c]`, `z = (p, l, c)` in
`RAX, RBX, RCX` and `RDI, RSI, R8`, `zz = (q, ql, qc)` in `R9, R10, R11`, `e` at `RSP_c + 8`, stored by the caller),
with the round facts `Mid` at the entry memory: the call through `SubMod2N.fullG` (a `Summary` on `LibW`); the
continuation gets the round facts at the return (`z` kept in place: `cap z ≥ ⌈n/64⌉ + 1 ≥ ⌈e/64⌉ + 1`), its value,
`zz` unchanged, and the budget step.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem subW_le {e n c : Nat} (he : e ≤ n) (hc : NW n + 1 ≤ c) : SubMod2N.W e + 1 ≤ c := by
  simp only [SubMod2N.W, NW] at hc ⊢; omega

theorem nw2_le {n l : Nat} (hn : n ≤ 2 ^ 15) (hl : l ≤ NW n + 2) : l ≤ 2 ^ 12 := by
  simp only [NW] at hl; omega

theorem nw_le {n l : Nat} (hn : n ≤ 2 ^ 15) (hl : l ≤ NW n) : l ≤ 2 ^ 12 := by
  simp only [NW] at hl; omega

theorem regs_of {r : W64} {v : Nat} (h : r.toNat = v) : r = BitVec.ofNat 64 v := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callSub {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains SubMod2N.fn = false) {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R) {kc : Nat}
    (hkc : SubMod2N.K ≤ kc) {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    {p l c q ql qc : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {S' : State}
    (hmid : Mid R kc L s zp zc st xp xl xc n S'.mem L1 b1 p l c q ql qc) {e : Nat} (he1 : 1 ≤ e) (he : e ≤ n)
    (hl : l ≤ NW n + 2) (hql : ql ≤ NW n) (hnz : NatNorm S'.mem p l) (hnq : NatNorm S'.mem q ql)
    (hb : SubMod2N.cost e ≤ b1) {pcv : Nat} (hpcv : pcv < 2 ^ 47)
    (hsp : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 232)) (h5 : S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (habi : Abi s S') (hpc : S'.rip = BitVec.ofNat 64 6215840) (hrd : S'.mem.readLE (S'.regs 4).toNat 8 = pcv)
    (hen : S'.mem.readLE ((S'.regs 4).toNat + 8) 8 = e)
    (h0 : S'.regs 0 = BitVec.ofNat 64 p) (h3 : S'.regs 3 = BitVec.ofNat 64 l) (h1 : S'.regs 1 = BitVec.ofNat 64 c)
    (h7 : S'.regs 7 = BitVec.ofNat 64 p) (h6 : S'.regs 6 = BitVec.ofNat 64 l) (h8 : S'.regs 8 = BitVec.ofNat 64 c)
    (h9 : S'.regs 9 = BitVec.ofNat 64 q) (h10 : S'.regs 10 = BitVec.ofNat 64 ql)
    (h11 : S'.regs 11 = BitVec.ofNat 64 qc) {ret : W64} {Qp : State → Prop}
    (K : ∀ (s' : State) (l' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 pcv →
      s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) → s'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) →
      Abi s s' → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c →
      Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l' c q ql qc →
      natVal s'.mem p l' = Exp.subMod2N (natVal S'.mem p l) (natVal S'.mem q ql) e → NatNorm s'.mem p l' →
      natVal s'.mem q ql = natVal S'.mem q ql → NatNorm s'.mem q ql →
      b1 - SubMod2N.cost e ≤ b' → SlotsKept s S'.mem s'.mem → stCap s'.mem st = stCap S'.mem st →
      ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S' Qp := by
  have hK := sp_K hpre
  have hS' := spN hsp
  obtain ⟨h14, hfs, hx15, hdf⟩ := habi
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨op, hone⟩, -⟩ := hpre'
  have hmid' := hmid
  obtain ⟨-, hrt, hz, -, -, hlc, hqlc, hnc, -⟩ := hmid'
  have hz' := hz
  obtain ⟨hc40, hp64, -⟩ := hz'
  have hW : SubMod2N.W e + 1 ≤ c := subW_le he hnc
  refine subCall hap hns hnf hkT haT htr hsub hadd hgr b1 (L := L1) (op := op) (n := e) hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 ?_ ?_
  · exact subPre_mi hpre hkc hmid hone hS' h14 hfs rfl he1 (Nat.le_trans he hn2) (nw2_le hn2 hl) (nw_le hn2 hql)
      hnz hnq ⟨hb, fun h => absurd hW (by omega)⟩ (by rw [hrd]; exact hpcv) hen (by rw [hx15, hx0])
      (by rw [hdf, hdf0])
  intro s' hr e1 e2 e3 e4 hreg hpost
  obtain ⟨hfs', hdf', p', l', c', f0, f1, f2, hv, hn', hlc', hc40', L', b', hLE, -, hbud, hinv, hlive, -, hF, hLF,
    hkeep⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hkeep hW
  rw [h14] at hinv
  obtain ⟨hF2, hLF2, hsb, hain, -, se2⟩ := nostk hpre hrt hS' hkc (by decide) hz hF hLF hLE
  obtain ⟨mid2, hqv, hsl⟩ := after_z hpre hmid hS' hkc (by decide) hreg hF2 hLF2 hLE hinv hsb hain hlive hc40' hp64
    (Or.inl ⟨rfl, rfl⟩) (fun h => absurd ⟨rfl, rfl⟩ h) hlc' hnc
  refine K s' l' L' b' (by rw [hr]; simp only [retAddrOf, hrd]) (by rw [e1]; exact sp_ret hsp (by omega))
    (e2.trans h5) ⟨e3.trans h14, hfs'.trans hfs, e4.trans hx15, hdf'.trans hdf⟩ (regs_of f0) (regs_of f1)
    (regs_of f2) mid2 hv hn' (hqv ql hqlc) (norm_keep hqv hqlc hnq) (hbud (Nat.le_of_succ_le hW)) hsl se2

end FvModexp.Amd64.ModInv
