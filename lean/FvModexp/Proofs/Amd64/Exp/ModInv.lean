import FvModexp.Proofs.Amd64.Exp.ModInvEntry
import FvModexp.Proofs.Amd64.Exp.ModInvSmall
import FvModexp.Proofs.Amd64.Exp.ModInvRt
import FvModexp.Proofs.Amd64.Exp.ModInvMkZZ
import FvModexp.Proofs.Amd64.Exp.ModInvLoop

set_option autoImplicit false

/-!
# **`nat.modularInverseModPowerOfTwo`** (go-bigmodexpfix nat.go:1287-1341), amd64 — the summary (agent infra s58;
twin of `Arm64/Exp/ModInv`)

`z.modularInverseModPowerOfTwo(stk, x, n)` (`x` normalised and odd, `1 ≤ n ≤ 2^15`, `cap z > 0`, `z` apart from `x`)
returns a normalised nat holding `Exp.modularInverseModPowerOfTwo X n` (`x⁻¹ mod 2^n`), in `z`'s array or a fresh one.
Paths: `n ≤ 64` (`ModInvSmall`), else `z.make` (reuse `make` / allocating `alloc`), `zz.make` (`mkzz`) and the Hensel
loop (`loop`). Callee premises: divmc's amd64 `Q.NatSqr.ens` shape (`SqrE`, window `kS`), asm's `Q.DivRec.MulHypQE`
(window `kM ≥ mulWX64`), `Trunc.Hyp2`, `Lsh.Hyp2`, `nat.subMod2N` (verified: `SubMod2N.fullG`, premises `Trunc.Hyp2` /
`SubHypR0` / `AddHypR` / growslice), the live `runtime.makeslice` contract. `X15 = 0` and `DF = 0` come from the call
setup (`CallSetup.zero` / `.df`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
  FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
/-- the whole function from its entry, as a `Summary` on the exp layer's program (internal budget form) -/
theorem full {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {nsS nsT nsM nsL : List String} (hnsS : ∀ x, nsS.contains x = true → LibW.names.contains x = true)
    (hnsT : ∀ x, nsT.contains x = true → LibW.names.contains x = true)
    (hnsM : ∀ x, nsM.contains x = true → LibW.names.contains x = true)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnfS : nsS.contains fn = false) (hnfT : nsT.contains fn = false) (hnfM : nsM.contains fn = false)
    (hnfL : nsL.contains fn = false) (hnfTS : nsT.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (cA "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : SubMod2N.K ≤ kc)
    {kS : Nat} (hsq : SqrE impl R nsS kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R nsT stkT aboveT) (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R nsM kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R nsL stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    (hsm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a') (hsm' : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c)
    (H b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Summary (LibW.program.link impl) 0x5ea8c0
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧
        s.regs 7 = BitVec.ofNat 64 st ∧ s.regs 6 = BitVec.ofNat 64 xp ∧ s.regs 8 = BitVec.ofNat 64 xl ∧
        s.regs 9 = BitVec.ofNat 64 xc ∧ s.regs 10 = BitVec.ofNat 64 n ∧ s.xmm 15 = 0 ∧ s.df = false ∧
        Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ Post R kc H sqrC mulC b L zp zc st xp xl n s s') := by
  intro s hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, hx0, hdf0, hpre⟩
  have hkc4 : 4096 ≤ kc := by
    have : 4096 ≤ SubMod2N.K := by decide
    omega
  have kL : J2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s :=
    loop hap hnsS hnsT hnsM hnsL hnfS hnfT hnfM hnfL hnfTS hkc hsq hkS hkS1 htr hkT haT hmu hkM hkM1 hls hkL haL hsub hadd hgr hsm hsm' hmm hx0 hdf0
  have kM := mkzz impl R hmk kc H _ _ b L zp zl zc st xp xl xc n s hkc4 kL
  exact entry impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s hpc h0 h3 h1 h7 h6 h8 h9 h10 hpre
    (small impl R kc H _ _ b L zp zl zc st xp xl xc n s)
    (make impl R kc H _ _ b L zp zl zc st xp xl xc n s kM (alloc impl R hmk kc H _ _ b L zp zl zc st xp xl xc n s hkc4 kM))

/-- the exp layer's functions (the program of `ens`) -/
def names : List String := LibW.names

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`nat.modularInverseModPowerOfTwo`** (amd64), Q-form: `z.modularInverseModPowerOfTwo(stk, x, n)` returns a
normalised nat holding `x⁻¹ mod 2^n` (`Exp.modularInverseModPowerOfTwo`), in `z`'s array or a fresh one; writes only
`z`'s array, the window, the stack object's writable parts and runtime memory; no panic, no fault; `DF` and `fsBase`
kept. Budget: one reserve level `H ≥ stLen + D n`, cost `cost sqrC mulC xl n + stkR H s.mem st`, refund
`stkR H s'.mem st`. -/
theorem ens {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {nsS nsT nsM nsL : List String} (hnsS : ∀ x, nsS.contains x = true → LibW.names.contains x = true)
    (hnsT : ∀ x, nsT.contains x = true → LibW.names.contains x = true)
    (hnsM : ∀ x, nsM.contains x = true → LibW.names.contains x = true)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnfS : nsS.contains fn = false) (hnfT : nsT.contains fn = false) (hnfM : nsM.contains fn = false)
    (hnfL : nsL.contains fn = false) (hnfTS : nsT.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : SubMod2N.K ≤ kc)
    {kS : Nat} (hsq : SqrE impl R nsS kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R nsT stkT aboveT) (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R nsM kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R nsL stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    (hsm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a') (hsm' : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c)
    (H B : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (PreQ R kc H sqrC mulC B L zp zl zc st xp xl xc n) (PostQ R kc H sqrC mulC B L zp zc st xp xl n) := by
  refine Ensures.of_old (fun s ret hs hret hp => ?_) ?_
  · -- the precondition's `∃ op` (the `natOne` limb pointer) is pulled out first; the setRet closer then sees `NatOne … op …`
    simp only [FvModexp.Amd64.ModInv.PreQ, FvModexp.Exp.B, FvModexp.Amd64.CallEnv, FvModexp.Amd64.ModInv.A, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.gA, FvModexp.stkWs, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.natVal, FvModexp.Amd64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.Amd64.Q.NatSqr.StkSep, FvModexp.stkR, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.ModInv.OneIn, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.stW, FvModexp.stCap, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.Q.NatSqr.guard, FvModexp.Amd64.Q.BasicSqr.freeP, FvModexp.Amd64.Q.BasicSqr.freeN, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.Q.NatSqr.tls, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.EvenHyp.natOneA] at hp ⊢
    simp only [← exists_and_left, ← exists_and_right] at hp ⊢
    obtain ⟨op, hp⟩ := hp
    refine ⟨op, ?_⟩
    janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ModInv.PreQ, FvModexp.Exp.B, FvModexp.Amd64.CallEnv, FvModexp.Amd64.ModInv.A, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.gA, FvModexp.stkWs, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.natVal, FvModexp.Amd64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.Amd64.Q.NatSqr.StkSep, FvModexp.stkR, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.ModInv.OneIn, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.stW, FvModexp.stCap, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.Q.NatSqr.guard, FvModexp.Amd64.Q.BasicSqr.freeP, FvModexp.Amd64.Q.BasicSqr.freeN, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.Q.NatSqr.tls, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.EvenHyp.natOneA]
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hmkL := MakesliceLiveContract64.of_codeIn hc hmk
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = 0x5ea8c0 by decide]
  intro ret hret s hs hpre
  have hdf := hs.df
  janus64_intro hs
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := by rw [h_ret]; exact hret.user
  refine Summary.returns (full hap hnsS hnsT hnsM hnsL hnfS hnfT hnfM hnfL hnfTS hmkL hkc hsq hkS hkS1 htr hkT haT hmu hkM hkM1 hls hkL haL hsub
    hadd (SubMod2N.growslice_of_codeIn hc hgr) hsm hsm' hmm H (B - stkR H s.mem st) L zp zl zc st xp xl xc n) hret
    (by rw [h_rip]) (by rw [retAddrOf, h_ret])
    ⟨h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6, h_a7, h_x15, hdf, pre_of_Q hpre hra⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, post_of_Q hq⟩

end FvModexp.Amd64.ModInv
