import FvModexp.Proofs.Arm64.Exp.W4Fun
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.Lsh

/-!
# `nat.expNNOddMontgomeryWindowSize4` (arm64): `ens` / `sum` (CONVENTIONS §3)

Premises: the live runtime contracts (memclr, memmove, makeslice, growslice, `gcWriteBarrier2`) and `nat.div`'s shape
`ExpHyp.DivHyp` (until asm lands `nat.div`). `nat.lsh` is discharged by asm's `Lsh.ens`, `(*stack).nat` by divmc's
`StackNat.hyp`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpW4

open FvModexp.Arm64.W4En (grE mcE wbE grE_eq mcE_eq wbE_eq fnE)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **window-4** (arm64): `z.expNNOddMontgomeryWindowSize4(stk, x, y, m)` returns `x^y mod m` (see `Pre`/`Post`) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD costD : Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costD)
    (hnsD : ∀ x, nsD.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD ≤ K) (hKL : 4256 ≤ K)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 ylen, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc]
      (Pre R b L K costD zp zc st xp xl xc yp ylen mp n mc) (Post R b L K costD zp zc st xp xl yp ylen mp n) := by
  rw [show names = LibExp.names from rfl, ← LibExp.eq_only, show segAddr Extracted.program fn = fnE by decide]
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hP, hMo, hM1, hslen, hbud⟩ := hpre
  obtain ⟨hbC, hbB, hbA, hbAC, hbP⟩ := buds hbud
  have hc := codeIn_ofImpl_restrict_of_apart hap LibExp.names
  rw [← LibExp.eq_only] at hc
  have hgr' : GrowsliceLiveContract (LibExp.program.link impl) grE 4096 R := by
    rw [← grE_eq]; exact StackNat.GrowsliceLiveContract.of_codeIn hc hgr
  have hmc' : MemclrNoHeapPointersLive (LibExp.program.link impl) mcE 4096 R := by
    rw [← mcE_eq]; exact MemclrNoHeapPointersLive.of_codeIn hc hclr
  have hwb' : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2 := by
    rw [← wbE_eq]; exact WbLiveContract.of_codeIn hc hwb
  refine returns_of_reaches (W4Pro.reaches_mono (W4En.enStep impl hap R hclr hmv hmk
    (StackNat.hyp impl hap R hgr hclr hwb) hgr' hmc' hwb' nsD stkD costD hDiv hnsD hnsW Lsh.names 4256
    (Lsh.ens impl hap R hmk hmv hclr) (MontW.sub_of_all (by decide)) (by decide) ret hret b L K
    (s.regs 28).toNat (s.sp.toNat - 928) st zp zc xp xl xc yp ylen mp n mc s hP hKD hKL hMo hM1 hslen hbC hbB hbA
    hbAC hbP h_pc h_x0 h_x2 h_x3 h_x4 h_x5 h_x6 h_x7 h_x8 h_x10 h_x11 h_x12 h_lr)
    (W4Pro.isReturn_mono fun s' h => ?_))
  obtain ⟨⟨e1, e2, e3, e4⟩, hq⟩ := post_of hP hMo h
  exact ⟨⟨e1, e2, e3, e4⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibExp.names` -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD costD : Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costD)
    (hnsD : ∀ x, nsD.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD ≤ K) (hKL : 4256 ≤ K)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) :=
  CallW.hypSum hap (fun _ h => h) (ens impl hap R hclr hmv hmk hgr hwb nsD stkD costD hDiv hnsD hnsW b L K hKD hKL
    zp zl zc st xp xl xc yp ylen yc mp n mc)

end FvModexp.Arm64.ExpW4
