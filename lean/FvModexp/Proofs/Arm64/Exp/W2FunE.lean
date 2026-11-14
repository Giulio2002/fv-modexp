import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W2Fun
import FvModexp.Proofs.Arm64.Exp.W2Comp
import FvModexp.Proofs.Arm64.Exp.W2XnS
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.Lsh

/-!
# `nat.expNNOddMontgomeryWindowSize2` (arm64): `ens` / `sum` (CONVENTIONS §3)

Premises: the live runtime contracts (memclr, memmove, makeslice, growslice, `gcWriteBarrier2`) and `nat.div`'s shape
`ExpHyp.DivHypL` (until asm exports `nat.div` in that form). `nat.lsh` is discharged by asm's `Lsh.ens`, `(*stack).nat` by divmc's
`StackNat.hyp`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpW2

open FvModexp.Arm64.W2En (grE mcE wbE grE_eq mcE_eq wbE_eq fnE)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **window-2** (arm64): `z.expNNOddMontgomeryWindowSize2(stk, x, y, m)` returns `x^y mod m` (see `Pre`/`Post`) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD ≤ K) (hKL : 4256 ≤ K)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 ylen, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc]
      (Pre R b L K costF zp zc st xp xl xc yp ylen mp n mc) (Post R b L K costF zp zc st xp xl yp ylen mp n) := by
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = fnE by decide]
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hP, hstnz, hMo, hM1, hslen, hbud⟩ := hpre
  have hcs := divCosts_of costF n xl (stLen s.mem st)
  obtain ⟨hbC, hbB, hbA, hbAC, hbP⟩ := buds hbud
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hgr' : GrowsliceLiveContract (LibW.program.link impl) grE 4096 R := by
    rw [← grE_eq]; exact StackNat.GrowsliceLiveContract.of_codeIn hc hgr
  have hmc' : MemclrNoHeapPointersLive (LibW.program.link impl) mcE 4096 R := by
    rw [← mcE_eq]; exact MemclrNoHeapPointersLive.of_codeIn hc hclr
  have hwb' : WbLiveContract (LibW.program.link impl) wbE 4096 R 2 := by
    rw [← wbE_eq]; exact WbLiveContract.of_codeIn hc hwb
  refine returns_of_reaches (W2Pro.reaches_mono (W2En.enStep W2Pro.xnStep W2Pro.rrSpec impl hap R hclr hmv hmk
    (StackNat.hypL impl hap R hgr hclr hwb) hgr' hmc' hwb' nsD stkD (divCost costF n xl (stLen s.mem st)) costF hDiv hnsD hnsW Lsh.names 4256
    (Lsh.ens impl hap R hmk hmv hclr) (MontW.sub_of_all (by decide)) (by decide) ret hret b L K
    (s.regs 28).toNat (s.sp.toNat - 640) st zp zc xp xl xc yp ylen mp n mc s hP hstnz hKD hKL hMo hM1 hslen hcs hbC hbB hbA
    hbAC hbP h_pc h_x0 h_x2 h_x3 h_x4 h_x5 h_x6 h_x7 h_x8 h_x10 h_x11 h_x12 h_lr)
    (W2Pro.isReturn_mono fun s' h => ?_))
  obtain ⟨⟨e1, e2, e3, e4⟩, hq⟩ := post_of hP hMo h
  exact ⟨⟨e1, e2, e3, e4⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibW.names` -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD ≤ K) (hKL : 4256 ≤ K)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) :=
  LibWC.hypSum hap (fun _ h => h) (ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF hDiv hnsD hnsW b L K hKD hKL
    zp zl zc st xp xl xc yp ylen yc mp n mc)

end FvModexp.Arm64.ExpW2
