import FvModexp.Proofs.Amd64.Exp.W2Fun
import FvModexp.Proofs.Amd64.Nat.StackNat
import FvModexp.Proofs.Amd64.Nat.StackNatX
import FvModexp.Proofs.Amd64.Nat.Lsh

set_option autoImplicit false

/-!
# `nat.expNNOddMontgomeryWindowSize2` (amd64): `ens` (CONVENTIONS §3; agent expmc s59)

Premises: the live runtime contracts (memclr, memmove, makeslice, growslice, `gcWriteBarrier2`) and `nat.div`'s shape
`ExpHyp.DivHypL`. `nat.lsh` is discharged by asm's `Lsh.ens`, `(*stack).nat` by divmc's `StackNat.hypL`. The return
address is only the ABI's (`RetAddr`); `PreD` does not mention it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.ExpW2

open FvModexp.Amd64.W2En (grE mcE wbE grE_eq mcE_eq wbE_eq fnE)

/-- the names of the program window-2 is proved on (`LibW.names`: the exp layer without its callers) -/
abbrev names : List String := LibW.names

theorem rsp_ge {v : BitVec 64} (h : v = BitVec.ofNat 64 (v.toNat - 0x270 + 0x270)) :
    v.toNat - 0x270 + 0x270 = v.toNat := by
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at h1
  have := v.isLt
  omega

theorem rsp_add {v w : BitVec 64} {sp : Nat} (hv : v = BitVec.ofNat 64 (sp + 0x270))
    (hw : w = BitVec.ofNat 64 (sp + 0x278)) (hs : sp - 8 + 0x2e8 ≤ 2 ^ 48) : w = v + 8 := by
  subst hv hw
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8]
  omega

theorem ofNat_self (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem lshW_sub : ∀ x, Lsh.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)
theorem lshW_fn : Lsh.names.contains W2Loop.fn = false := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **window-2** (amd64): `z.expNNOddMontgomeryWindowSize2(stk, x, y, m)` returns `x^y mod m` (see `PreD`/`PostD`) -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W2Loop.fn = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD ≤ K)
    (costD zp zl zc st xp xl xc yp ylen mp n mc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program W2Loop.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc]
      (PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc)
      (PostD R b L K costD zp zc st xp xl yp ylen mp n) := by
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program W2Loop.fn = fnE by decide]
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hPA, hstnz, hMo, hM1, hB, hbS⟩ := hpre
  have hge := rsp_ge hPA.1.1
  have hKL : 4248 ≤ K := Nat.le_trans (by decide) hPA.1.2.2.2.2.2.2.1
  have hP := EPre_of hPA (r := ret) (by rw [hge]; exact h_ret) hret.user
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hgr' : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R := by
    rw [← grE_eq]; exact StackNatX.GrowsliceLiveContract64.of_codeIn' hc hgr
  have hmc' : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R := by
    rw [← mcE_eq]; exact MemclrNoHeapPointersLive64.of_codeIn hc hclr
  have hwb' : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2 := by
    rw [← wbE_eq]; exact WbLiveContract64.of_codeIn hc hwb
  have hE := W2En.enStep hap hclr hmv hmk (StackNat.hypL impl hap R hgr hclr hwb) hgr' hmc' hwb' hDiv hnsD hnsW
    (Lsh.ens impl hap R hmk hmv hclr) lshW_sub lshW_fn hP hstnz hKD hKL hMo hM1 hB hbS (s.regs 3).isLt h_rip h_a0
    (ofNat_self _).symm h_a2 h_a3 h_a4 h_a5 h_a6
  have hsum : Summary (LibW.program.link impl) fnE (fun s0 => s0 = s)
      (fun _ s' => W2En.EnPost R b L K (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x270) st
        (s.regs 5).toNat ret zp zc xp xl xc yp ylen mp n mc costD s s') := by
    intro s0 hpc h0; subst h0
    rw [retAddrOf, h_ret]; exact hE
  refine Summary.returns hsum hret h_rip (by rw [retAddrOf, h_ret]) rfl fun s' h => ?_
  obtain ⟨⟨e4, e5, e14, efs, ex15, edf⟩, hq⟩ := post_of hP hMo hM1 hB h
  exact ⟨⟨rsp_add hPA.1.1 e4 hPA.1.2.2.2.2.2.2.2.2.1.2.2.1, e5.trans (ofNat_self _), e14.trans (ofNat_self _), ex15.trans h_x15.symm⟩,
    fs_eq efs, edf.trans h_df.symm, hq⟩

end FvModexp.Amd64.ExpW2
