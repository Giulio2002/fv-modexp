import FvModexp.Proofs.Amd64.Exp.P2PreE
import FvModexp.Proofs.Amd64.Exp.P2PreE1
import FvModexp.Proofs.Amd64.Exp.P2PreF
import FvModexp.Proofs.Amd64.Exp.P2PreX
import FvModexp.Proofs.Amd64.Exp.P2PreX1
import FvModexp.Proofs.Amd64.Exp.P2PreXT
import FvModexp.Proofs.Amd64.Exp.P2PreRnd
import FvModexp.Proofs.Amd64.Exp.P2PreDefE
import FvModexp.Proofs.Amd64.Exp.P2PreInvPP
import FvModexp.Proofs.Amd64.Exp.P2PreInvPN
import FvModexp.Proofs.Amd64.Exp.P2PreInvNP
import FvModexp.Proofs.Amd64.Exp.P2PreInvNN
set_option autoImplicit false

/-!
# **`buildPrecomputationWindowModPower2`** (go-bigmodexpfix nat.go:856-899), amd64 — the summary (agent divmc s65;
twin of infra's `Arm64/Exp/P2Pre`)

`buildPrecomputationWindowModPower2(stk, powers, windowSize, logM, x)` with `windowSize ∈ {2, 4}`,
`len(powers) = 2^windowSize`, `2 ≤ logM ≤ 2^13`, `x` normalised: every `powers[j]` (`j < len`) is a normalised nat of at
most `w = ⌈logM/64⌉` words holding `Exp.p2Pow logM X j` (`= X^j mod 2^logM`), stored in the scratch nat
`buf = stk.nat((len+1) w)` at `buf + 8 j w` (cap `w`); the stack grows by `rnd((len+1) w)` words; only `powers`, the
stack object's writable parts, the window and runtime memory are written; no panic, no fault (`Post`, P2PreDefs).
Composition: `entry` → `callSN` (`stk.nat`) → `fill_all` (fill loop) → `exitF` (`powers[0] = 1`) → `jX1` / `callTrX`
(`trunc(x)`) → `segT` (→ `HeadJ 2`) → `head_all` (main loop, `round`, return).
Callee premises: divmc's `(*stack).nat` (`StackNatX.HypQ`), `nat.sqr` / `nat.mul` (`SqrE` / `Q.DivRec.MulHypQE`), asm's
`nat.trunc` (`Trunc.Hyp2`), the live `runtime.memmove` and `runtime.gcWriteBarrier2` contracts.
`PreE` = the internal `Pre` without its last three conjuncts (the return-address bound, `X15 = 0`, `DF = 0`), which the
call setup provides: the statement puts no constraint on the return address.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)
set_option maxRecDepth 20000 in
/-- the whole function from its entry, as a `Summary` on the exp layer's program -/
theorem full {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :
    Summary (LibW.program.link impl) 0x5e8900
      (fun s => s.regs 0 = BitVec.ofNat 64 st ∧ s.regs 3 = BitVec.ofNat 64 pw ∧ s.regs 1 = BitVec.ofNat 64 pl ∧
        s.regs 7 = BitVec.ofNat 64 pc ∧ s.regs 6 = BitVec.ofNat 64 ws ∧ s.regs 8 = BitVec.ofNat 64 lm ∧
        s.regs 9 = BitVec.ofNat 64 x ∧ s.regs 10 = BitVec.ofNat 64 xl ∧ s.regs 11 = BitVec.ofNat 64 xc ∧
        Pre R kc b L st pw pl ws lm x xl s)
      (fun s s' => GoalQ R kc b L st pw pl lm x xl s s') := by
  intro s hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
  have hpl := pl_facts hpre
  exact entry impl R kc b L st pw pl pc ws lm x xl xc s (by omega) hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 hpre
    (callSN hap hns hnf hsn hkN haN (fill_all hwb hkc (exitF hmv hwb hkc (jX1 hap hns hnf htr hkT haT hkc
      (segT hwb hkc (head_all hap hns hnf hsq hkS1 hkS hml hkM1 hkM htr hkT haT hwb hkc hpl.2.2 (by omega)))))
      pl 0 (by omega)))

def names : List String := LibW.names

theorem preE_inv {R : RtInv} {kc b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} (p : Janus.Amd64.Program) (e : Nat) (args : List W64) :
    Ensures.SetRetInv p e args (PreE R kc b L st pw pl ws lm x xl) := by
  intro s ret hs hret hp
  by_cases h1 : 0 < xl <;> by_cases h2 : 0 < stCap s.mem st
  · exact preE_setRet_pp s ret hs hret h1 h2 hp
  · exact preE_setRet_pn s ret hs hret h1 h2 hp
  · exact preE_setRet_np s ret hs hret h1 h2 hp
  · exact preE_setRet_nn s ret hs hret h1 h2 hp

set_option maxRecDepth 20000 in
/-- **`buildPrecomputationWindowModPower2`** (amd64): the table `powers[j] = X^j mod 2^logM` (`Exp.p2Pow`), see the
module doc; `Post` (P2PreDefs) states the values, the stack growth, the scratch nat and the frames. -/
theorem ens {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 st, BitVec.ofNat 64 pw, BitVec.ofNat 64 pl, BitVec.ofNat 64 pc, BitVec.ofNat 64 ws,
        BitVec.ofNat 64 lm, BitVec.ofNat 64 x, BitVec.ofNat 64 xl, BitVec.ofNat 64 xc]
      (PreE R kc b L st pw pl ws lm x xl) (Post R kc b L st pw pl lm x xl) := by
  refine Ensures.of_old (preE_inv _ _ _) ?_
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hmvL : MemmoveLive64 (LibW.program.link impl) mvE 4096 R := by
    rw [← mvE_eq]; exact MemmoveLive64.of_codeIn hc hmv
  have hwbL : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2 := by
    rw [← wbE_eq]; exact WbLiveContract64.of_codeIn hc hwb
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = 0x5e8900 by decide]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full hap hns hnf hmvL hwbL hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT
    b L st pw pl pc ws lm x xl xc) hret
    (by rw [h_rip]) (by rw [retAddrOf, h_ret])
    ⟨h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6, h_a7, h_a8, pre_of hpre (by rw [h_ret]; exact hret.user) h_x15 h_df⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibW.names` -/
def sum {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :=
  hypSumW hap (fun _ h => h) (by simp [numIntRegs])
    (ens hap hns hnf hmv hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT b L st pw pl pc ws lm x xl xc)

end FvModexp.Amd64.P2Pre
