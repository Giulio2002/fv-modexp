import FvModexp.Proofs.Amd64.Exp.P2W4EP
import FvModexp.Proofs.Amd64.Exp.P2W4Cp5
import FvModexp.Proofs.Amd64.Exp.P2W4Bd
import FvModexp.Proofs.Amd64.Exp.P2W4LO
import FvModexp.Proofs.Amd64.Exp.P2W4X4

set_option autoImplicit false

/-!
# **`nat.expNNPowerOfTwoWindowSize4`** (go-bigmodexpfix nat.go:975-1125), amd64 — the composition (agent divmc s77, port of divmc s74;
amd64 twin of agent infra's `Arm64.P2W4`)

`z.expNNPowerOfTwoWindowSize4(stk, x, y, logM)` with `x` odd, `y > 0`, `2 ≤ logM ≤ 2^13` (and the frame/stack/object
facts `EPre`, the table-call facts `EX`) returns a normalised nat of value `x^y mod 2^logM` (`Exp.p2win_correct`), in
`z`'s array or a fresh one (`FQ` = ABI facts + `NHyp.CPostR`: live set grown, budget `cost`, `StackBackL`, frames,
`ResSep`), no panic, no fault.
Composition: `entP` (entry → reserve → `stk.nat(2w)` → table) → `afterT` (skip-zero loop, `return 1`, first window)
→ `loopKL` (body `bodyKI` = B0…B10, outer step `outerStep`, exit `exitKI`: odd-swap `z.set(zz)`, `norm`, deferred
`stk.restore`, `RET`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the budget of the whole function (Q-form callee costs) -/
@[reducible] def cost (yl lm : Nat) : Nat :=
  cost0 lm + allocCost 8 + 2 * P2Pre.tC lm + 16 * min yl ((lm - 2) / 64 + 1) * bc lm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the whole function from its entry** (continuation-free form: the run returns to `r` with `FQ`) -/
theorem full {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : EX xp xl s) (hKk : P2Pre.K kc ≤ K)
    (hXo : natVal s.mem xp xl % 2 = 1) (hY : 0 < natVal s.mem yp yl) (hbud : cost yl lm ≤ b)
    {zl : Nat} (hzl : zl < 2 ^ 64) (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 st) (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl)
    (h9 : s.regs 9 = BitVec.ofNat 64 xc) (h10 : s.regs 10 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) s
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) (cost yl lm) s) := by
  have hkK : 184 + kc ≤ K := hKk
  have hfs0 : s.fsBase.toNat = fs := hP.1.2.2.1
  have hadx := hX.2.2
  refine entP hap hns hnf hnfP hgr hmc hmv hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT
    (BitVec.ofNat 64 r) _ hP hX hKk (by simp only [cost] at hbud; omega) hzl hpc h0 h3 h1 h7 h6 h8 h9 h10 ?_
  intro s' L3 b3 zzp tp hpc' h4' h14' hx15' hfs' hdf' hAT hb3
  have hfsE : s'.fsBase = s.fsBase := BitVec.eq_of_toNat_eq (hfs'.trans hfs0.symm)
  exact afterT hap hmk hno hmv hP hAT hb3 (by simp only [cost]; omega) hbud (by simp only [cost]; omega) hXo hY
    (s'.regs 5) (fun kk => loopKL (exitKI hap hmv hmk hP hbud) (fun i => outerStep hP i)
      (bodyKI hap hns hnf hsq (by omega) hkS1 hml (by omega) hkM1 htr (by omega) haT hP hXo hadx hbud))
    s' hpc' ⟨h4', h14', rfl, hx15', hfsE, hdf', rfl⟩

end FvModexp.Amd64.P2W4
