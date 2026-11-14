import FvModexp.Proofs.Amd64.Exp.NFunNE
import FvModexp.Proofs.Amd64.Exp.IExpL
import FvModexp.Proofs.Amd64.Exp.IExpA

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64): `nat.expNN` (`ExpN.ensNilF`, on `LibNE`) as a `Summary` of `LibExpI` (agent expmc s76; twin of
`Arm64.IExp.nSum`)

The call of `(*Int).exp` (`z.abs.expNN(nil, x.abs, y.abs, m.abs, false)`, `x = z`) is instantiated in `IExpFun`. Also
`raN_ret`: the call's return point `raN` (inside `(*Int).exp`) is outside `LibNE`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.IExp

set_option maxRecDepth 20000 in
/-- the return point of the `expNN` call (fn+0x4a5, in `(*Int).exp`'s segment) is outside `LibNE` -/
theorem raN_ret (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments LibNE.names).link impl) raN := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg5) (ns := LibNE.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 0x4a5
    (by decide) (by decide)
  simpa only [Extracted.seg5] using this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.expNN` (`ensNilF`) as a `Summary` of `LibExpI` -/
theorem nSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : ExpN.DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains ExpN.fn = false)
    (hKR : stkR ≤ K + 0x388) (hEv : ∀ xl yl n, ExpN.EvH impl R K needS costS xl yl n)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) :
    Summary (LibExpI.program.link impl) fnN
      (fun s => RetAddr ((Extracted.program.onlySegments LibNE.names).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧
        ArgsFrom64 s 0 [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st,
          BitVec.ofNat 64 xp, BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 slow] ∧ s.df = false ∧
        ExpN.PreNF R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        ExpN.PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s') := by
  have hS := Ensures.toSummaryIn (ExpN.ensNilF (costD := costD) impl hap R H hRem hnsR hnfR hKR hEv hno0 hget0 hput0 b L
    zp zl zc st xp xl xc yp yl yc mp n mc slow) (A64.noExit_restrict64 hap LibNE.names) (by simp [numIntRegs])
    (A64.codeIn_restrict_mono64 hap ne_sub)
  rw [← LibExpI.eq_only, show segAddr Extracted.program ExpN.fn = fnN by decide] at hS
  exact hS

end FvModexp.Amd64.IExp
