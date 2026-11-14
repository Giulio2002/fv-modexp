import FvModexp.Proofs.Amd64.Exp.IExpFun
import FvModexp.Proofs.Amd64.Nat.RowLink

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64) on the Run extraction, PREMISE FORM (agent expmc s77; staging for the amd64 IExpRow)

`correctnessP` = `IExp.ens` moved to `Extracted.program.link impl` (`Ensures.full64`), with the write-barrier contract
taken on `Extracted.program.ofImpl impl` like the other live contracts. Pre = `RunIface.ExpSpec`'s pre ∧ `IExp.ExpA`.
The callee shapes (`DHyps`, `RemHyp`, `EvH`) are still PREMISES: this is NOT a release row (the Janus audit refuses
non-contract hypotheses); the row `IExpRow` replaces them by the closed amd64 instances once they exist (needed: an amd64
`nat.expNNSlow` summary for `SlowHyp`, divmc's P2W4 + asm's P2D for `P2Hyp`, asm/infra's `EvH` instance and the amd64
`RemHyp` instance) and adds `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.RunIface
open Janus.Contracts.EqHashModel (CodeIn64)

namespace FvModexp.Amd64.IExpRowP

/-- `(*Int).exp`'s symbol -/
abbrev fnExpL : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).exp"

/-- **`(*Int).exp`** (amd64), premise form: `z.exp(z, y, m, false)` (`m > 0`, operands of at most 128 words) returns
`z` holding `z ^ y mod m` (`IntPost`), for every runtime meeting the live contracts, given `nat.expNN`'s callee
shapes -/
theorem correctnessP (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : ExpN.DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains ExpN.fn = false)
    (hKR : stkR ≤ K + 0x388) (hEv : ∀ xl yl n, ExpN.EvH impl R K needS costS xl yl n)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hwb0 : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {stk above : Nat} (hK : K + 0x5d0 ≤ stk) (hK4 : 41640 ≤ K) (hK20 : K + 0x98 ≤ 2 ^ 20) (h1138 : 0x1138 ≤ stk)
    (hab : 0x30 ≤ above)
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      needR xl n ≤ 2 ^ 16 ∧ needS xl yl n ≤ 2 ^ 16 ∧ needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + max (costR 0 xl n) (makeCost n + max (costS 0 xl yl n) (costP 0 xl yl lm))) ≤
        ExpBudget (max (max xl yl) n) yl ∧
      ExpOdd.OBud costF n (costD xl yl n) xl yl 0 (ExpBudget (max (max xl yl) n) yl - 24 - makeCost n) ∧
      24 + ExpN.NCost (costD xl yl n) costR costS costP xl yl n 0 lm ≤ ExpBudget (max (max xl yl) n) yl)
    (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program fnExpL) [z, z, y, mm, 0#64]
      (fun s => (IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R s.mem (win s stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 wbA 4 ∧ ModX s.mem z.toNat) ∧
        IExp.ExpA s.mem)
      (fun s s' => s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s') := by
  have hcI : CodeIn64 (Extracted.program.ofImpl impl) (LibExpI.program.link impl) := by
    rw [LibExpI.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibExpI.names
  have hE := IExp.ens impl hap R H hRem hnsR hnfR hKR hEv hno0 hget0 hput0 (WbLiveContract64.of_codeIn hcI hwb0)
    hK hK4 hK20 h1138 hab hneed hbud b L z y mm
  exact Ensures.full64 hap (by simp [numIntRegs]) hE

end FvModexp.Amd64.IExpRowP
