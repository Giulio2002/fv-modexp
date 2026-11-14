import FvModexp.Proofs.Amd64.Exp.IExpFun
import FvModexp.Proofs.Amd64.Exp.IExpClD
import FvModexp.Proofs.Amd64.Exp.BudSlow
import FvModexp.Proofs.Amd64.Exp.BudWin
import FvModexp.Proofs.Amd64.Exp.BudP2
import FvModexp.Proofs.Amd64.Exp.BudEven

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64) with the closed callees and the TIGHT-COSTS budget (agent expmc s83; twin of arm64
ExpQ/IExpClQ + BudClQ)

`ensClE`: `IExp.ExpSpecA impl R stk above` from the live runtime contracts (`IExpClD`: `dhyps`, `evH`, `rem`), with
the windows' division bound `BudW.dW` and the budget `hbudCl` proved from the per-term targets (`W = BudQ.opC
(max xl n)`, the release allowance `RunIface.ExpBudget w yl ≥ (512·yl + 128)·W`):
| term | bound | module |
|---|---|---|
| `nat.rem` (`RemInst.remC 0`) | `8 W` | `rem_target` (here) |
| `nat.expNNSlow` (`EvenRow.cS 0`) | `makeCost xl + 8 W + yl·128 W` | BudSlow `Q.ExpSlow.slow_target` |
| `nat.expNNPowerOfTwo` (`EvenRow.cP 0`, `lm < 64 n`) | `8 W + yl·64 W` | BudP2 `Q.BudP2.hp2Q` |
| the windows (`OCost` / `OBud` at `dW`) | `32 W` | BudW `ocost` / `obud` |
| `nat.expNNEven` (`EvenRow.cE 0`) | `120 W + yl·256 W` | `evenT` (BudEven `heven`) |
`nat.expNN` takes ONE branch (path MAX), so each fits the allowance on its own.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp

namespace FvModexp.Amd64.IExp

open FvModexp.Amd64.RunIface (ExpBudget)

/-- `nat.rem`'s bridged cost at the top -/
theorem rem_target {xl n : Nat} (hx : xl ≤ 128) (hn : n ≤ 128) :
    RemInst.remC 0 xl n ≤ 8 * BudQ.opC (max xl n) := by
  have hm1 := BudQ.makeCost_le16 xl
  have hm2 := BudQ.makeCost_le16 (xl + 1)
  have hm3 := BudQ.makeCost_le16 (xl - n + 1)
  have hm4 : makeCost 1 = 40 := by decide
  have hd : Q.drsCQ (xl + 1) n ≤ (if n < 40 then 0 else 560 * (xl + 1) + 88 * n + 1400) := by
    split
    · rw [Q.drsCQ_small (by assumption)]; exact Nat.le_refl _
    · exact Q.drsCQ_le hn (by omega)
  have hW := Q.BudW.opC_eq (max xl n)
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  rw [hW]
  simp only [RemInst.remC, RemInst.brC, Q.NatDiv.costQ, Q.DivLarge.costQ, Q.NatRem.need, stkRes_eq, Nat.zero_add]
  generalize max xl n = M at hxM hnM
  split at hd <;> omega

/-- **the remaining target**: `nat.expNNEven`'s cost at the top (the even branch of `nat.expNN`) -/
def EvenT : Prop :=
  ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
    EvenRow.cE 0 xl yl n ≤ 120 * BudQ.opC (max xl n) + yl * (256 * BudQ.opC (max xl n))

/-- **`EvenT`** (BudEven's `heven`, stated on the unfolded `EvenRow.cE`) -/
theorem evenT : EvenT := fun _ _ _ hx _ hn0 hn => Q.BudE.heven hx hn0 hn

/-- the factor-free allowance at `max xl n` is below `RunIface.ExpBudget` -/
theorem eb_ge {xl yl n : Nat} :
    512 * (yl * BudQ.opC (max xl n)) + 128 * BudQ.opC (max xl n) ≤ ExpBudget (max (max xl yl) n) yl := by
  unfold ExpBudget
  have e1 : BudQ.opC (max xl n) ≤ RunIface.opCost (max (max xl yl) n) := by
    unfold BudQ.opC RunIface.opCost allocCost; omega
  have e2 := Nat.mul_le_mul_left (8 * (64 * yl) + 128) e1
  have e3 : (8 * (64 * yl) + 128) * BudQ.opC (max xl n) = 512 * (yl * BudQ.opC (max xl n)) + 128 * BudQ.opC (max xl n) := by
    rw [Nat.add_mul, show 8 * (64 * yl) = 512 * yl by omega, Nat.mul_assoc]
  omega

theorem yW {yl k W : Nat} : yl * (k * W) = k * (yl * W) := Nat.mul_left_comm _ _ _

/-- **the budget premise of `IExp.ens`** at the closed instances, from `EvenT` -/
theorem hbudCl (he : EvenT) : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + max (RemInst.remC 0 xl n) (makeCost n + max (costS 0 xl yl n) (EvenRow.cP 0 xl yl lm))) ≤
        ExpBudget (max (max xl yl) n) yl ∧
      ExpOdd.OBud DivInst.divC n (Q.BudW.dW xl n) xl yl 0 (ExpBudget (max (max xl yl) n) yl - 24 - makeCost n) ∧
      24 + ExpN.NCost (Q.BudW.dW xl n) RemInst.remC costS EvenRow.cP xl yl n 0 lm ≤
        ExpBudget (max (max xl yl) n) yl := by
  intro xl yl n lm hx hy hn0 hn hlm
  have hR := rem_target hx hn
  have hS := Q.ExpSlow.slow_target (yl := yl) hx hn0 hn
  have hE := he xl yl n hx hy hn0 hn
  have hP := Q.BudP2.hp2Q xl yl n lm hx hy hn0 hn hlm
  have hO := Q.BudW.ocost (yl := yl) hn0 hn hx
  have hB := eb_ge (xl := xl) (yl := yl) (n := n)
  have m1 : makeCost 1 = 40 := by decide
  have mn := BudQ.makeCost_le16 n; have mx := BudQ.makeCost_le16 xl
  have hW := Q.BudW.opC_eq (max xl n)
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hcS : costS 0 xl yl n = max (EvenRow.cS 0 xl yl n) (EvenRow.cE 0 xl yl n) := rfl
  have hcS' : EvenRow.cS 0 xl yl n = Q.ExpSlow.slowBr (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ))
      Q.ExpSlow.needH 0 xl yl n := rfl
  have hOB := Q.BudW.obud (yl := yl) (b := ExpBudget (max (max xl yl) n) yl - 24 - makeCost n) hn0 hn hx
  have hcP : EvenRow.cP 0 xl yl lm = P2D.costP P2W2.costB P2W4.costB 0 xl yl lm := rfl
  simp only [hcS, ExpN.NCost]; rw [hcS', hcP]
  generalize Q.ExpSlow.slowBr (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)) Q.ExpSlow.needH 0 xl yl n = cs at hS ⊢
  generalize P2D.costP P2W2.costB P2W4.costB 0 xl yl lm = cp at hP ⊢
  generalize EvenRow.cE 0 xl yl n = ce at hE ⊢
  generalize RemInst.remC 0 xl n = cr at hR ⊢
  generalize ExpOdd.OCost n xl yl (Q.BudW.dW xl n) 0 = co at hO ⊢
  generalize ExpBudget (max (max xl yl) n) yl = EB at hB hOB ⊢
  generalize BudQ.opC (max xl n) = W at hR hS hE hP hO hB hW hOB
  rw [Nat.mul_left_comm yl 128 W] at hS; rw [Nat.mul_left_comm yl 256 W] at hE; rw [Nat.mul_left_comm yl 64 W] at hP
  generalize yl * W = Y at hS hE hP hB
  refine ⟨?_, hOB (by omega), ?_⟩ <;> omega

/-- the callees' stack needs -/
theorem hneedCl : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    Q.NatRem.need xl n ≤ 2 ^ 16 ∧ needS xl yl n ≤ 2 ^ 16 ∧ P2D.needP xl yl lm ≤ 2 ^ 16 := by
  intro xl yl n lm hx _ _ hn _
  refine ⟨by simp only [Q.NatRem.need]; omega, ?_, by simp only [P2D.needP]; omega⟩
  simp only [needS, EvenRow.nE, ExpEven.needE, ExpSlow.need, Q.NatRem.need, P2D.needP, ExpEven.needO,
    StackNat.rnd, if_pos (show xl ≤ 128 ∧ n ≤ 128 from ⟨hx, hn⟩)]
  omega

set_option maxRecDepth 20000 in
/-- **`(*Int).exp`** (amd64), `ExpSpecA`, every callee closed (premise left: the even-branch budget `EvenT`) -/
theorem ensClE (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (he : EvenT) {K : Nat} (hK : 42248 ≤ K) (hK20 : K + 0x98 ≤ 2 ^ 20) {stk above : Nat} (hKs : K + 0x5d0 ≤ stk)
    (hab : 0x30 ≤ above) : ExpSpecA impl R stk above := by
  have hcI : Janus.Contracts.EqHashModel.CodeIn64 (Extracted.program.ofImpl impl) (LibExpI.program.link impl) := by
    rw [LibExpI.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibExpI.names
  exact ens impl hap R (dhyps hap hgr hmc hmv hmz hmk hno hwb hK) (rem hap hgr hmc hmv hmz hmk hwb)
    EvenRow.libRem_libN EvenRow.libRem_nfN (by omega) (evH hap hgr hmc hmv hmz hmk hno hwb hK) hno hget hput
    (WbLiveContract64.of_codeIn hcI hwb) hKs (by omega) hK20 (by omega) hab hneedCl (costD := fun xl _ n => Q.BudW.dW xl n)
    (hbudCl he)

set_option maxRecDepth 20000 in
/-- **`(*Int).exp`** (amd64), `ExpSpecA`, CLOSED: premises = the 9 live runtime contracts only; any call stack window
`stk ≥ 43736` (`K = 42248`, `K + 0x5d0`), `above ≥ 0x30` -/
theorem ensCl (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {stk above : Nat} (hstk : 43736 ≤ stk) (hab : 0x30 ≤ above) : ExpSpecA impl R stk above :=
  ensClE impl hap R hgr hmc hmv hmz hmk hno hwb hget hput evenT (K := 42248) (by decide) (by decide)
    (by omega) hab

end FvModexp.Amd64.IExp
