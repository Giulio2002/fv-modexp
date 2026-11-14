import FvModexp.Proofs.Amd64.Exp.CalleeInstE
import FvModexp.Proofs.Amd64.Exp.CalleeInstR
import FvModexp.Proofs.Amd64.Exp.EvSum
import FvModexp.Proofs.Amd64.Exp.EvMiEns
import FvModexp.Proofs.Amd64.Exp.NMidE
import FvModexp.Proofs.Amd64.Exp.EvCD

set_option autoImplicit false

/-!
# **`nat.expNNEven`** amd64 — `EvInst`: asm's `ExpEven.full` with every callee summary plugged in (agent divmc s78)

* `miEQ`: infra's `ModInv.ens` (through asm's `miEns_of`) with the `CalleeInstQ` instances on `nsQ`, frame
  `kc = mulWX64`, costs `sqrCQ` / `mulCQ`.
* `fullI`: `ExpEven.full` with `(*stack).nat` (`sl`), `nat.lsh` (`lh`), `nat.rsh` (asm's `rh`), `nat.mul` (`mu`, window
  `mulWX64`), `nat.trunc` (`t0`; `tr` inside `subMod2N`/`modInv`), `nat.add` (`a0`; `ad` inside), `nat.sub` (`sb`),
  `nat.subMod2N` (`se`), `modInv` (`miEQ`) — all on `nsQ`; frame depth `stkE KN`.
* `evInst`: the closed `∀ xl yl n, ExpN.EvH impl R K needS0 costS0 xl yl n` consumed by expmc's `ensNilF` (`hEv`).
Remaining premises: the Janus runtime contracts (on `Extracted.program.ofImpl impl`), expmc's `ExpNNHypNE1` for
EVERY `costD` (as `ExpN.hypNE1` gives it) at the closed division cost `DivInst.divC`, its monotonicity / budget facts
(`hNB`/`hNC` at the level-dependent division bound `cDE`), and the slot bounds `stkE KN ≤ K + 0x388`,
`needE ≤ needS0`, `costE ≤ costS0`.
* asm s73 (cost shape, coordinator DECISION "[asm s72]"): the inner `nat.expNN` calls are instantiated at
  `costD := cDE xl lm lv = EvCD.cD (needO xl lm) lv (max (2·lm+1) xl) lm` (`lm` = the call's modulus length, `lv` =
  its stack level) instead of one constant `costD` with `costF ≤ costD` on all levels `≤ 2^16` (≥ 1.1·10^7).
  `divC_cDE` is `ExpEven.full`'s `hFD`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Amd64.CalleeInstQ
open Janus.Contracts.EqHashModel (CodeIn64)

namespace FvModexp.Amd64.ExpEven

/-- the level-dependent division bound of the inner `nat.expNN` call with modulus length `a` at stack level `l` -/
def cDE (x a l : Nat) : Nat := cD (needO x a) l (max (2 * a + 1) x) a

/-- `DivInst.divC ≤ cDE` on every window division of that call (`ExpEven.full`'s `hFD`) -/
theorem divC_cDE : ∀ x lm lv l' a, x ≤ 128 → lm ≤ 128 → l' ≤ lv + needO x lm → (a ≤ 2 * lm + 1 ∨ a ≤ x) →
    DivInst.divC l' a lm ≤ cDE x lm lv := by
  intro x lm lv l' a hx hlm hl ha
  have hA : a ≤ max (2 * lm + 1) x := by
    rcases ha with h | h
    · exact Nat.le_trans h (Nat.le_max_left _ _)
    · exact Nat.le_trans h (Nat.le_max_right _ _)
  exact divC_le _ _ _ _ _ _ hl hA (Nat.max_le.2 ⟨by omega, by omega⟩) hlm

/-- `nat.expNNEven`'s frame depth for the inner `nat.expNN` window `KN` -/
@[reducible] def stkE (KN : Nat) : Nat := max (42816 + 0x150) (KN + 0x498 + 0x150)

variable {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hgr hmc hmv hmk hwb in
/-- `ModInv.ens` with every callee proved: `MiEns` at `kc = mulWX64`, costs `sqrCQ` / `mulCQ` -/
theorem miEQ : MiEns impl R mulWX64 sqrCQ mulCQ :=
  miEns_of hap sub sub sub sub nfM nfM nfM nfM nfS hmk (by decide) (sq hap hgr hmc hmv hmk hwb mulWX64)
    (Nat.le_refl _) (by decide) (tr hap hmv hmk) (by decide) (by decide) (mu hap hgr hmc hmv hmk hwb mulWX64)
    (Nat.le_refl _) (Nat.le_refl _) (lh hap hmc hmv hmk) (by decide) (by decide) (sb hap hmv hmk) (ad hap hmv hmk)
    hgr (fun _ _ h => sqrCQ_mono h) (fun _ _ h => sqrCQ_mono h) (fun _ _ _ h => mulCQ_mono h (Nat.le_refl _))

include hgr hmc hmv hmz hmk hwb in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNEven`** (amd64) with every callee summary except the inner `nat.expNN` (`ExpNNHypNE1`) plugged in -/
theorem fullI {KN : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : ∀ costD, EvenHyp.ExpNNHypNE1 impl R KN DivInst.divC costD needR costR needS needP costS costP)
    (hKN : 41640 ≤ KN) (hKN2 : KN + 0x498 ≤ 2 ^ 20)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      NBudO (cDE x a l) costR costS costP x y a l k ≤ bU x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost (cDE x a l) costR costS costP x y a l k ≤ cU x y a' l' k') :
    EvenSum impl R (stkE KN) 0x70 (needE needR needS needP) (costE bU cU sqrCQ mulCQ) := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibNE.program.link impl) := by
    rw [LibNE.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibNE.names
  have hmvE : MemmoveLive64 (LibNE.program.link impl) mvE 4096 R := by
    rw [show mvE = cA "runtime.memmove" by decide]; exact MemmoveLive64.of_codeIn hc hmv
  have hmzE : MemmoveZeroLive64 (LibNE.program.link impl) mvE 4096 R := by
    rw [show mvE = cA "runtime.memmove" by decide]; exact MemmoveZeroLive64.of_codeIn hc hmz
  have hmkE : MakesliceLiveContract64 (LibNE.program.link impl) mkE 4096 R := by
    rw [show mkE = cA "runtime.makeslice" by decide]; exact MakesliceLiveContract64.of_codeIn hc hmk
  have hmW : mulWX64 = 30792 := rfl
  exact full hap subNE nfE (sl hap hgr hmc hwb) (by decide) (lh hap hmc hmv hmk) (by decide) (rh hap hmv hmk)
    (by decide) hE hKN (by omega) hmvE hmzE hmkE (se hap hgr hmv hmk) sub sub sub sub nfM nfM nfM nfM nfS hmk
    (by decide) (sq hap hgr hmc hmv hmk hwb mulWX64) (Nat.le_refl _) (by decide) (tr hap hmv hmk) (by decide)
    (by decide) (mu hap hgr hmc hmv hmk hwb mulWX64) (Nat.le_refl _) (Nat.le_refl _) (lh hap hmc hmv hmk)
    (by decide) (by decide) (sb hap hmv hmk) (ad hap hmv hmk) hgr (fun _ _ h => sqrCQ_mono h)
    (fun _ _ h => sqrCQ_mono h) (fun _ _ _ h => mulCQ_mono h (Nat.le_refl _)) (fun _ _ _ _ h1 h2 => mulCQ_mono h1 h2)
    (mu hap hgr hmc hmv hmk hwb mulWX64) (Nat.le_refl _) (t0 hap hmv hmk) (a0 hap hmv hmk) hRm hSm hPm hNB hNC divC_cDE
    (by simp only [stkE]; omega) (by simp only [stkE]; omega)
    ⟨by simp only [stkE]; omega, by simp only [stkE]; omega, by simp only [stkE]; omega,
      by simp only [stkE]; omega, by simp only [stkE]; omega, by simp only [stkE]; omega⟩

include hgr hmc hmv hmz hmk hwb in
/-- **the closed even-call premise** of expmc's `ExpN.ensNilF` (`hEv`): for every slot `K` / `needS0` / `costS0`
that covers `nat.expNNEven`'s frame, need and cost -/
theorem evInst {KN : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : ∀ costD, EvenHyp.ExpNNHypNE1 impl R KN DivInst.divC costD needR costR needS needP costS costP)
    (hKN : 41640 ≤ KN) (hKN2 : KN + 0x498 ≤ 2 ^ 20)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      NBudO (cDE x a l) costR costS costP x y a l k ≤ bU x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost (cDE x a l) costR costS costP x y a l k ≤ cU x y a' l' k')
    {K : Nat} (hK : stkE KN ≤ K + 0x388) {needS0 : Nat → Nat → Nat → Nat} {costS0 : Nat → Nat → Nat → Nat → Nat}
    (hnS : ∀ xl yl n, needE needR needS needP xl yl n ≤ needS0 xl yl n)
    (hcS : ∀ l xl yl n, costE bU cU sqrCQ mulCQ l xl yl n ≤ costS0 l xl yl n) :
    ∀ xl yl n, ExpN.EvH impl R K needS0 costS0 xl yl n := fun xl yl n =>
  ⟨stkE KN, needE needR needS needP, costE bU cU sqrCQ mulCQ,
    fullI hap hgr hmc hmv hmz hmk hwb hE hKN hKN2 hRm hSm hPm hNB hNC, hK, hnS xl yl n, fun l => hcS l xl yl n⟩

end FvModexp.Amd64.ExpEven
