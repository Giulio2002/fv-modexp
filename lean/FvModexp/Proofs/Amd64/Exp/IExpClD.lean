import FvModexp.Proofs.Amd64.Exp.EvenRowP
import FvModexp.Proofs.Amd64.Exp.SlowCl

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64): the CLOSED callee premises of `IExp.ens` (agent expmc s83; twin of arm64 Exp/IExpClD +
Exp/NHypMono)

* `CPre.mono` / `CPostR0.mono` / `SlowHyp.mono`: an `expNNSlow` summary with need/cost `≤ need'/cost'` is one with
  `need'/cost'` (bigger need = stronger pre, bigger cost = weaker post).
* `needS`/`costS`: the slow slot of `nat.expNN` is shared by `expNNSlow` and the `expNNEven` call (`ExpN.EvH`), so it
  carries the pointwise MAX of the two (`ExpSlow.need` / `EvenRow.nE`, `EvenRow.cS` / `EvenRow.cE`).
* `dhyps`: `ExpN.DHyps` from the live runtime contracts only (div = `DivInst.hyp`, slow = `Q.ExpSlow.slowCl` widened,
  p2 = `P2DRow.hyp 42520`); `evH`: `ExpN.EvH` from `EvenRow.sumP … Q.ExpSlow.hypCl` (frame `stkE 41640 = 43152`, so
  `42248 ≤ K`); `rem` = `RemInst.hyp` (41720).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.NHyp

theorem CPre.mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st : Nat}
    {ins : List (Nat × Nat)} {need cst need' cst' : Nat} {s : State} (hn : need ≤ need') (hc : cst ≤ cst')
    (h : CPre R b L stk above zp zl zc st ins need' cst' s) : CPre R b L stk above zp zl zc st ins need cst s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, by omega, a15, a16, a17, a18, a19, a20, a21,
    by omega, a23, a24, a25⟩

theorem CPostR0.mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zc st v cst cst' : Nat}
    {s s' : State} (hc : cst ≤ cst') (h : CPostR0 R b L stk above zp zc st v cst s s') :
    CPostR0 R b L stk above zp zc st v cst' s s' := by
  obtain ⟨hf, hd, p, l, c, q0, q1, q2, L', b', hof, ⟨hx, hb, hinv⟩, rest⟩ := h
  exact ⟨hf, hd, p, l, c, q0, q1, q2, L', b', hof, ⟨hx, by omega, hinv⟩, rest⟩

theorem SlowHyp.mono {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {need need' : Nat → Nat → Nat → Nat} {cost cost' : Nat → Nat → Nat → Nat → Nat}
    (h : SlowHyp impl R ns stk above need cost) (hn : ∀ a b c, need a b c ≤ need' a b c)
    (hc : ∀ l a b c, cost l a b c ≤ cost' l a b c) : SlowHyp impl R ns stk above need' cost' := by
  intro b L z zl zc st x xl xc y yl yc m ml mc
  refine (h b L z zl zc st x xl xc y yl yc m ml mc).mono (fun s hs => ?_) (fun s s' _ hq => CPostR0.mono (hc _ _ _ _) hq)
  obtain ⟨h0, ⟨h1, h2⟩, h3⟩ := hs
  exact ⟨h0, ⟨CPre.mono (hn _ _ _) (hc _ _ _ _) h1, h2⟩, h3⟩

end FvModexp.Amd64.NHyp

namespace FvModexp.Amd64.IExp

/-- the slow slot's need: `expNNSlow`'s or `expNNEven`'s -/
def needS (xl yl n : Nat) : Nat := max (ExpSlow.need xl yl n) (EvenRow.nE xl yl n)
/-- the slow slot's cost: `expNNSlow`'s or `expNNEven`'s -/
def costS (l xl yl n : Nat) : Nat := max (EvenRow.cS l xl yl n) (EvenRow.cE l xl yl n)

section
variable {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
  (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap hgr hmc hmv hmz hmk hno hwb

/-- **`nat.expNN`'s dispatch callees** (amd64), closed: only the live runtime contracts -/
theorem dhyps {K : Nat} (hK : 42248 ≤ K) :
    ExpN.DHyps impl R K DivInst.divC needS P2D.needP costS EvenRow.cP Q.NatDiv.names 41512 LibW.names 41952
      LibW.names 42520 :=
  have hc : Janus.Contracts.EqHashModel.CodeIn64 (Extracted.program.ofImpl impl) (LibN.program.link impl) := by
    rw [LibN.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibN.names
  { mkN := MakesliceLiveContract64.of_codeIn hc hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr, wb := hwb,
    div := DivInst.hyp impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub, hnsW4 := DivInst.ns_w4,
    hnsW2 := DivInst.ns_w2, hKD := by omega,
    slow := NHyp.SlowHyp.mono (Q.ExpSlow.slowCl hap hgr hmc hmv hmz hmk hwb) (fun _ _ _ => Nat.le_max_left _ _)
      (fun _ _ _ _ => Nat.le_max_left _ _),
    hnsS := EvenRow.libW_libN, hnfS := EvenRow.libW_nfN, hKS := by omega,
    p2 := P2DRow.hyp impl hap R hgr hmc hmv hmk hno hwb 42520 (by decide) (by decide),
    hnsP := EvenRow.libW_libN, hnfP := EvenRow.libW_nfN, hKP := by omega }

/-- **the `expNNEven` call** (amd64), closed: `EvenRow.sumP` with the closed `expNNSlow` -/
theorem evH {K : Nat} (hK : 42248 ≤ K) : ∀ xl yl n, ExpN.EvH impl R K needS costS xl yl n := fun _ _ _ =>
  ⟨ExpEven.stkE 41640, EvenRow.nE, EvenRow.cE,
    EvenRow.sumP impl hap R hgr hmc hmv hmz hmk hno hwb (Q.ExpSlow.hypCl hap hgr hmc hmv hmz hmk hwb)
      EvenRow.libW_libN EvenRow.libW_nfN (by decide),
    by simp only [ExpEven.stkE]; omega, Nat.le_max_right _ _, fun _ => Nat.le_max_right _ _⟩

omit hno in
/-- **`nat.rem`** (amd64), closed -/
theorem rem : NHyp.RemHyp impl R LibRem.names 41720 112 Q.NatRem.need RemInst.remC :=
  RemInst.hyp impl hap R hgr hmc hwb hmk hmv hmz

end

end FvModexp.Amd64.IExp
