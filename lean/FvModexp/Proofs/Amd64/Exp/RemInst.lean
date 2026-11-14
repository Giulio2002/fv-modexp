import FvModexp.Proofs.Amd64.NatQ.RemEns
import FvModexp.Proofs.Amd64.NatQ.DivCG
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# `nat.rem` (amd64): Q-form → level-cost bridge and the closed instance (agent expmc s68; amd64 twin of arm64
`ExpQ/Bridge.rem_of_Q`)

`NHyp.RemHypQ` (reserve level `H` ∀-quantified, cost `C ul vl + stkR H s.mem st`) gives `NHyp.RemHyp` (the
`nat.expNN` premise; cost a function of the entry stack length `ℓ`) at `C ul vl + stkRes (ℓ + need ul vl)`: choose
`H := stLen s.mem st + need ul vl` per call (`ens_param`). `hyp` = the closed `nat.rem` (`div` by top's
`Q.NatDiv.ensCL`) on `LibRem.names`, window 41720 / 112.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.RemInst

/-- an `Ensures` for every reserve level gives one whose level is a function of the entry state -/
theorem ens_param {p : Amd64.Program} {e : Nat} {args : List (BitVec 64)} {pre : Nat → State → Prop}
    {post : Nat → State → State → Prop} {pre' : State → Prop} {post' : State → State → Prop}
    (h : ∀ H, Ensures p e args (pre H) (post H)) (f : State → Nat) (hpre : ∀ s, pre' s → pre (f s) s)
    (hpost : ∀ s s', post (f s) s s' → post' s s') : Ensures p e args pre' post' :=
  fun ret hret s hs hp => (h (f s) ret hret s hs (hpre s hp)).mono fun _ h' => ⟨h'.1, hpost _ _ h'.2⟩

theorem bud_br {b b' C H r r' : Nat} (hr : r ≤ stkRes H) (h : b - (C + r) + r' ≤ b') : b - (C + stkRes H) ≤ b' := by
  omega

theorem cost_br {b C H : Nat} {m : Janus.Arm64.Memory} {st : Nat} (h : C + stkRes H ≤ b) : C + stkR H m st ≤ b :=
  Nat.le_trans (Nat.add_le_add_left (stkR_le H m st) C) h

/-- the bridged cost of a callee with level bound `D` -/
@[reducible] def brC (C : Nat → Nat → Nat) (D : Nat → Nat → Nat) (l u v : Nat) : Nat := C u v + stkRes (l + D u v)

set_option maxRecDepth 20000 in
/-- **`nat.rem`**: `RemHypQ` gives `RemHyp` at the cost `C ul vl + stkRes (ℓ + need ul vl)` -/
theorem rem_of_Q {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {need C : Nat → Nat → Nat} (h : NHyp.RemHypQ impl R ns stk above need C) :
    NHyp.RemHyp impl R ns stk above need (brC C need) := by
  intro b L z zl zc st u ul uc v vl vc
  refine ens_param (fun H => h H b L z zl zc st u ul uc v vl vc)
    (fun s => stLen s.mem st.toNat + need ul.toNat vl) (fun s hp => ?_) (fun s s' hq => ?_)
  · obtain ⟨⟨a1, a2, a3⟩, ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, hc, h23, h24, hinv⟩, hv⟩, hna, hst⟩ := hp
    simp only [Nat.add_zero] at a1 a2 a3
    exact ⟨⟨a1, a2, a3⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, cost_br hc, h23, h24, hinv, hv, hna, hst, Nat.le_refl _⟩
  · obtain ⟨hf, hd, p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, hb, hinv⟩, hsb, hfr, hl, hrs⟩ := hq
    exact ⟨hf, hd, p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, hfr, hl, hrs⟩

/-- the cost function of the closed `nat.rem` in the level-cost form -/
abbrev remC : Nat → Nat → Nat → Nat := brC (Q.NatDiv.costQ Q.drsCQ) Q.NatRem.need

/-- `nat.rem` (amd64), every callee discharged, `NHyp.RemHyp` form (program `LibRem.names`, window 41720 / 112) -/
theorem hyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    NHyp.RemHyp impl R LibRem.names 41720 112 Q.NatRem.need remC :=
  rem_of_Q (Q.NatRem.ens impl hap R hgr hmc hwb (Q.NatDiv.ensCL impl hap R hgr hmc hwb hmk0 hmv0 hmz0))

end FvModexp.Amd64.RemInst
