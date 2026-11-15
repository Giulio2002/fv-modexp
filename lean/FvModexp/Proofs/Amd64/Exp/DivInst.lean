import FvModexp.Proofs.Amd64.NatQ.DivCG
import FvModexp.Proofs.Amd64.Exp.MontW
import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W4Defs
import FvModexp.Proofs.Amd64.Exp.W2Defs
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# `nat.div` (amd64) as the windows' / `expNNOdd`'s / `expNN`'s premise `ExpHyp.DivHypL` (agent expmc s66; twin of
`Arm64.DivInst` + the `nat.div` part of `Arm64.Q` Bridge)

top's CLOSED Q-form `nat.div` (`Q.NatDiv.ensCL : ExpHyp.DivHypLQ impl R names 41512 112 (costQ drsCQ)`, NatQ/DivCG.lean:
only live runtime contracts on `Extracted.program.ofImpl impl` remain) bridged to the level-cost form the windows take
(`divL_of_Q`: reserve level `H := stLen + 16·len u + 64` per call, cost `C ul vl + stkRes (ℓ + 16·ul + 64)`), as on
arm64 (ExpQ/Bridge `divL_of_Q`). Plus the name facts the callers' statements ask of `nsD`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.DivInst

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

/-- the bridged cost of `nat.div` (level bound `16·len u + 64`) -/
@[reducible] def divBr (C : Nat → Nat → Nat) (l ul vl : Nat) : Nat := C ul vl + stkRes (l + 16 * ul + 64)

set_option maxRecDepth 20000 in
open FvModexp.Amd64.ExpHyp in
/-- **`nat.div`**: `DivHypLQ` gives `DivHypL` at the cost `C ul vl + stkRes (ℓ + 16·ul + 64)` -/
theorem divL_of_Q {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat} {C : Nat → Nat → Nat}
    (h : DivHypLQ impl R ns stk above C) : DivHypL impl R ns stk above (divBr C) := by
  intro b L z zl zc st z2 z2l z2c u ul uc v vl vc
  refine ens_param (fun H => h H b L z zl zc st z2 z2l z2c u ul uc v vl vc)
    (fun s => stLen s.mem st.toNat + 16 * ul + 64) (fun s hp => ?_) (fun s s' hq => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, hc, h40, h41, hinv⟩ := hp
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, ⟨Nat.le_refl _, cost_br hc⟩,
      h40, h41, hinv⟩
  · obtain ⟨hf, hd, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr, ⟨hLE, hb, hinv⟩, hsb, ha, hfr, hl⟩ := hq
    exact ⟨hf, hd, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr,
      ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, ha, hfr, hl⟩

/-- the cost function of the closed `nat.div` in the level-cost form -/
abbrev divC : Nat → Nat → Nat → Nat := divBr (Q.NatDiv.costQ Q.drsCQ)

/-- `nat.div` (amd64), every callee discharged, `ExpHyp.DivHypL` form (program `Q.NatDiv.names`, window 41512 / 112) -/
theorem hyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypL impl R Q.NatDiv.names 41512 112 divC :=
  divL_of_Q (Q.NatDiv.ensCL impl hap R hgr hmc hwb hmk0 hmv0 hmz0)

set_option maxHeartbeats 64000000 in
theorem ns_sub : ∀ x, Q.NatDiv.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide +kernel)

theorem ns_w4 : Q.NatDiv.names.contains W4Loop.fn = false := by decide

theorem ns_w2 : Q.NatDiv.names.contains W2Loop.fn = false := by decide

end FvModexp.Amd64.DivInst
