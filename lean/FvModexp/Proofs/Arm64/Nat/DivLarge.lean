import FvModexp.Proofs.Arm64.Nat.DivLargeNat
import FvModexp.Proofs.Arm64.Nat.DivLargeMkU
import FvModexp.Proofs.Arm64.Nat.DivLargeMkA
import FvModexp.Proofs.Arm64.Nat.DivLargeCpA
import FvModexp.Proofs.Arm64.Nat.DivLargeCpB
import FvModexp.Proofs.Arm64.Nat.DivLargeShA
import FvModexp.Proofs.Arm64.Nat.DivLargeQ
import FvModexp.Proofs.Arm64.Nat.DivLargeDBR
import FvModexp.Proofs.Arm64.Nat.DivLargeDRM
import FvModexp.Proofs.Arm64.Nat.DivLargeT1
import FvModexp.Proofs.Arm64.Nat.DivLargeT2

set_option autoImplicit false

/-!
# `(z nat) divLarge(stk, u, uIn, vIn)` (go-bigmodexpfix natdiv.go:597), arm64 — the composition

entry → `stk.nat(n)` (`pro1`, `pro2`) → `u.make(len uIn + 1)` (`mkR` / `mkA`) → `shift = 0`: two copies (`cpA`, `cpB`) |
`shift ≠ 0`: two `lshVU` (`shA`) → `alias(z, u)`, `q = z.make(m + 1)` (`qSeg`) → `n < divRecursiveThreshold`:
`divBasic` (`db`) | `clear(q)` + `divRecursiveStep` (`dr`) → `q.norm()`, `rshVU` (`t1`) → `u.norm()`, deferred
`stk.restore`, return (`t2`). `ens`: the `Ensures` (`Hyp`), premise `DrsHyp` (`divRecursiveStep`) and the live
runtime contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivLarge

section
variable (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
  (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc0 : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
  (hmk : MakesliceLiveContract (LibDivL.program.link impl) (cA "runtime.makeslice") 4096 R)
  (hmv : MemmoveLive (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
  (hmc : MemclrNoHeapPointersLive (LibDivL.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc)
include hap hgr hmc0 hwb hmc hD

set_option maxRecDepth 20000 in
/-- from `joinQ`: the division, then the tail -/
theorem afterJ {b : Nat} {L : List (Nat × Nat)} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S
      (RQ R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s) := by
  by_cases hv : vl < 40
  · exact db impl hap R hgr hmc0 hwb dc b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS
      hv _ fun _ _ _ _ T hT => t1 impl hap R hE T hT _ fun _ T' hR => t2 impl R hE T' hR hl4 hl48
  · exact dr impl hap R hmc dc hD b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS
      (by omega) _ fun _ _ _ _ T hT => t1 impl hap R hE T hT _ fun _ T' hR => t2 impl R hE T' hR hl4 hl48

include hmk hmv in
set_option maxRecDepth 20000 in
/-- from `joinU` (`u = u.make(len uIn + 1)` done): the scaling (copy or `lshVU`), `q = z.make(m + 1)`, then `afterJ` -/
theorem afterU {b : Nat} {L : List (Nat × Nat)} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S
      (RQ R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s) := by
  have hbq : ∀ {bk' : Nat}, b1 - makeCost (il + 1) ≤ bk' → makeCost (il - vl + 1) ≤ bk' := fun h => by
    have h1 := hE.bud; have h2 := hE.pre.cost
    simp only [cost] at h2; omega
  by_cases hclz : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0
  · exact cpA impl R hmv b L _ zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS (Mem.grd hE hS.mem) hclz _
      (cpB impl R hmv b L _ zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS hclz _ fun S' hA =>
        qSeg impl R hmk b L _ zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C 0 hE S' hA (hbq hA.bud2) _
          fun S'' _ _ _ _ hJ => afterJ impl hap R hgr hmc0 hwb hmc dc hD hE S'' hJ hl4 hl48)
  · exact shA impl hap R b L _ zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS _ rfl hclz _ fun S' hA =>
      qSeg impl R hmk b L _ zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C _ hE S' hA (hbq hA.bud2) _
        fun S'' _ _ _ _ hJ => afterJ impl hap R hgr hmc0 hwb hmc dc hD hE S'' hJ hl4 hl48

end

set_option maxRecDepth 20000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc0 : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st up ul uc ip il ic vp vl vc : BitVec 64) :
    Summary (LibDivL.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = st ∧ s.regs 4 = up ∧ s.regs 5 = ul ∧ s.regs 6 = uc ∧ s.regs 7 = ip ∧
        s.regs 8 = il ∧ s.regs 9 = ic ∧ s.regs 10 = vp ∧ s.regs 11 = vl ∧ s.regs 12 = vc ∧
        Pre R b L (cost dc (stLen s.mem st.toNat) il.toNat vl.toNat) zp.toNat zc.toNat st.toNat up.toNat uc.toNat
          ip.toNat il.toNat vp.toNat vl.toNat s)
      (fun s s' => RQ R b L (cost dc (stLen s.mem st.toNat) il.toNat vl.toNat) zp.toNat zc.toNat st.toNat up.toNat
        uc.toNat ip.toNat il.toNat vp.toNat vl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibDivL.names
  have hmk := MakesliceLiveContract.of_codeIn hc3 hmk0
  have hmv := MemmoveLive.of_codeIn hc3 hmv0
  have hmc := MemclrNoHeapPointersLive.of_codeIn hc3 hmc0
  have hcost : stackNatCost (stLen s.mem st.toNat) vl.toNat ≤ cost dc (stLen s.mem st.toNat) il.toNat vl.toNat := by
    simp only [cost]; omega
  refine pro1 impl R b L _ zp zl zc st up ul uc ip il ic vp vl vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hpre _
    fun P hP hinvP => pro2 impl hap R 4208 24 (StackNat.hypL impl hap R hgr hmc0 hwb) (by decide) (by decide) b L _
      zp zc st up uc ip il ic vp vl vc s hpre hcost P hP hinvP _ fun S2 L1 b1 hA => ?_
  have hE := env_of (S2 := S2.mem) hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow
    (fun a n v => by rw [hA.F2.accessible, hP.fr.accessible]) hA.mem
  by_cases hz : il.toNat + 1 ≤ uc.toNat
  · exact mkR impl R 4208 24 (by decide) (by decide) b L _ _ _ _ _ _ _ _ _ _ _ _ s hpre P hP S2 L1 b1 hA hz _
      fun S hU => afterU impl hap R hgr hmc0 hwb hmk hmv hmc dc hD hE S hU hl4 hl48
  · have hb1 : makeCost (il.toNat + 1) ≤ b1 := by
      have h1 := hA.bud; have h2 := hpre.cost; simp only [cost] at h2; omega
    exact mkA impl R 4208 24 (by decide) (by decide) hmk b L _ _ _ _ _ _ _ _ _ _ _ _ s hpre P hP S2 L1 b1 hA
      (by omega) hb1 _ fun S _ _ _ _ hU => afterU impl hap R hgr hmc0 hwb hmk hmv hmc dc hD hE S hU hl4 hl48

/-- **`nat.divLarge`** (arm64): `q, r = z.divLarge(stk, u, uIn, vIn)` (`2 ≤ len vIn ≤ len uIn ≤ 2^9`, `vIn` normalised)
returns `q = UIn / VIn`, `r = UIn mod VIn`, both normalised, `q` in `z`'s array or a fresh one, `r` in `u`'s array or a
fresh one (apart from the stack's final array), the stack's `len` restored; writes only `z`, `u`, the stack, the
runtime's memory and the window; no panic, no fault. Premises: `divRecursiveStep` (`DrsHyp`) and the live runtime
contracts (`growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`, `makeslice`, `memmove`). -/
theorem ensG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc0 : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc) : HypG impl R dc := by
  intro b L zp zl zc st up ul uc ip il ic vp vl vc
  rw [show names = LibDivL.names from rfl, ← LibDivL.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hgr hmc0 hwb hmk0 hmv0 dc hD b L zp zl zc st up ul uc ip il ic vp vl vc)
    hret h_pc h_lr ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10, h_x11, h_x12, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- `ensG` in the `Post` form (`Hyp`) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc0 : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc) : Hyp impl R dc :=
  (ensG impl hap R hgr hmc0 hwb hmk0 hmv0 dc hD).toHyp

end FvModexp.Arm64.DivLarge
