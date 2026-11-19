import FvModexp.Proofs.Amd64.NatQ.DivLargeNat
import FvModexp.Proofs.Amd64.NatQ.DivLargeMkU
import FvModexp.Proofs.Amd64.NatQ.DivLargeMkA
import FvModexp.Proofs.Amd64.NatQ.DivLargeSc
import FvModexp.Proofs.Amd64.NatQ.DivLargeQ
import FvModexp.Proofs.Amd64.NatQ.DivLargeDBS
import FvModexp.Proofs.Amd64.NatQ.DivLargeDRM
import FvModexp.Proofs.Amd64.NatQ.DivLargeT1
import FvModexp.Proofs.Amd64.NatQ.DivLargeT2
import FvModexp.Proofs.Amd64.Nat.StackNat
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLarge.lean, TIGHT COSTS, top s38)
# `(z nat) divLarge(stk, u, uIn, vIn)` (go-bigmodexpfix natdiv.go:597), amd64 — the composition

entry → `stk.nat(n)` (`pro1`, `pro2`) → `u.make(len uIn + 1)` (`mkR` / `mkA`) → the scaling (`scale`: two copies |
two `lshVU`) → `alias(z, u)`, `q = z.make(m + 1)` (`qSeg`) → `n < divRecursiveThreshold`: `divBasic` (`db`) |
`clear(q)` + `divRecursiveStep` (`dr`) → `q.norm()`, `rshVU` (`t1`) → `u.norm()`, deferred `stk.restore`, return
(`t2`). `ens`: the `Ensures` (`Hyp`), premise `DrsHypQ` (`divRecursiveStep`) and the live runtime contracts.
Port of `Arm64/Nat/DivLarge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

section
variable (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
  (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc0 : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
  (hmk : MakesliceLiveContract64 (LibDivL.program.link impl) (cA "runtime.makeslice") 4096 R)
  (hmv : MemmoveLive64 (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
  (hmc : MemclrNoHeapPointersLive64 (LibDivL.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc)
include hap hgr hmc0 hwb hmc hD

set_option maxRecDepth 20000 in
/-- from `joinQ`: the division, then the tail -/
theorem afterJ {b : Nat} {L : List (Nat × Nat)} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S
      (RQ R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s) := by
  by_cases hv : vl < 40
  · exact db impl hap R hgr hmc0 hwb dc b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS
      hv _ fun _ _ _ _ T hT => t1 impl hap R hE T hT _ fun _ T' hR => t2 impl R hE T' hR
  · exact dr impl hap R hmc dc hD b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS
      (by omega) _ fun _ _ _ _ T hT => t1 impl hap R hE T hT _ fun _ T' hR => t2 impl R hE T' hR

include hmk hmv in
set_option maxRecDepth 20000 in
/-- from `joinU` (`u = u.make(len uIn + 1)` done): the scaling (copy or `lshVU`), `q = z.make(m + 1)`, then `afterJ` -/
theorem afterU {b : Nat} {L : List (Nat × Nat)} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C S) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S
      (RQ R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s) := by
  have hbq : ∀ {bk' : Nat}, b1 - makeCost (il + 1) ≤ bk' → makeCost (il - vl + 1) ≤ bk' := fun h => by
    have h1 := hE.bud; have h2 := hE.pre.cost
    simp only [costQ] at h2; omega
  exact scale impl hap R hmv b L _ zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C hE S hS _ fun sh S' hA =>
    qSeg impl R hmk b L _ zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh hE S' hA (hbq hA.bud2) _
      fun S'' _ _ _ _ hJ => afterJ impl hap R hgr hmc0 hwb hmc dc hD hE S'' hJ

end

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc0 : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st up ul uc : BitVec 64) (ip il vp vl : Nat) :
    Summary (LibDivL.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = st ∧ s.regs 6 = up ∧ s.regs 8 = ul ∧
        s.regs 9 = uc ∧
        Pre R b H L (costQ dc il vl) zp.toNat zc.toNat st.toNat up.toNat uc.toNat ip il vp vl s)
      (fun s s' => RQ R b H L (costQ dc il vl) zp.toNat zc.toNat st.toNat up.toNat uc.toNat
        ip il vp vl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDivL.names
  have hmk := MakesliceLiveContract64.of_codeIn hc3 hmk0
  have hmv := MemmoveLive64.of_codeIn hc3 hmv0
  have hmc := MemclrNoHeapPointersLive64.of_codeIn hc3 hmc0
  refine pro1 impl R b L _ zp zl zc st up ul uc ip il vp vl s hpc hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre _
    fun P hP hinvP => pro2 impl hap R (StackNatX.hypQ impl hap R hgr hmc0 hwb) b L _ zp zc st up uc ip il vp vl s
      hpre P hP hinvP _ fun S2 L1 b1 hA => ?_
  have hE := env_of (S2 := S2.mem) hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow
    (fun a n v => by rw [hA.F2.accessible, Janus.Arm64.Memory.accessible_writeLE, hP.fr.accessible]) hA.mem hx15 hdf hra
  by_cases hz : il + 1 ≤ uc.toNat
  · exact mkR impl R b L _ _ _ _ _ _ _ _ _ _ s hpre hx15 hdf hra P hP S2 L1 b1 hA hz _
      fun S hU => afterU impl hap R hgr hmc0 hwb hmk hmv hmc dc hD hE S hU
  · have hb1 : makeCost (il + 1) ≤ b1 := by
      have h1 := hA.bud; have h2 := hpre.cost; simp only [costQ] at h2; omega
    exact mkA impl R hmk b L _ _ _ _ _ _ _ _ _ _ s hpre hx15 hdf hra P hP S2 L1 b1 hA (by omega) hb1 _
      fun S _ _ _ _ hU => afterU impl hap R hgr hmc0 hwb hmk hmv hmc dc hD hE S hU

/-- **`nat.divLarge`** (amd64): `q, r = z.divLarge(stk, u, uIn, vIn)` (`2 ≤ len vIn ≤ len uIn ≤ 2^9`, `vIn` normalised)
returns `q = UIn / VIn`, `r = UIn mod VIn`, both normalised, `q` in `z`'s array or a fresh one, `r` in `u`'s array or a
fresh one (apart from the stack's final array), the stack's `len` restored; writes only `z`, `u`, the stack, the
runtime's memory and the window; `fsBase` and `DF` kept; no panic, no fault. Premises: `divRecursiveStep` (`DrsHypQ`)
and the live runtime contracts (`growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`, `makeslice`, `memmove`). -/
theorem ensG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc0 : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc) : HypG impl R dc := by
  intro H b L zp zl zc st up ul uc ip il vp vl
  rw [show names = LibDivL.names from rfl, ← LibDivL.eq_only]
  janus64_ensures_old [FvModexp.Amd64.Q.DivLarge.Pre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.DivLarge.StkIn, FvModexp.stLen, FvModexp.stW, FvModexp.stCap, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.stkR, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hgr hmc0 hwb hmk0 hmv0 dc hD b L zp zl zc st up ul uc ip il vp vl) hret
    (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
      h_a3, h_a4, h_a5, h_a6, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- `ensG` in the `Post` form (`Hyp`) -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc0 : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc) : Hyp impl R dc :=
  (ensG impl hap R hgr hmc0 hwb hmk0 hmv0 dc hD).toHyp

end FvModexp.Amd64.Q.DivLarge
