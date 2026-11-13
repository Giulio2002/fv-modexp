import FvModexp.Proofs.Amd64.NatQ.DivOneA
import FvModexp.Proofs.Amd64.NatQ.DivOneB
import FvModexp.Proofs.Amd64.NatQ.DivOneT
import FvModexp.Proofs.Amd64.NatQ.DivOneTB
import FvModexp.Proofs.Amd64.NatQ.DivOneTC
import FvModexp.Proofs.Amd64.NatQ.DivCmp
import FvModexp.Proofs.Amd64.NatQ.DivCmpB
import FvModexp.Proofs.Amd64.NatQ.DivLess
import FvModexp.Proofs.Amd64.NatQ.DivLessA
import FvModexp.Proofs.Amd64.NatQ.DivLessC
import FvModexp.Proofs.Amd64.NatQ.DivBig
import FvModexp.Proofs.Amd64.NatQ.DivBigC
import FvModexp.Proofs.Amd64.NatQ.DivLarge

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/Div.lean, TIGHT COSTS, top s38)
# `(z nat) div(stk, z2, u, v)` (go-bigmodexpfix natdiv.go:518), amd64 — the composition

`len v = 1`: `one1` → `one2` (`divW`) → `oneA | oneB | oneC` (`setWord`); `len v ≥ 2`: `two1` → `two2` (`cmp`) →
`u < v`: `lessR | lessA` (`z2.make`) → `lessC1 | lessC0` (`copy`); `u ≥ v`: `big1` → `big2` (`divLarge`).
`full` ends in `RQG` (expmc's `ExpSlow.DivPostLG`); `ens`: the `Ensures` = `ExpHyp.DivHypL … 41512 112 (cost dc)`
(`HypL`, via `DivPostLG.toL`), premises `DivLarge.HypG` (or `DrsHyp` via `DivLarge.ensG`: `ensD`) and the live runtime contracts. Port of `Arm64/Nat/Div.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) :
    Summary (LibDiv.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = st ∧ s.regs 6 = z2 ∧ s.regs 8 = z2l ∧
        s.regs 9 = z2c ∧
        Pre R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
      (fun s s' => RQG R b H dc L zp.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  have hc3 := codeIn_lib impl hap
  have hmk := MakesliceLiveContract64.of_codeIn hc3 hmk0
  have hmv := MemmoveLive64.of_codeIn hc3 hmv0
  have hmz := MemmoveZeroLive64.of_codeIn hc3 hmz0
  have hp := hpre.f
  have hv0 := hp.v0
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  by_cases hv1 : vl = 1
  · subst hv1
    refine one1 impl R b dc L zp zl zc st z2 z2l z2c u ul uc v vc s hpc hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre _
      fun X hX => one2 impl hap R hmk0 hmv0 hmz0 b dc L zp zl zc st z2 z2l z2c u ul uc v vc s hpre X hX _
        fun q ql qc L' b' T hW => ?_
    by_cases hr0 : natVal s.mem u ul % natVal s.mem v 1 = 0
    · exact oneA impl R hpre.toG hW hr0 hra hx15 hdf
    · rcases Nat.eq_zero_or_pos z2c.toNat with hz | hz
      · rw [hz] at hpre hW ⊢
        exact oneC impl R hmk hpre.toG hW hr0 hra hx15 hdf
      · exact oneB impl R hpre.toG hW hr0 hz hra hx15 hdf
  · have hv2 : 2 ≤ vl := by omega
    refine two1 impl R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s hpc hx15 hdf h0 h3 h1 h7 h6 h8 h9 hv2 hpre _
      fun X hX => two2 impl hap R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s hpre X hX _ fun S hS => ?_
    rcases Nat.lt_or_ge (natVal s.mem u ul) (natVal s.mem v vl) with hU | hU
    · have hr0 : S.regs 0 = 18446744073709551615#64 := by rw [hS.r0]; exact cmp_lt hp.un hU
      have kC : ∀ S' p c L' b', AtS R b L zp.toNat zc.toNat z2.toNat z2c.toNat u ul s p c L' b' S' →
          ReachesRet (LibDiv.program.link impl) (retAddrOf s) S'
            (RQG R b H dc L zp.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s) := by
        intro S' p c L' b' hA
        rcases Nat.eq_zero_or_pos ul with hu | hu
        · subst hu
          exact lessC0 impl R hmz hpre.toG hA hU z2.isLt hra hx15 hdf
        · exact lessC1 impl R hmv hpre hA hU hu hra hx15 hdf
      by_cases hz : ul ≤ z2c.toNat
      · exact lessR impl R hpre hS hr0 hz _ fun S' hA => kC S' _ _ _ _ hA
      · exact lessA impl R hmk hpre hS hr0 (by omega) _ kC
    · obtain ⟨c, hc, hr0⟩ := cmp_ge hp.vn hU
      rw [← hS.r0] at hr0
      exact big1 impl hS c hc hr0 hp.st0 hb' ha hw _ fun X hX =>
        big2 impl hap R dc hL hpre hU hv2 X hX zp.isLt z2.isLt hra hx15 hdf

/-- **`nat.div`** (amd64), `stk ≠ nil`: `q, r = z.div(stk, z2, u, v)` (`v ≠ 0`, `u`, `v` normalised, `len ≤ 2^9`)
returns `q = U / V`, `r = U mod V`, both normalised (in `z` / `z2`'s array or fresh ones), the stack restored
(`StackBackL`); writes only `z`, `z2`, the stack, the runtime's memory and the window; `fsBase` and `DF` kept; no
panic, no fault. The statement is `ExpHyp.DivHypL … 41512 112 (cost dc)`. Premises: `DivLarge.HypG` and the live
runtime contracts (`makeslice`, `memmove`, `memmove` with `n = 0`). -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc) : HypL impl R dc := by
  intro H b L zp zl zc st z2 z2l z2c u ul uc v vl vc
  rw [show ExpHyp.fnDiv = fn from rfl, show names = LibDiv.names from rfl, ← LibDiv.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk0 hmv0 hmz0 dc hL b L zp zl zc st z2 z2l z2c u ul uc v vl vc) hret
    (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
      h_a3, h_a4, h_a5, h_a6, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, ExpSlow.DivPostLGQ.toL hq⟩

/-- **`nat.div`** (amd64) with `divLarge` discharged (`DivLarge.ens`): premise `DrsHyp` (`divRecursiveStep`) and the
live runtime contracts. -/
theorem ensD (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DivLarge.DrsHypQ impl R dc) : HypL impl R dc :=
  ens impl hap R hmk0 hmv0 hmz0 dc (DivLarge.ensG impl hap R hgr hmc hwb hmk0 hmv0 dc hD)

end FvModexp.Amd64.Q.NatDiv
