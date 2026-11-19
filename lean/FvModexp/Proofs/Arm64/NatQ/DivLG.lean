import FvModexp.Proofs.Arm64.NatQ.Div
import FvModexp.Proofs.Arm64.NatQ.DivZOne
import FvModexp.Proofs.Arm64.NatQ.DivZTwo
import FvModexp.Proofs.Arm64.NatQ.DivMOneA

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivLG.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64): expmc's `ExpSlow.DivHypLG` (empty-tolerant dividend, results apart) — asm s35

`fullZ`: `len u = 0` (`u` possibly `nil`): `len v = 1`: `one1G` → `one2Z` (`divW` via `DivW.ens0`) → `oneA`
(`r = z2[:0]`); `len v ≥ 2`: `two1G` → `two2Z` (`cmp`, no limb of `u` read) → `U = 0 < V` → `lessRM` (`0 ≤ cap z2`)
→ `lessC0` (`MemmoveZeroLive`). `ensLG`: `len u = 0` → `fullZ`; `len u > 0` → `PreG.toPre` → `full` (whose paths all
end in `RQG`: `post_keptG` / `oneFinG` / `bigFin` with `DivLarge.PostG`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
theorem fullZ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st z2 z2l z2c up ul uc vp vl vc : BitVec 64) (hu : ul.toNat = 0) :
    Summary (LibDiv.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = st ∧ s.regs 4 = z2 ∧ s.regs 5 = z2l ∧ s.regs 6 = z2c ∧ s.regs 7 = up ∧
        s.regs 8 = ul ∧ s.regs 9 = uc ∧ s.regs 10 = vp ∧ s.regs 11 = vl ∧ s.regs 12 = vc ∧
        PreG R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat vp.toNat
          vl.toNat s)
      (fun s s' => RQG R b H dc L zp.toNat zc.toNat st.toNat z2.toNat z2c.toNat up.toNat ul.toNat vp.toNat vl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpre⟩
  have hc3 := codeIn_lib impl hap
  have hmz := MemmoveZeroLive.of_codeIn hc3 hmz0
  have hp := hpre.f
  have hU0 : natVal s.mem up.toNat ul.toNat = 0 := by simp only [natVal, hu, Nat.mul_zero, Memory.readLE_zero]
  by_cases hv1 : vl.toNat = 1
  · have e : vl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hv1)
    subst e
    refine one1G impl R L zp zl zc st z2 z2l z2c up ul uc vp vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      hp.ce hp.vo _ fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 => one2Z impl hap R
        hmk0 hmv0 hmz0 b dc L zp zl zc st z2 z2l z2c up ul uc vp s hpre hu X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
        x13 x14 x15 x16 x17 x18 x19 _ fun q ql qc L' b' T hW => ?_
    exact oneA impl R hpre hW (by rw [hU0, Nat.zero_mod]) hl4 hl48
  · have hv2 : 2 ≤ vl.toNat := by have := hp.v0; omega
    refine two1G impl R L zp zl zc st z2 z2l z2c up ul uc vp vl vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      hv2 hp.ce _ fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
        x27 x28 x29 => two2Z impl hap R L zp zl zc st z2 z2l z2c up ul uc vp vl vc s hp.ce hp.ui hp.vo hl4 hl48 X x1 x2
        x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 _
        fun S hS => ?_
    have hV : 0 < natVal s.mem vp.toNat vl.toNat := by
      rcases hp.vn with h | h
      · omega
      · have := natVal_ge1 s.mem vp.toNat vl.toNat (by omega) h
        have := Nat.two_pow_pos (64 * (vl.toNat - 1)); omega
    have hU : natVal s.mem up.toNat ul.toNat < natVal s.mem vp.toNat vl.toNat := by rw [hU0]; exact hV
    have hr0 : S.regs 0 = 18446744073709551615#64 := by rw [hS.r0]; exact cmp_lt hp.un hU
    refine lessRM impl R hp.ce hp.inv hp.ul9 hp.z2o.1 hS hr0 (by omega) _ fun S' hA => ?_
    rw [hu] at hpre hA hU ⊢
    exact lessC0 impl R hmz hpre hA hU hl4 hl48

/-- **`nat.div`** (arm64) in expmc's empty-tolerant / results-apart form (`ExpSlow.DivHypLG`): premise
`DivLarge.HypG` and the live runtime contracts -/
theorem ensLG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc) :
    ExpSlow.DivHypLGQ impl R names 41504 112 (costQ dc) := by
  intro H b L z zl zc st z2 z2l z2c u ul uc v vl vc
  rw [show names = LibDiv.names from rfl, ← LibDiv.eq_only]
  janus_ensures_old [FvModexp.Arm64.ExpSlow.DivPreGQ, FvModexp.stkR, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn0, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, FvModexp.Arm64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Arm64.StackNat.wbA, FvModexp.Arm64.RunIface.gA, FvModexp.stkRes, FvModexp.potK, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  have hl4 : (s.regs 30).toNat % 4 = 0 := by
    rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  have hl48 : (s.regs 30).toNat < 2 ^ 48 := by
    rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48
  by_cases hu : ul.toNat = 0
  · exact Summary.returns (fullZ (H := H) impl hap R hmk0 hmv0 hmz0 dc b L z zl zc st z2 z2l z2c u ul uc v vl vc hu)
      hret h_pc h_lr ⟨hl4, hl48, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10, h_x11, h_x12, hpre⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · exact Summary.returns (full (H := H) impl hap R hmk0 hmv0 hmz0 dc hL b L z zl zc st z2 z2l z2c u ul uc v vl vc)
      hret h_pc h_lr ⟨hl4, hl48, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10, h_x11, h_x12,
        PreG.toPre hpre (by omega)⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- `ensLG` with `divLarge` discharged (`DivLarge.ensG`): premise `DrsHyp` and the live runtime contracts -/
theorem ensDLG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DivLarge.DrsHypQ impl R dc) :
    ExpSlow.DivHypLGQ impl R names 41504 112 (costQ dc) :=
  ensLG impl hap R hmk0 hmv0 hmz0 dc (DivLarge.ensG impl hap R hgr hmc hwb hmk0 hmv0 dc hD)

end FvModexp.Arm64.Q.NatDiv
