import FvModexp.Proofs.Arm64.Nat.DivMGetK
import FvModexp.Proofs.Arm64.Nat.DivMOneT
import FvModexp.Proofs.Arm64.Nat.DivMLess

set_option autoImplicit false

/-!
# `nil.div(nil, u, u, v)` (go-bigmodexpfix natdiv.go:518, `stk == nil`, `z = nil`, `z2 = u`), arm64 — the composition

As `(*Int).QuoRem` calls it from `(*Int).Mod` (divmc's `IMod.DivHypM`, Arm64/Int/ModDefs.lean).
`len v = 1`: `one1G` → `one2M` (`divW`, `DivW.ens0`) → `oneAM | oneBM | oneCM` (`setWord`); `len v ≥ 2`: `two1G` →
`two2M` (`cmp`) → `u < v`: `lessRM` (`z2 = u` has `cap ≥ len u`) → `lessSM` (self-copy skipped); `u ≥ v`: `bigM`
(`getStack()` = `Pool.Get` / `newobject`, defer record, `divLarge`, deferred `stk.free()` = `Pool.Put`).
`ensM`: the `Ensures` = `IMod.DivHypM impl R LibDiv.names 41504 112 (costM dc)`; premises `DivLarge.Hyp` and the live
runtime contracts on `Extracted.program.ofImpl impl`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
open Janus.Contracts.Pool Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Arm64.NatDiv

theorem libDivFree_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibDivFree.program.link impl) := by
  rw [LibDivFree.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibDivFree.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fullM (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (up ul uc vp vl vc : BitVec 64) :
    Summary (LibDiv.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = 0#64 ∧ s.regs 1 = 0#64 ∧
        s.regs 2 = 0#64 ∧ s.regs 3 = 0#64 ∧ s.regs 4 = up ∧ s.regs 5 = ul ∧ s.regs 6 = uc ∧ s.regs 7 = up ∧
        s.regs 8 = ul ∧ s.regs 9 = uc ∧ s.regs 10 = vp ∧ s.regs 11 = vl ∧ s.regs 12 = vc ∧
        PreM R b dc L up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s)
      (fun s s' => RQM R b dc L up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpre⟩
  have hc3 := codeIn_lib impl hap
  have hmk := MakesliceLiveContract.of_codeIn hc3 hmk0
  have hno := NewobjectLiveContract.of_codeIn hc3 hno0
  have hget : PoolGetLive (LibDiv.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh :=
    fun L b => Summary.of_codeIn hc3 (hget0 L b)
  have hput : PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh :=
    fun L b rs => Summary.of_codeIn (libDivFree_code impl hap) (hput0 L b rs)
  have hp := hpre.f
  have hv0 := hp.v0
  have hce := hp.ce
  by_cases hv1 : vl.toNat = 1
  · have e : vl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hv1)
    subst e
    refine one1G impl R L 0#64 0#64 0#64 0#64 up ul uc up ul uc vp vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      h12 hce hp.vo _ fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 => one2M impl hap R
        hmk0 hmv0 hmz0 b dc L up ul uc vp s hp X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 _
        fun q ql qc L' b' T hW => ?_
    by_cases hr0 : natVal s.mem up.toNat ul.toNat % natVal s.mem vp.toNat 1 = 0
    · exact oneAM impl R hp hW hr0 hl4 hl48
    · rcases Nat.eq_zero_or_pos uc.toNat with hz | hz
      · rw [hz] at hp hW ⊢
        exact oneCM impl R hmk hp hW hr0 hl4 hl48
      · exact oneBM impl R hp hW hr0 hz hl4 hl48
  · have hv2 : 2 ≤ vl.toNat := by omega
    refine two1G impl R L 0#64 0#64 0#64 0#64 up ul uc up ul uc vp vl vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      h12 hv2 hce _ fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
        x26 x27 x28 x29 => two2M impl hap R L 0#64 0#64 0#64 0#64 up ul uc up ul uc vp vl vc s hp hl4 hl48 X x1 x2 x3
        x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 _
        fun S hS => ?_
    rcases Nat.lt_or_ge (natVal s.mem up.toNat ul.toNat) (natVal s.mem vp.toNat vl.toNat) with hU | hU
    · have hr0 : S.regs 0 = 18446744073709551615#64 := by rw [hS.r0]; exact cmp_lt hp.un hU
      exact lessRM impl R hce hp.inv hp.ul9 hp.uo.1 hS hr0 hp.ulc _ fun S' hA => lessSM impl R hp hA hU hl4 hl48
    · obtain ⟨c, hc, hr0⟩ := cmp_ge hp.vn hU
      rw [← hS.r0] at hr0
      exact bigM impl hap R dc hL hget hput hno hp hU hv2 up.isLt hl4 hl48 hS c hc hr0

/-- **`nat.div`** (arm64) as `(*Int).QuoRem` calls it from `(*Int).Mod`: `q, r = nil.div(nil, u, u, v)` (`stk == nil`,
`z2 = u`; `v ≠ 0`, `u`, `v` normalised, `len ≤ 2^9`) returns `r = U mod V` normalised, in `u`'s array or a fresh one;
writes only `u`'s array, the runtime's memory and the window; no panic, no fault (divmc's `IMod.DivHypM`). Premises:
`DivLarge.Hyp` and the live runtime contracts. -/
theorem ensML (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc) :
    IMod.DivHypM impl R LibDiv.names 41504 112 (costM dc) := by
  intro b L u ul uc v vl vc
  rw [← LibDiv.eq_only]
  janus_ensures_old [FvModexp.Arm64.IMod.DivPreM, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn0, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.RunIface.PoolG, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.Arm64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (fullM impl hap R hmk0 hmv0 hmz0 hno0 hget0 hput0 dc hL b L u ul uc v vl vc)
    hret h_pc h_lr ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10, h_x11, h_x12, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.NatDiv
