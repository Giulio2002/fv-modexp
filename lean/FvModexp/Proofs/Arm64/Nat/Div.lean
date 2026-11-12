import FvModexp.Proofs.Arm64.Nat.DivOneA
import FvModexp.Proofs.Arm64.Nat.DivOneB
import FvModexp.Proofs.Arm64.Nat.DivOneT
import FvModexp.Proofs.Arm64.Nat.DivCmp
import FvModexp.Proofs.Arm64.Nat.DivCmpB
import FvModexp.Proofs.Arm64.Nat.DivLess
import FvModexp.Proofs.Arm64.Nat.DivLessC
import FvModexp.Proofs.Arm64.Nat.DivBig
import FvModexp.Proofs.Arm64.Nat.DivBigC
import FvModexp.Proofs.Arm64.Nat.DivLarge

set_option autoImplicit false

/-!
# `(z nat) div(stk, z2, u, v)` (go-bigmodexpfix natdiv.go:518), arm64 — the composition

`len v = 1`: `one1` → `one2` (`divW`) → `oneA | oneB | oneC` (`setWord`); `len v ≥ 2`: `two1` → `two2` (`cmp`) →
`u < v`: `lessR | lessA` (`z2.make`) → `lessC1 | lessC0` (`copy`); `u ≥ v`: `big1` → `big2` (`divLarge`).
`ens`: the `Ensures` = `ExpHyp.DivHyp … 41504 112 (cost dc)` (DivPre contains `HdrSep` since expmc s24)
(asm s18 REQUEST to expmc), premises `DivLarge.Hyp` (or `DrsHyp` via `DivLarge.ens`: `ens'`) and the live contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st z2 z2l z2c up ul uc vp vl vc : BitVec 64) :
    Summary (LibDiv.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = st ∧ s.regs 4 = z2 ∧ s.regs 5 = z2l ∧ s.regs 6 = z2c ∧ s.regs 7 = up ∧
        s.regs 8 = ul ∧ s.regs 9 = uc ∧ s.regs 10 = vp ∧ s.regs 11 = vl ∧ s.regs 12 = vc ∧
        Pre R b dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat vp.toNat
          vl.toNat s)
      (fun s s' => RQG R b dc L zp.toNat zc.toNat st.toNat z2.toNat z2c.toNat up.toNat ul.toNat vp.toNat vl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpre⟩
  have hsep : HdrSep s st.toNat := hpre.f.hdr
  have hc3 := codeIn_lib impl hap
  have hmk := MakesliceLiveContract.of_codeIn hc3 hmk0
  have hmv := MemmoveLive.of_codeIn hc3 hmv0
  have hmz := MemmoveZeroLive.of_codeIn hc3 hmz0
  have hp := hpre.f
  have hv0 := hp.v0
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hp.ce
  by_cases hv1 : vl.toNat = 1
  · have e : vl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hv1)
    subst e
    refine one1 impl R b dc L zp zl zc st z2 z2l z2c up ul uc vp vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      hpre _ fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 => one2 impl hap R hmk0 hmv0 hmz0
        b dc L zp zl zc st z2 z2l z2c up ul uc vp s hpre X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
        x19 _ fun q ql qc L' b' T hW => ?_
    by_cases hr0 : natVal s.mem up.toNat ul.toNat % natVal s.mem vp.toNat 1 = 0
    · exact oneA impl R hpre.toG hW hr0 hl4 hl48
    · rcases Nat.eq_zero_or_pos z2c.toNat with hz | hz
      · rw [hz] at hpre hW ⊢
        exact oneC impl R hmk hpre.toG hW hr0 hl4 hl48
      · exact oneB impl R hpre.toG hW hr0 hz hl4 hl48
  · have hv2 : 2 ≤ vl.toNat := by omega
    refine two1 impl R b dc L zp zl zc st z2 z2l z2c up ul uc vp vl vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      hv2 hpre _ fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
        x27 x28 x29 => two2 impl hap R b dc L zp zl zc st z2 z2l z2c up ul uc vp vl vc s hpre hl4 hl48 X x1 x2 x3 x4 x5 x6
        x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 _ fun S hS => ?_
    rcases Nat.lt_or_ge (natVal s.mem up.toNat ul.toNat) (natVal s.mem vp.toNat vl.toNat) with hU | hU
    · have hr0 : S.regs 0 = 18446744073709551615#64 := by rw [hS.r0]; exact cmp_lt hp.un hU
      have kC : ∀ S' p c L' b', AtS R b L zp.toNat zc.toNat z2.toNat z2c.toNat up.toNat ul.toNat s p c L' b' S' →
          ReachesRet (LibDiv.program.link impl) (s.regs 30) S'
            (RQG R b dc L zp.toNat zc.toNat st.toNat z2.toNat z2c.toNat up.toNat ul.toNat vp.toNat vl.toNat s) := by
        intro S' p c L' b' hA
        rcases Nat.eq_zero_or_pos ul.toNat with hu | hu
        · rw [hu] at hpre hA hU ⊢
          exact lessC0 impl R hmz hpre.toG hA hU hl4 hl48
        · exact lessC1 impl R hmv hpre hA hU hu hl4 hl48
      by_cases hz : ul.toNat ≤ z2c.toNat
      · exact lessR impl R hpre hS hr0 hz _ fun S' hA => kC S' _ _ _ _ hA
      · exact lessA impl R hmk hpre hS hr0 (by omega) _ kC
    · obtain ⟨c, hc, hr0⟩ := cmp_ge hp.vn hU
      rw [← hS.r0] at hr0
      refine big1 impl hS c hc hr0 hp.st0 hal hb' ha hw _ fun X y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14
        y15 y16 y17 y18 y19 yF yR yB => ?_
      have hFX : MemFrame s.mem X.mem (winA s 41504 112) := hS.mf.trans yF fun a n h => ⟨h, by
        simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
      have hslot : ∀ a, (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232) → X.mem.readLE a 8 = S.mem.readLE a 8 :=
        fun a h => yF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
      exact big2 impl hap R dc hL hpre hsep hU hv2 hl4 hl48 X y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
        y17 y18 y19 hFX (by rw [yR, hS.reg]) (by rw [hslot _ ⟨by omega, by omega⟩]; exact hS.lr)
        (by rw [hslot _ ⟨by omega, by omega⟩]; exact hS.fp) yB zp.isLt z2.isLt

/-- **`nat.div`** (arm64), `stk ≠ nil`: `q, r = z.div(stk, z2, u, v)` (`v ≠ 0`, `u`, `v` normalised, `len ≤ 2^9`)
returns `q = U / V`, `r = U mod V`, both normalised (in `z` / `z2`'s array or fresh ones), the stack restored; writes
only `z`, `z2`, the stack, the runtime's memory and the window; no panic, no fault. The precondition is
`ExpHyp.DivPre` (= `ExpHyp.DivHyp`). Premises: `DivLarge.Hyp` and the live runtime contracts. -/
theorem ensLG0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => Pre R b dc L z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat
        v.toNat vl.toNat s)
      (fun s s' => PostLG R b dc L z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s') := by
  rw [show names = LibDiv.names from rfl, ← LibDiv.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk0 hmv0 hmz0 dc hL b L z zl zc st z2 z2l z2c u ul uc v vl vc)
    hret h_pc h_lr ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10, h_x11, h_x12, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- `ensLG0` in the `PostL` form -/
theorem ensL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => Pre R b dc L z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat
        v.toNat vl.toNat s)
      (fun s s' => PostL R b dc L z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s') :=
  (ensLG0 impl hap R hmk0 hmv0 hmz0 dc hL b L z zl zc st z2 z2l z2c u ul uc v vl vc).mono (fun _ h => h)
    (fun _ _ _ h => ExpSlow.DivPostLG.toL h)

/-- `ensL` in the `StackBack` form (`ExpHyp.DivPost`) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => Pre R b dc L z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat
        v.toNat vl.toNat s)
      (fun s s' => Post R b dc L z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s') :=
  (ensL impl hap R hmk0 hmv0 hmz0 dc hL b L z zl zc st z2 z2l z2c u ul uc v vl vc).mono (fun _ h => h)
    (fun _ _ _ h => h.toDivPost)

end FvModexp.Arm64.NatDiv

namespace FvModexp.Arm64.NatDiv

/-- **`nat.div`** (arm64) with `divLarge` discharged (`DivLarge.ens`): premise `DrsHyp` (`divRecursiveStep`) and the
live runtime contracts. -/
theorem ensDL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hD : DivLarge.DrsHyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => Pre R b dc L z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat
        v.toNat vl.toNat s)
      (fun s s' => PostL R b dc L z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s') :=
  ensL impl hap R hmk0 hmv0 hmz0 dc (DivLarge.ensG impl hap R hgr hmc hwb hmk0 hmv0 dc hD) b L z zl zc st z2 z2l z2c u ul
    uc v vl vc


/-- `ensDL` in the `StackBack` form -/
theorem ensD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hD : DivLarge.DrsHyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => Pre R b dc L z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat
        v.toNat vl.toNat s)
      (fun s s' => Post R b dc L z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s') :=
  (ensDL impl hap R hgr hmc hwb hmk0 hmv0 hmz0 dc hD b L z zl zc st z2 z2l z2c u ul uc v vl vc).mono (fun _ h => h)
    (fun _ _ _ h => h.toDivPost)

end FvModexp.Arm64.NatDiv
