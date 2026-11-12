import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4P01Ret
import FvModexp.Proofs.Arm64.Exp.W4Snc

/-!
# window-4 (arm64): from `oneJ` (fn+0x524) to the return

`oneSmall`/`oneLarge` (`one`, `powers` zeroing) → `snCall` (`buf := stk.nat(17n)`) → `p01Ret`. The facts `p01Ret`
needs at `p01` are moved from the memory at `oneJ` through the two frames (`OnePost`, `SnPost`); the table buffer
`buf = stW' + 8·len` lies in the old free part of the stack (kept array) or in a fresh array.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step)

/-- the whole window-4 frame below `sp + 1040`, including the deepest callee window (`nat.sub`, 4304) -/
@[reducible] def W4w (sp : Nat) : Nat × Nat := (sp - 4304, 4304 + 1040)

set_option maxRecDepth 20000 in
theorem one_rd {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g sp n onep a k : Nat} {M0 M1 : Memory}
    (hO : OnePost R L L1 b b1 g sp n M0 M1 onep) (hh : InRanges a k L ∨ Outside a k R.rt)
    (hw : Apart a k (sp - 4288) (4288 + 1040)) : M1.readLE a k = M0.readLE a k := by
  have hF := hO.2.2.2.1
  have hL := hO.2.2.2.2.1
  unfold Apart at hw
  rcases hh with h | h
  · exact hL.readLE a k h trivial
  · exact hF.readLE a k (by
      simp only [ow, outside_append, outside_cons, outside_nil, and_true]; exact ⟨h, by omega, by omega, by omega, by omega⟩)

theorem sn_rd {R : RtInv} {L1 L2 : List (Nat × Nat)} {b1 b2 g sp st k a j : Nat} {M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st k M1 M2) (hok : stLen M1 st ≤ stCap M1 st)
    (hh : InRanges a j L1 ∨ Outside a j R.rt)
    (hw : Apart a j (sp - 4288) (4288 + 1040)) (hst : Apart a j st 24) (hfr : Apart a j (stFree M1 st).1 (stFree M1 st).2) :
    M2.readLE a j = M1.readLE a j := by
  obtain ⟨-, -, -, -, -, -, -, hF, hL, -⟩ := hS
  unfold Apart at hw hst hfr
  simp only at hfr
  have h2 : Outside a j (stkWs M1 st) := by
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega
  exact FvModexp.Expmc.held_readLE hh hF hL (by simp only [outside_cons, outside_nil, and_true]; omega) h2

theorem apart_held' {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart a n p k := by
  have := apart_held hin hap hh; unfold Apart at this ⊢; omega

/-- the table buffer is apart from every held object that is apart from the old free part -/
theorem buf_apart {R : RtInv} {L1 L2 : List (Nat × Nat)} {b1 b2 g sp st k a j : Nat} {M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st k M1 M2) (hok : stLen M1 st ≤ stCap M1 st)
    (hh : InRanges a j L1 ∨ Outside a j R.rt)
    (hfr : stLen M1 st + StackNat.rnd k ≤ stCap M1 st → Apart a j (stFree M1 st).1 (stFree M1 st).2) :
    Apart a j (stW M2 st + 8 * stLen M1 st) (8 * k) := by
  obtain ⟨-, -, -, hsok, hlen, hkept, hfresh, -⟩ := hS
  have hr : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega
  have hlc := hsok.2.2.2.2.2.1
  by_cases hc : stLen M1 st + StackNat.rnd k ≤ stCap M1 st
  · obtain ⟨e1, e2⟩ := hkept hc
    have hfr' := hfr hc
    rw [e1]; unfold Apart at hfr' ⊢; simp only at hfr'; omega
  · obtain ⟨hin, hap⟩ := hfresh (by omega)
    have := apart_held' hin hap hh
    unfold Apart at this ⊢; omega

/-- the table buffer's own facts at `p01` -/
theorem buf_facts {R : RtInv} {L1 L2 : List (Nat × Nat)} {b1 b2 g sp st n : Nat} {M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st (17 * n) M1 M2) (hok : stLen M1 st ≤ stCap M1 st)
    (harr : 0 < stCap M1 st → Apart (stW M1 st) (8 * stCap M1 st) (sp - 4304) (4304 + 1040) ∧
      Apart (stW M1 st) (8 * stCap M1 st) (g + 16) 8)
    (hrt : Outside (sp - 4304) (4304 + 1040) R.rt) (hgrt : Outside (g + 16) 8 R.rt) (hn : 0 < n) :
    M2.accessible (stW M2 st + 8 * stLen M1 st) (8 * (17 * n)) true = true ∧
    stW M2 st + 8 * stLen M1 st + 8 * (17 * n) ≤ 2 ^ 48 ∧
    (InRanges (stW M2 st + 8 * stLen M1 st) (8 * (17 * n)) L2 ∨
      Outside (stW M2 st + 8 * stLen M1 st) (8 * (17 * n)) R.rt) ∧
    Apart (stW M2 st + 8 * stLen M1 st) (8 * (17 * n)) (sp - 4304) (4304 + 1040) ∧
    Apart (g + 16) 8 (stW M2 st + 8 * stLen M1 st) (8 * (17 * n)) := by
  obtain ⟨bp, hbp⟩ : ∃ bp, bp = stW M2 st + 8 * stLen M1 st := ⟨_, rfl⟩
  rw [← hbp]
  obtain ⟨-, -, -, hsok, hlen, hkept, hfresh, -⟩ := hS
  obtain ⟨-, -, -, -, hlive, hlc2, -⟩ := hsok
  have hr : 17 * n ≤ StackNat.rnd (17 * n) := by simp only [StackNat.rnd]; omega
  have hcap : 0 < stCap M2 st := by omega
  obtain ⟨l8, lh, lacc, l48⟩ := hlive hcap
  have hsub1 : stW M2 st ≤ bp := by omega
  have hsub2 : bp + 8 * (17 * n) ≤ stW M2 st + 8 * stCap M2 st := by omega
  refine ⟨M2.accessible_sub lacc (Or.inr rfl) hsub1 hsub2, by omega,
    lh.imp (fun h => h.sub hsub1 hsub2) (fun h => h.of_sub hsub1 hsub2), ?_, ?_⟩
  all_goals by_cases hc : stLen M1 st + StackNat.rnd (17 * n) ≤ stCap M1 st
  · obtain ⟨e1, e2⟩ := hkept hc
    obtain ⟨a1, -⟩ := harr (by omega)
    unfold Apart at a1 ⊢; rw [hbp, e1] at hsub1 hsub2 ⊢; rw [e2] at hsub2; omega
  · obtain ⟨hin, -⟩ := hfresh (by omega)
    have := out_inR hrt hin; unfold Apart; omega
  · obtain ⟨e1, e2⟩ := hkept hc
    obtain ⟨-, a2⟩ := harr (by omega)
    unfold Apart at a2 ⊢; rw [hbp, e1] at hsub1 hsub2 ⊢; rw [e2] at hsub2; omega
  · obtain ⟨hin, -⟩ := hfresh (by omega)
    have := out_inR hgrt hin; unfold Apart; omega

set_option maxRecDepth 20000 in
theorem hdr_one {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g sp n onep st : Nat} {M0 M1 : Memory}
    (hO : OnePost R L L1 b b1 g sp n M0 M1 onep) (hh : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hw : Apart st 24 (sp - 4304) (4304 + 1040)) :
    stW M1 st = stW M0 st ∧ stLen M1 st = stLen M0 st ∧ stCap M1 st = stCap M0 st := by
  have h3 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M0.readLE (st + j) 8 := fun j hj =>
    one_rd hO (hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (by unfold Apart at hw ⊢; omega)
  exact ⟨by simpa using h3 0 (by omega), h3 8 (by omega), h3 16 (by omega)⟩

set_option maxRecDepth 20000 in
/-- a held object apart from the window, the stack header and the free part keeps its bytes `oneJ → p01` -/
theorem rd2 {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b2 g sp n onep st a k : Nat} {M0 M1 M2 : Memory}
    (hO : OnePost R L L1 b b1 g sp n M0 M1 onep) (hS : SnPost R b1 L1 L2 b2 g sp st (17 * n) M1 M2)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt) (hstw : Apart st 24 (sp - 4304) (4304 + 1040))
    (hlc : stLen M0 st ≤ stCap M0 st)
    (hh : InRanges a k L ∨ Outside a k R.rt) (hw : Apart a k (sp - 4288) (4288 + 1040)) (hs : Apart a k st 24)
    (hfr : Apart a k (stFree M0 st).1 (stFree M0 st).2) : M2.readLE a k = M0.readLE a k := by
  obtain ⟨e1, e2, e3⟩ := hdr_one hO hsth hstw
  have hx := hO.2.1
  rw [sn_rd hS (by rw [e2, e3]; exact hlc) (hh.imp hx.inRanges_old id) hw hs (by simp only [e1, e2, e3]; exact hfr),
    one_rd hO hh hw]

set_option maxRecDepth 20000 in
/-- a frame slot of window-4 outside `ow` keeps its word `oneJ → p01` -/
theorem slot2 {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b2 g sp n onep st K : Nat} {M0 M1 M2 : Memory}
    (hO : OnePost R L L1 b b1 g sp n M0 M1 onep) (hS : SnPost R b1 L1 L2 b2 g sp st (17 * n) M1 M2)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt) (hstw : Apart st 24 (sp - 4304) (4304 + 1040))
    (hfw : Apart (stFree M0 st).1 (stFree M0 st).2 (sp - 4304) (4304 + 1040)) (hlc : stLen M0 st ≤ stCap M0 st)
    (hrt : Outside (sp - 4304) (4304 + 1040) R.rt) (hsp : 4304 ≤ sp)
    (hK : 32 ≤ K ∧ K + 8 ≤ 336 ∨ 368 ≤ K ∧ K + 8 ≤ 432 ∨ 824 ≤ K ∧ K + 8 ≤ 1040) :
    M2.readLE (sp + K) 8 = M0.readLE (sp + K) 8 := by
  obtain ⟨e1, e2, e3⟩ := hdr_one hO hsth hstw
  have hro : Outside (sp + K) 8 R.rt := hrt.of_sub (by omega) (by omega)
  have hF1 := hO.2.2.2.1
  have hF2 := hS.2.2.2.2.2.2.2.1
  unfold Apart at hstw hfw
  simp only at hfw
  rw [hF2.readLE _ _ ?_, hF1.readLE _ _ ?_]
  · simp only [ow, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hro, by omega, by omega, by omega, by omega⟩
  · simp only [stkWs, e1, e2, e3, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hro, by omega, by omega⟩, by omega, by omega⟩


set_option maxRecDepth 20000 in
theorem one_facts {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b1 b2 g sp n st onep : Nat} {M M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st (17 * n) M1 M2) (hxO : LiveExt R L L1)
    (e1 : stW M1 st = stW M st) (e2 : stLen M1 st = stLen M st) (e3 : stCap M1 st = stCap M st)
    (hlc : stLen M st ≤ stCap M st) (hcap : 0 < stCap M st)
    (lah : Held R L (stW M st) (8 * stCap M st)) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hrt4 : Outside (sp - 4304) (4304 + 1040) R.rt) (hstw4 : Apart st 24 (sp - 4304) (4304 + 1040))
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4304) (4304 + 1040)) (hK4 : 4304 ≤ sp)
    (hbw : Apart (stW M2 st + 8 * stLen M st) (8 * (17 * n)) (sp - 4304) (4304 + 1040))
    (honeC : (onep = sp + 336 ∧ n ≤ 4) ∨ (InRanges onep (8 * n) L1 ∧ InRanges onep (8 * n) R.rt ∧
      ApartAll onep (8 * n) L ∧ M1.accessible onep (8 * n) true = true ∧ onep + 8 * n ≤ 2 ^ 48 ∧ onep % 8 = 0))
    (hone1O : M1.readLE onep (8 * n) = 1) :
    OneIn R L2 sp n M2 onep ∧ M2.readLE onep (8 * n) = 1 ∧
    Apart (stW M2 st + 8 * stLen M st) (8 * (17 * n)) onep (8 * n) ∧
    (∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4288) (4288 + 1040) → Apart a k onep (8 * n)) := by
  have hxS2 := hS.1
  have hFS := hS.2.2.2.2.2.2.2.1
  have hlc1 : stLen M1 st ≤ stCap M1 st := by rw [e2, e3]; exact hlc
  have hFE : stFree M1 st = stFree M st := by simp only [stFree]; rw [e1, e2, e3]
  have hWE : stkWs M1 st = stkWs M st := by simp only [stkWs]; rw [e1, e2, e3]
  have hfw' := hfw; have hstw' := hstw4
  unfold Apart at hfw' hstw'; simp only at hfw'
  rcases honeC with ⟨rfl, h4⟩ | ⟨i1, i2, i3, i4, i5, i6⟩
  · refine ⟨Or.inr ⟨rfl, h4⟩, ?_, ?_, fun a k _ hw => ?_⟩
    · rw [hFS.readLE _ _ ?_]; exact hone1O
      have hro : Outside (sp + 336) (8 * n) R.rt := hrt4.of_sub (by omega) (by omega)
      rw [hWE]
      simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hro, by omega, by omega⟩, by omega, by omega⟩
    · unfold Apart at hbw ⊢; omega
    · unfold Apart at hw ⊢; omega
  · have hpw := out_inR hrt4 i2
    have hsto : Apart st 24 onep (8 * n) := apart_held' i2 i3 hsth
    have hoF : Apart onep (8 * n) (stFree M st).1 (stFree M st).2 := by
      have := apart_held' i2 i3 lah; unfold Apart at this ⊢; simp only; omega
    refine ⟨Or.inl ⟨by rw [hFS.accessible]; exact M1.accessible_sub i4 (Or.inr rfl) (Nat.le_refl _) (Nat.le_refl _),
      i5, Or.inl (hxS2.inRanges_old i1), by unfold Apart; omega⟩, ?_, ?_, fun a k hh _ => apart_held' i2 i3 hh⟩
    · rw [sn_rd hS hlc1 (Or.inl i1) (by unfold Apart; omega) (by unfold Apart at hsto ⊢; omega)
        (by rw [hFE]; exact hoF)]
      exact hone1O
    · have := buf_apart hS hlc1 (Or.inl i1) (fun _ => by rw [hFE]; exact hoF)
      rw [e2] at this; unfold Apart at this ⊢; omega

/-- `p01Ret`'s conclusion with the operand values given explicitly -/
@[reducible] def RetPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t bp yp ylen Y yi zp zc zzp zzc st n0 onep : Nat)
    (r18 r29 : BitVec 64) (Mv xv rv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (Mj M' : Memory) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
    MemFrame M Mj (R.rt ++ tw sp bp n) ∧ LiveFrame M Mj L [(bp, bp + 8 * (17 * n))] ∧
    R.inv b L g (view R.rt L Mj) ∧ Mj.regions = M.regions ∧
    ZPost R L L' b b' g sp n Mj M' zp zc zp' zc' ∧
    ZjPost R b' L' g sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) yp ylen bp zp' zc' zzp zzc
      (Exp.montPow n Mv ((2 ^ 64 - t) % 2 ^ 64) xv rv)
      (zjVal n Mv ((2 ^ 64 - t) % 2 ^ 64) (Exp.montPow n Mv ((2 ^ 64 - t) % 2 ^ 64) xv rv) Y ylen yi)
      st n0 onep r18 r29 M' s'

/-- small-context arithmetic for `afterOne` (omega in its ~150-hypothesis context cost > 2 min) -/
theorem sub2 {b b1 b2 x y : Nat} (h1 : b - x ≤ b1) (h2 : b1 - y ≤ b2) : b - (x + y) ≤ b2 := by omega

theorem fe15 {n0 a b c d r : Nat} (hn0 : n0 ≤ a) (e2 : b = a) (hlen : c = b + r) (hc : c ≤ d) : n0 ≤ d := by omega

set_option maxRecDepth 20000 in
theorem win_sub {a k sp : Nat} (hsp : 4304 ≤ sp) (h : Apart a k (sp - 4304) (4304 + 1040)) :
    Apart a k (sp - 4288) (4288 + 1040) := by unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
theorem go2 {g sp st : Nat} {M : Memory} (hsp : 4304 ≤ sp) (hga4 : Apart (g + 16) 8 (sp - 4304) (4304 + 1040))
    (hstg : Apart st 24 (g + 16) 8) (hfg : Apart (stFree M st).1 (stFree M st).2 (g + 16) 8)
    (hlc : stLen M st ≤ stCap M st) :
    Outside (g + 16) 8 (ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M st) := by
  unfold Apart at hga4 hstg hfg; simp only at hfg
  simp only [ow, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega

/-- the stack/runtime chain `oneJ → p01` -/
@[reducible] def OneChain (R : RtInv) (b : Nat) (L L2 : List (Nat × Nat)) (b2 sp n st : Nat) (M0 M2 : Memory) : Prop :=
  MemFrame M0 M2 (R.rt ++ ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M0 st) ∧
  LiveFrame M0 M2 L (stkWs M0 st) ∧ LiveExt R L L2 ∧
  b - ((if 4 < n then blockSize (8 * n) true else 0) + stackNatCost (stLen M0 st) (17 * n)) ≤ b2 ∧
  StkOK M2 R L2 st ∧ stLen M2 st = stLen M0 st + StackNat.rnd (17 * n) ∧
  (stLen M0 st + StackNat.rnd (17 * n) ≤ stCap M0 st → stW M2 st = stW M0 st ∧ stCap M2 st = stCap M0 st) ∧
  (stCap M0 st < stLen M0 st + StackNat.rnd (17 * n) → InRanges (stW M2 st) (8 * stCap M2 st) R.rt ∧
    ApartAll (stW M2 st) (8 * stCap M2 st) L) ∧ M2.regions = M0.regions

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 from the `stk.nat(17n)` call (after `one`/`powers`) to the return -/
theorem afterOne (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t rrp rrc xp xc yp ylen Y yi zp zc zzp zzc st n0 : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64)
    (he : Env R L g sp M) (hce : CallW.CEnv R L g sp 4304 1040 M)
    (hn : 0 < n) (hn128 : n ≤ 128) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp) (hrr : Inp R L sp n M rrp) (hx : Inp R L sp n M xp)
    (r1016 : M.readLE (sp + 1016) 8 = mp) (r1024 : M.readLE (sp + 1024) 8 = n) (r1032 : M.readLE (sp + 1032) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r832 : M.readLE (sp + 832) 8 = rrp) (r256 : M.readLE (sp + 256) 8 = n) (r264 : M.readLE (sp + 264) 8 = rrc)
    (r904 : M.readLE (sp + 904) 8 = xp) (r328 : M.readLE (sp + 328) 8 = n) (r320 : M.readLE (sp + 320) 8 = xc)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hy : Inp R L sp ylen M yp) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0)
    (hold : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) st 24 ∧
      Apart zp (8 * zc) (stFree M st).1 (stFree M st).2)
    (hzz : Buf R L g sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzz4 : Apart zzp (8 * zzc) (sp - 4304) 16) (hzzs : Apart zzp (8 * zzc) st 24)
    (hzzF : Apart zzp (8 * zzc) (stFree M st).1 (stFree M st).2)
    (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r952 : M.readLE (sp + 952) 8 = zc) (r936 : M.readLE (sp + 936) 8 = zp)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (hokz : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4])
    (hokM : ∀ p d, R.ok (Extracted.program.contractAddr "runtime.memmove") [p, d, 8 * n])
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm : NatNorm M mp n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 1040))
    -- the stack
    (hsok : StkOK M R L st) (hn0 : n0 ≤ stLen M st) (hcap : 0 < stCap M st)
    (hfg : Apart (stFree M st).1 (stFree M st).2 (g + 16) 8)
    (harr : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4304) (4304 + 1040) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8)
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4304) (4304 + 1040))
    (hslen : stLen M st + 17 * n + 3 ≤ 2 ^ 16) (hwba : M.accessible StackNat.wbA 4 false = true)
    (hstwb : Apart st 24 StackNat.wbA 4) (hstf : Apart st 24 (stFree M st).1 (stFree M st).2)
    (hmS : Apart mp (8 * n) st 24) (hmF : Apart mp (8 * n) (stFree M st).1 (stFree M st).2)
    (hrS : Apart rrp (8 * n) st 24) (hrF : Apart rrp (8 * n) (stFree M st).1 (stFree M st).2)
    (hxS : Apart xp (8 * n) st 24) (hxF : Apart xp (8 * n) (stFree M st).1 (stFree M st).2)
    (hyS : Apart yp (8 * ylen) st 24) (hyF : Apart yp (8 * ylen) (stFree M st).1 (stFree M st).2)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (17 * n) + blockSize (8 * (2 * n + 4)) true ≤ b)
    -- after `one`
    (L1 : List (Nat × Nat)) (b1 onep : Nat) (M1 : Memory) (hO : OnePost R L L1 b b1 g sp n M M1 onep)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 snE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 (17 * n))
    (h30 : S.regs 30 = BitVec.ofNat 64 p01)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M1) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        OneChain R b L L2 b2 sp n st M M2 ∧
        RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29
          (M.readLE mp (8 * n)) (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) M2 s')) := by
  have hO0 := hO
  obtain ⟨heO, hxO, hbO, hFO, hLO, hinvO, hrgO, r816O, hone1O, honeC⟩ := hO0
  obtain ⟨e1, e2, e3⟩ := hdr_one hO hsth hstw4
  have hFE : stFree M1 st = stFree M st := by simp only [stFree]; rw [e1, e2, e3]
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hce0 := hce
  obtain ⟨-, hK4, -, hacc4, -, -, -, hrt4, hga4, -, -, hd, -⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  -- `CEnv`, stack and call precondition at the `stk.nat` call
  have hgoO : Outside (g + 16) 8 (ow sp) := by
    unfold Apart at hga4; simp only [ow, outside_cons, outside_nil, and_true]; omega
  have hwsO : ∀ r ∈ ow sp, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [ow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals exact M.accessible_sub hacc4 (Or.inr rfl) (by simp only; omega) (by simp only; omega)
  have hce1 : CallW.CEnv R L1 g sp 4304 1040 M1 := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := CallW.CEnv.frame hce hFO hrgO hwsO hgoO
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hxO.liveSep c11 ?_, c12, c13⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 1040 - (sp - 4304) = 4304 + 1040 by omega]; exact c8
  have hsok1 : StkOK M1 R L1 st := by
    refine ⟨hst8, hxO.held hsth', by rw [hFO.accessible]; exact hstacc, hst48, ?_, by rw [e2, e3]; exact hlc,
      by rw [e3]; exact hcap40⟩
    intro hc
    rw [e3] at hc; rw [e1, e3]
    obtain ⟨q1, q2, q3, q4⟩ := hlive hc
    exact ⟨q1, hxO.held q2, by rw [hFO.accessible]; exact q3, q4⟩
  have hbud1 : stackNatCost (stLen M st) (17 * n) ≤ b1 := by
    by_cases h4 : 4 < n <;> simp only [h4, ite_true, ite_false] at hbO <;> omega
  have hpre1 : SnPre R b1 L1 g sp st (17 * n) M1 := by
    refine ⟨hce1, hserv, hsok1, hstw4, by rw [e1, e3]; exact harr, by omega, by rw [e2]; omega, by rw [e2]; exact hbud1,
      hinvO, by rw [hFO.accessible]; exact hwba, hstwb, by rw [hFE]; exact hstf⟩
  refine snCall impl hap R hSN ret hret _ b1 L1 g sp n st M1 r18 f29 hpre1 (by omega) hn S hpc hsp h0 h1 h30 h18
    h28 h29 hmem ?_
  intro S2 M2 L2 b2 c1 c2 c3 c4 c5 c6 c7 c8 c9 hS
  rw [e2] at c3
  have hS0 := hS
  obtain ⟨hxS2, hbS, hinvS, hsok2, hlen2, hkept, hfresh, hFS, hLS, hrgS⟩ := hS0
  have hx2 : LiveExt R L L2 := hxO.trans hxS2
  have hlc1 : stLen M1 st ≤ stCap M1 st := by rw [e2, e3]; exact hlc
  have harr1 : 0 < stCap M1 st → Apart (stW M1 st) (8 * stCap M1 st) (sp - 4304) (4304 + 1040) ∧
      Apart (stW M1 st) (8 * stCap M1 st) (g + 16) 8 := by rw [e1, e3]; exact harr
  obtain ⟨hba, hbb, hbh, hbw, hbg⟩ := buf_facts hS hlc1 harr1 hrt4 hgrt hn
  rw [e2] at hba hbb hbh hbw hbg
  have hWE : stkWs M1 st = stkWs M st := by simp only [stkWs]; rw [e1, e2, e3]
  rw [hWE] at hFS hLS
  -- frames `oneJ → p01`
  have fr2 : MemFrame M M2 (R.rt ++ (ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M st)) := by
    refine hFO.trans hFS (fun a k h => ⟨?_, ?_⟩)
    · simp only [outside_append] at h ⊢; exact ⟨h.1, h.2.1.1⟩
    · simp only [outside_append] at h ⊢; exact ⟨⟨h.1, h.2.1.2⟩, h.2.2⟩
  have lf2 : LiveFrame M M2 L (stkWs M st) :=
    ⟨fun a k hin hout => by rw [hLS.readLE a k (hxO.inRanges_old hin) hout, hLO.readLE a k hin trivial]⟩
  have hrg2 : M2.regions = M.regions := hrgS.trans hrgO
  have acc2 : ∀ a k w, M2.accessible a k w = M.accessible a k w := fun a k w => by
    rw [hFS.accessible, hFO.accessible]
  have hgo2 : Outside (g + 16) 8 (ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M st) :=
    go2 hK4 hga4 hfe.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hfg hlc
  have hfw' := hfw; have hfg' := hfg; have hstw' := hstw4; have hstg := hfe.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hfw' hfg' hstw' hstg; simp only at hfw' hfg'
  have hws2 : ∀ r ∈ ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M st, r.1 < r.2 →
      M.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr hlt
    simp only [ow, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hw6 : ∀ a k, sp - 4304 ≤ a → a + k ≤ sp + 1040 → M.accessible a k true = true := fun a k h1 h2 =>
      M.accessible_sub hacc4 (Or.inr rfl) h1 (by omega)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
    · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
    · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
    · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
    · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
    · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  have he2 : Env R L2 g sp M2 := by
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := env_frame he fr2 hgo2
    refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, hx2.liveSep d11 ?_⟩
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 1040 - (sp - 4288) = 4288 + 1040 by omega]; exact d8
  have hce2 : CallW.CEnv R L2 g sp 4304 1040 M2 := by
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := CallW.CEnv.frame hce fr2 hrg2 hws2 hgo2
    refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, hx2.liveSep d11 ?_, d12, d13⟩
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 1040 - (sp - 4304) = 4304 + 1040 by omega]; exact d8
  -- reads
  have rdo : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4288) (4288 + 1040) → Apart a k st 24 →
      Apart a k (stFree M st).1 (stFree M st).2 → M2.readLE a k = M.readLE a k :=
    fun a k hh hw hs hf => rd2 hO hS hsth hstw4 hlc hh hw hs hf
  have rs : ∀ K, (32 ≤ K ∧ K + 8 ≤ 336 ∨ 368 ≤ K ∧ K + 8 ≤ 432 ∨ 824 ≤ K ∧ K + 8 ≤ 1040) →
      M2.readLE (sp + K) 8 = M.readLE (sp + K) 8 :=
    fun K hK => slot2 hO hS hsth hstw4 hfw hlc hrt4 hK4 hK
  have rs1 : ∀ a k, sp + 24 ≤ a → a + k ≤ sp + 1040 → M2.readLE a k = M1.readLE a k := by
    intro a k h1 h2
    refine hFS.readLE _ _ ?_
    have hro : Outside a k R.rt := hrt4.of_sub (by omega) (by omega)
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hro, by omega, by omega⟩, by omega, by omega⟩
  have bap : ∀ a k, (InRanges a k L1 ∨ Outside a k R.rt) →
      (stLen M st + StackNat.rnd (17 * n) ≤ stCap M st → Apart a k (stFree M st).1 (stFree M st).2) →
      Apart a k (stW M2 st + 8 * stLen M st) (8 * (17 * n)) := by
    intro a k hh hf
    have := buf_apart hS hlc1 hh (fun h => by rw [hFE]; exact hf (by rw [← e2, ← e3]; exact h))
    rw [e2] at this; exact this
  have inpT : ∀ k p, Inp R L sp k M p → Inp R L2 sp k M2 p := fun k p h =>
    ⟨by rw [acc2]; exact h.1, h.2.1, hx2.held h.2.2.1, h.2.2.2⟩
  have hmr : M2.readLE mp (8 * n) = M.readLE mp (8 * n) := rdo _ _ hm.2.2.1 hm.2.2.2 hmS hmF
  have hxr : M2.readLE xp (8 * n) = M.readLE xp (8 * n) := rdo _ _ hx.2.2.1 hx.2.2.2 hxS hxF
  have hrrr : M2.readLE rrp (8 * n) = M.readLE rrp (8 * n) := rdo _ _ hrr.2.2.1 hrr.2.2.2 hrS hrF
  obtain ⟨hone2, hone12, hbo, hoA⟩ := one_facts hS hxO e1 e2 e3 hlc hcap lah hsth hrt4 hstw4 hfw hK4 hbw honeC hone1O
  have flip : ∀ a k c j, Apart a k c j → Apart c j a k := fun a k c j h => by unfold Apart at h ⊢; omega
  have bapL : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (stFree M st).1 (stFree M st).2 →
      Apart a k (stW M2 st + 8 * stLen M st) (8 * (17 * n)) := fun a k hh hf => bap a k (hh.imp hxO.inRanges_old id)
    (fun _ => hf)
  have hyi' : M2.readLE (yp + 8 * (ylen - 1)) 8 = yi := by
    have hy4 := hy.2.2.2; have hyS' := hyS; have hyF' := hyF
    unfold Apart at hy4 hyS' hyF'
    rw [rdo _ _ ?_ (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega)]
    · exact hyi
    · rcases hy.2.2.1 with h1 | h1
      · exact Or.inl (h1.sub (by omega) (by omega))
      · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hnm2 : NatNorm M2 mp n := by
    rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2; have hmS' := hmS; have hmF' := hmF
      unfold Apart at hm4 hmS' hmF'
      rw [rdo _ _ ?_ (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega)]
      · exact h
      · rcases hm.2.2.1 with h1 | h1
        · exact Or.inl (h1.sub (by omega) (by omega))
        · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hbud2 : b - ((if 4 < n then blockSize (8 * n) true else 0) + stackNatCost (stLen M st) (17 * n)) ≤ b2 := by
    rw [e2] at hbS; exact sub2 hbO hbS
  have hfe2 : FinEnv sp g st n0 r29 ret M2 := by
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hfe
    have hrd : ∀ a, a = sp - 8 ∨ a = sp → M2.readLE a 8 = M.readLE a 8 := by
      intro a ha
      refine fr2.readLE _ _ ?_
      have hro : Outside a 8 R.rt := hrt4.of_sub (by omega) (by omega)
      simp only [ow, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hro, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hgr : M2.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
      fr2.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hgo2⟩)
    have hc2 := hsok2.2.2.2.2.2.1
    refine ⟨f1, f2, f3, by rw [acc2]; exact f4, f5, by rw [acc2]; exact f6, by rw [hgr]; exact f7, f8,
      by rw [rs 912 (by omega)]; exact f9, by rw [rs 840 (by omega)]; exact f10, by rw [rs 848 (by omega)]; exact f11,
      by rw [rs 856 (by omega)]; exact f12, f13, by rw [acc2]; exact f14, ?_, f16, f17,
      by rw [hrd _ (Or.inl rfl)]; exact f18, by rw [hrd _ (Or.inr rfl)]; exact f19⟩
    exact fe15 hn0 e2 hlen2 hc2
  have hz2 : 2 * n ≤ zc → Buf R L2 g sp n M2 zp zc ∧ zp % 8 = 0 := fun h => ⟨buf_ext hx2 (hz h).1 fr2, (hz h).2⟩
  have hold2 : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) (stW M2 st + 8 * stLen M st) (8 * (17 * n)) ∧
      Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) onep (8 * n) ∧ Apart zp (8 * zc) st 24 := by
    intro h
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hold h
    have hb := (hz h).1
    exact ⟨a1, a2, a3, bapL _ _ hb.2.2.2.2.1 a6, a4, hoA _ _ hb.2.2.2.2.1 hb.2.2.2.2.2.1, a5⟩
  refine reaches_mono (p01Ret impl hap R hclr hmv hmk hserv ret hret b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st)
    onep rrp rrc xp xc yp ylen Y yi zp zc zzp zzc st n0 M2 r18 r29 f29 he2 hce2 hn (by omega) hmc hmc' ht (inpT _ _ hm)
    hba hbb hbh (win_sub hK4 hbw) hbg (flip _ _ _ _ (bapL _ _ hm.2.2.1 hmF)) hone2 hbo hone12
    (inpT _ _ hrr) (flip _ _ _ _ (bapL _ _ hrr.2.2.1 hrF)) (inpT _ _ hx) (flip _ _ _ _ (bapL _ _ hx.2.2.1 hxF))
    (by rw [rs 1016 (by omega)]; exact r1016) (by rw [rs 1024 (by omega)]; exact r1024)
    (by rw [rs 1032 (by omega)]; exact r1032) (by rw [rs 224 (by omega)]; exact r224)
    (by rw [rs 128 (by omega)]; exact r128) (by rw [rs1 _ _ (by omega) (by omega)]; exact r816O)
    (by rw [rs 832 (by omega)]; exact r832) (by rw [rs 256 (by omega)]; exact r256)
    (by rw [rs 264 (by omega)]; exact r264) (by rw [rs 904 (by omega)]; exact r904)
    (by rw [rs 328 (by omega)]; exact r328) (by rw [rs 320 (by omega)]; exact r320) hok hinvS hyl hyl' (inpT _ _ hy)
    (bapL _ _ hy.2.2.1 hyF) (by rw [rdo _ _ hy.2.2.1 hy.2.2.2 hyS hyF]; exact hY) hyi' hyi0 hzc hz2 hold2
    (buf_ext hx2 hzz fr2) hzz8 hzzm hzzy (bapL _ _ hzz.2.2.2.2.1 hzzF) hzz4
    (hoA _ _ hzz.2.2.2.2.1 hzz.2.2.2.2.2.1) hzzs hro hty
    (by rw [rs 952 (by omega)]; exact r952) (by rw [rs 936 (by omega)]; exact r936)
    (by rw [rs 168 (by omega)]; exact r168) (by rw [rs 400 (by omega)]; exact r400)
    (by rw [rs 1000 (by omega)]; exact r1000) (by rw [rs 992 (by omega)]; exact r992)
    (fun h => ⟨hokz h, by by_cases h4 : 4 < n <;> simp only [h4, ite_true, ite_false] at hbud2 <;> omega⟩) hokM hmw4 hnm2 (by rw [hmr]; exact hkk) (by rw [hmr]; exact hmB) hfe2
    (hx2.held hsth) hstw4 (bapL _ _ hsth hstf) S2 c1 c2 c3 c4 c5 c6 c7 c8 c9) ?_
  refine isReturn_mono fun s' h => ⟨M2, L2, b2, ⟨?_, lf2, hx2, hbud2, hsok2, by rw [hlen2, e2], ?_, ?_, hrg2⟩, ?_⟩
  · simpa only [List.append_assoc] using fr2
  · intro h; rw [← e1, ← e3]; exact hkept (by rw [e2, e3]; exact h)
  · intro h
    obtain ⟨q1, q2⟩ := hfresh (by rw [e2, e3]; exact h)
    exact ⟨q1, fun r hr => q2 r (hxO.mem_old hr)⟩
  · rw [hmr, hxr, hrrr] at h; exact h

end FvModexp.Arm64.W4Pro
