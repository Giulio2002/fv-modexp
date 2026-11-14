import FvModexp.Proofs.Amd64.Exp.P2W2EnCtx
import FvModexp.Proofs.Amd64.Exp.CallW
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.StkFrame
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the shared context `WC` of every point after the entry (agent divmc s67;
amd64 twin of agent infra's `Arm64.P2W2WC`)

`WC R H L K g sp st zp zc m0 M L1 b1 ℓ`: the memory `M` at a point of the function (entry memory `m0`, entry live set
`L`) differs from `m0` only in the runtime ranges, the function's window `WN` (`[sp - 8 - K, sp + 0x1d0)` = callee
stacks + frame + saved `BP`, and the argument spill area `[sp + 0x1f0, sp + 0x230)`; NOT the return address
`[sp + 0x1d0, sp + 0x1d8)` nor the stack argument `y` `[sp + 0x1d8, sp + 0x1f0)`) and `ZS` (`z`'s array, the stack
header, the entry free part of the stack's array); live objects of `L` keep their bytes outside `ZS`; the live set
`L1` extends `L`, the invariant holds with the effective budget `b1`; the stack is `StkOK` at level `ℓ ≥ ℓ₀` with its
array the entry one or fresh (relative to `L`) and, when fresh, an element of `L1` (`ArrIn`).

Every later segment imports this module (ROW-TIME rule). Transport: `WC.frame` (own writes / a callee that keeps the
stack), `WC.call` (a callee post with a new live set and stack level); reads `WC.read`, `WC.readB`, `stk_out`,
`free_apart`, `free_apart'`; `Scr.rebase`; the entry facts `EPre.win_rt/ws_acc/g_out/fs_out`; the callee environment
`WC.cenv` (`CallW.CEnv … (sp - 8) K 0x238`, as at the entry), `WC.globals`, `WC.win_out`, `oe_bytes`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the window ranges the function writes (entry `RSP = sp + 0x1d0`): callee stacks, frame, saved `BP`; spill area -/
@[reducible] def WN (sp K : Nat) : List (Nat × Nat) := [(sp - 8 - K, sp + 0x1d0), (sp + 0x1f0, sp + 0x230)]

/-- the caller-visible ranges the function writes: `z`'s array, the stack header and the entry free part -/
@[reducible] def ZS (zp zc st : Nat) (m0 : Memory) : List (Nat × Nat) := [(zp, zp + 8 * zc)] ++ stkWs m0 st

/-- the context at every point after the entry (see the module doc) -/
structure WC (R : RtInv) (H : Nat) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory)
    (L1 : List (Nat × Nat)) (b1 ℓ : Nat) : Prop where
  fr : MemFrame m0 M (R.rt ++ WN sp K ++ ZS zp zc st m0)
  lf : LiveFrame m0 M L (ZS zp zc st m0)
  rg : M.regions = m0.regions
  le : LiveExt R L L1
  /-- `b1` is the EFFECTIVE budget: the invariant holds with the unheld stack reserve on top -/
  inv : R.inv (b1 + stkR H M st) L1 g (view R.rt L1 M)
  sok : StkOK M R L1 st
  len : stLen M st = ℓ
  lo : stLen m0 st ≤ ℓ
  lc0 : stLen m0 st ≤ stCap m0 st
  kf : ArrKF R L st m0 M
  ain : ArrIn L1 st m0 M

/-- a read whose every byte is outside the frame's ranges -/
theorem MemFrame.bytewise {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a n : Nat}
    (hb : ∀ i, i < n → Outside (a + i) 1 rs) : m'.readLE a n = m.readLE a n := by
  apply Janus.Arm64.Memory.readLE_congr
  intro i hi
  have := h.readLE (a + i) 1 (hb i hi)
  simp only [Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

section
variable {R : RtInv} {H : Nat} {L : List (Nat × Nat)} {K g sp st zp zc : Nat} {m0 M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a held range (live in `L` or outside the runtime) outside the entry free part is apart from the free part now -/
theorem free_apart (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hf : Apart a k (free m0 st).1 (free m0 st).2) : Apart a k (free M st).1 (free M st).2 := by
  have hc := h.sok.2.2.2.2.2.1
  have hl := h.len
  have hlo := h.lo
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    simp only [Apart] at hf ⊢; rw [e1, e2]; omega
  · have : a + k ≤ stW M st ∨ stW M st + 8 * stCap M st ≤ a := by
      rcases hh with hL | hO
      · have := hap.apart_of_inRanges hL; omega
      · have := hin.apart hO; unfold Apart at this; omega
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    unfold Apart; omega

/-- a held range outside `ZS` is outside the stack's writable ranges now -/
theorem stk_out (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (ho : Outside a k (ZS zp zc st m0)) : Outside a k (stkWs M st) := by
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
  refine ⟨ho.2.1, ?_⟩
  have := h.lc0
  have := free_apart h hh (by simp only [Apart]; omega)
  simp only [Apart] at this
  have hc := h.sok.2.2.2.2.2.1
  omega

/-- the read form: a held range outside the window and `ZS` keeps its bytes -/
theorem WC.read (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hw : Outside a k (WN sp K)) (ho : Outside a k (ZS zp zc st m0)) : M.readLE a k = m0.readLE a k :=
  Expmc.held_readLE hh h.fr h.lf hw ho

/-- a range outside everything the function may write is outside the runtime and the stack's writable ranges now -/
theorem out_all (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat}
    (ho : Outside a k (R.rt ++ WN sp K ++ ZS zp zc st m0)) :
    Outside a k R.rt ∧ Outside a k (WN sp K) ∧ Outside a k (stkWs M st) := by
  rw [outside_append, outside_append] at ho
  exact ⟨ho.1.1, ho.1.2, stk_out h (Or.inr ho.1.1) ho.2⟩

/-- `WC` through a step that writes `ws` and keeps the stack header (the function's own stores, a callee that
does not change the stack object) -/
theorem WC.frame (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {M' : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hsub : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st m0) → Outside a k ws)
    (hL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st m0) → Outside a k ws)
    (hhd : Outside st 24 ws) (hws : ∀ r ∈ ws, InRanges r.1 (r.2 - r.1) L1 ∨ Outside r.1 (r.2 - r.1) R.rt) :
    WC R H L K g sp st zp zc m0 M' L1 b1 ℓ := by
  have e0 : stW M' st = stW M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M' st = stLen M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M' st = stCap M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  refine ⟨h.fr.trans hF fun a k ho => ⟨ho, hsub a k ho⟩,
    ⟨fun a k hin ho => by rw [hF.readLE a k (hL a k hin ho), h.lf.readLE a k hin ho]⟩, hrg.trans h.rg, h.le,
    by rw [stkR_congr e2]; exact Expmc.inv_frame hF hws h.inv, stkOK_hdr h.sok hF e0 e1 e2 (LiveExt.refl R L1),
    by rw [e1]; exact h.len, h.lo, h.lc0, ?_, ?_⟩
  · rcases h.kf with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨e0.trans a1, e2.trans a2⟩
    · exact Or.inr (by rw [e0, e2]; exact ⟨a1, a2⟩)
  · exact h.ain.congr e0 e2 fun _ hr => hr

/-- `WC` through a callee whose post has a new live set `L2`, budget `b2` and stack level `ℓ'` (array kept, or
fresh relative to `L1` and then an element of `L2`) -/
theorem WC.call (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {M' : Memory} {ws ws' : List (Nat × Nat)}
    {L2 : List (Nat × Nat)} {b2 ℓ' : Nat}
    (hF : MemFrame M M' (R.rt ++ ws)) (hLF : LiveFrame M M' L1 ws') (hrg : M'.regions = M.regions)
    (hsub : ∀ a k, Outside a k R.rt → Outside a k (WN sp K) → Outside a k (stkWs M st) →
      Outside a k (ZS zp zc st m0) → Outside a k ws)
    (hL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st m0) → Outside a k ws')
    (hx : LiveExt R L1 L2) (hinv : R.inv (b2 + stkR H M' st) L2 g (view R.rt L2 M')) (hok : StkOK M' R L2 st)
    (hlen : stLen M' st = ℓ') (hle : ℓ ≤ ℓ')
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1))
    (hmem : ArrIn L2 st M M') :
    WC R H L K g sp st zp zc m0 M' L2 b2 ℓ' := by
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => h.le.mem_old hr
  refine ⟨h.fr.trans hF fun a k ho => ⟨ho, ?_⟩, ⟨fun a k hin ho => ?_⟩, hrg.trans h.rg, h.le.trans hx, hinv, hok,
    hlen, by have := h.lo; omega, h.lc0, ?_, h.ain.trans hmem hx⟩
  · obtain ⟨o1, o2, o3⟩ := out_all h ho
    rw [outside_append, outside_append] at ho
    rw [outside_append]
    exact ⟨o1, hsub a k o1 o2 o3 ho.2⟩
  · rw [hLF.readLE a k (h.le.inRanges_old hin) (hL a k hin ho), h.lf.readLE a k hin ho]
  · rcases harr with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rcases h.kf with ⟨b1', b2'⟩ | ⟨b1', b2'⟩
      · exact Or.inl ⟨a1.trans b1', a2.trans b2'⟩
      · exact Or.inr (by rw [a1, a2]; exact ⟨b1', b2'⟩)
    · exact Or.inr ⟨a1, fun r hr => a2 r (hLL r hr)⟩

/-- a scratch nat of a callee (relative to the call memory `M`) is one relative to the entry -/
theorem Scr.rebase (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) {L2 : List (Nat × Nat)} {M' : Memory} {t k : Nat}
    (hs : Scr R L1 L2 M M' st t k) : Scr R L L2 m0 M' st t k := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  refine ⟨s1, s2, s3, s4, ?_⟩
  have hl := h.len
  have hlo := h.lo
  rcases s5 with ⟨c0, c1, c2⟩ | ⟨c1, c2⟩
  · rcases h.kf with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · left; rw [← e1, ← e2]; exact ⟨c0, by omega, c2⟩
    · right; exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
  · right; exact ⟨c1, fun r hr => c2 r (h.le.mem_old hr)⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

theorem EPre.win_rt (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) :
    Outside (sp - 8 - K) (K + 0x238) R.rt := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  exact hrt

theorem EPre.cenv0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) :
    CallW.CEnv R L g fs (sp - 8) K 0x238 s.mem := hP.1.2.2.2.2.2.2.2.2.1

theorem EPre.stk0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) : StkOK s.mem R L st := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  exact ⟨k1, k2, k3, k4, k5, hlc, k7⟩

/-- every range the function writes (besides the runtime's) is writable at the entry -/
theorem EPre.ws_acc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) :
    ∀ r ∈ WN sp K ++ ZS zp zc st s.mem, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  intro r hr hlt
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only at hlt ⊢
  · exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact (hz (by omega)).2.1
  · rw [show st + 24 - st = 24 by omega]; exact k3
  · exact Janus.Arm64.Memory.accessible_mono _ (k5 (by omega)).2.2.1 (by omega) (by omega)

/-- the guard word's bytes are outside every range the function writes (byte-wise: `z`'s array and the free part
may be empty ranges anywhere) -/
theorem EPre.g_out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) :
    ∀ i, i < 8 → Outside (g + 16 + i) 1 (R.rt ++ WN sp K ++ ZS zp zc st s.mem) := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  intro i hi
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
    and_true]
  unfold Apart at hstg hga
  refine ⟨⟨hgrt.of_sub (by omega) (by omega), by omega, by omega⟩, ?_, by omega, ?_⟩
  · rcases Nat.eq_zero_or_pos zc with h0 | h0
    · subst h0; omega
    · have := (hz h0).2.2.2.2.1; unfold Apart at this; omega
  · rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · omega
    · have := (harr h0).2.1; unfold Apart at this; omega

/-- the TLS word's bytes are outside every range the function writes -/
theorem EPre.fs_out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) :
    ∀ i, i < 8 → Outside (fs - 8 + i) 1 (R.rt ++ WN sp K ++ ZS zp zc st s.mem) := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  intro i hi
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
    and_true]
  unfold Apart at hstfs f6
  refine ⟨⟨f5.of_sub (by omega) (by omega), by omega, by omega⟩, ?_, by omega, ?_⟩
  · rcases Nat.eq_zero_or_pos zc with h0 | h0
    · subst h0; omega
    · have := (hz h0).2.2.2.2.2.1; unfold Apart at this; omega
  · rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · omega
    · have := (harr h0).2.2; unfold Apart at this; omega

end

section
variable {R : RtInv} {H : Nat} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat}
    {s : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the callee environment of the entry (`RSP_callee = sp - 8`, window `[sp - 8 - K, sp + 0x230)`) at `M` -/
theorem WC.cenv (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) : CallW.CEnv R L1 g fs (sp - 8) K 0x238 M := by
  have hgM : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := MemFrame.bytewise h.fr hP.g_out
  have hfM : M.readLE (fs - 8) 8 = s.mem.readLE (fs - 8) 8 := MemFrame.bytewise h.fr hP.fs_out
  have hws := hP.ws_acc
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hP.cenv0
  refine ⟨hal, hK0, hA0, by rw [h.fr.accessible]; exact hacc, hg1, by rw [h.fr.accessible]; exact hg2,
    by rw [hgM]; exact hg3, hrt, hga, hgrt, ?_,
    FvModexp.dataLoaded_frame64 hd h.rg hro (by rw [← List.append_assoc]; exact h.fr) hws, hro, f1, f2,
    by rw [h.fr.accessible]; exact f3, by rw [hfM]; exact f4, f5, f6⟩
  refine h.le.liveSep hLs fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr; simp only
  rw [show sp - 8 + 0x238 - (sp - 8 - K) = K + 0x238 by omega]; exact hrt

end

/-- a held range (adapted from `ModInv.held_bytes`): every byte outside the extra ranges keeps its value -/
theorem held_bytesW {rt L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (hh : InRanges a n L ∨ Outside a n rt) (hf : MemFrame m m' (rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (h : ∀ i, i < n → Outside (a + i) 1 ws1 ∧ Outside (a + i) 1 ws2) : m'.readLE a n = m.readLE a n := by
  apply Janus.Arm64.Memory.readLE_congr
  intro i hi
  have hh1 : InRanges (a + i) 1 L ∨ Outside (a + i) 1 rt :=
    hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have := Expmc.held_readLE hh1 hf hl (h i hi).1 (h i hi).2
  simp only [Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

section
variable {R : RtInv} {H : Nat} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat}
    {s : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- byte-wise read through `WC` -/
theorem WC.readB (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hb : ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st s.mem)) :
    M.readLE a k = s.mem.readLE a k :=
  held_bytesW hh h.fr h.lf hb

/-- the bytes of an entry object (`OE`, apart from `z` when `z` is not empty) are outside the function's writes -/
theorem oe_bytes {a k : Nat} (hoe : OE R L sp K st s.mem a k) (hza : 0 < zc → Apart zp (8 * zc) a k) :
    ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st s.mem) := by
  obtain ⟨-, h2, h3, h4⟩ := hoe
  intro i hi
  simp only [Apart] at h2 h3 h4
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨by omega, by omega⟩, ?_, by omega, by omega⟩
  rcases Nat.eq_zero_or_pos zc with h0 | h0
  · subst h0; omega
  · have := hza h0; unfold Apart at this; omega

/-- the stack's array apart from a window range (`Outside` the runtime) whenever its free part is not empty -/
theorem free_apart' (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {a k : Nat} (hrt : Outside a k R.rt)
    (hf : 0 < stCap s.mem st → Apart a k (stW s.mem st) (8 * stCap s.mem st)) :
    stLen M st < stCap M st → Apart a k (free M st).1 (free M st).2 := by
  intro hlt
  have hl := h.len
  have hlo := h.lo
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · have := hf (by rw [← e2]; omega)
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    simp only [Apart] at this ⊢; rw [e1, e2]; rw [e2] at hlt; omega
  · have := hin.apart hrt
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- the globals at `M`, outside any window `w` inside `[sp - 8 - K, sp + 0x230)` and the header -/
theorem WC.globals (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {w : List (Nat × Nat)}
    (hw : ∀ a n, Outside a n [(sp - 8 - K, sp + 0x230), (st, st + 24)] → Outside a n w) :
    RunIface.Globals R M w := by
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  have hgst := hgO.2.2.1
  have hz5 := k5
  have hb := oe_bytes (zp := zp) (zc := zc) hgO fun h0 => (hz h0).2.2.2.2.2.2.2.2
  have hrd : ∀ j, j + 8 ≤ 32 → M.readLE (RunIface.gA + j) 8 = s.mem.readLE (RunIface.gA + j) 8 := fun j hj =>
    h.readB (Or.inr (g9.of_sub (by omega) (by omega))) fun i hi => by
      have := hb (j + i) (by omega); rwa [← Nat.add_assoc] at this
  simp only [outside_cons, outside_nil, and_true] at g10 g13
  have ewb : StackNat.wbA = RunIface.wbA := by decide
  rw [ewb] at hwbA
  unfold Apart at hgst hwbA
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [h.fr.accessible]; exact g8, g9,
    hw _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
    by rw [h.fr.accessible]; exact g11, g12, hw _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
  · rw [g5, hrd 8 (by omega), ← g5]; exact g1
  · rw [g6, hrd 16 (by omega), ← g6]; exact g2
  · rw [g7, hrd 24 (by omega), ← g7]; exact g3
  · have e : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
        RunIface.gA + 0 := by decide
    rw [e, hrd 0 (by omega)]; rw [← e]; exact g4

set_option maxRecDepth 20000 in
/-- the window is outside the runtime ranges and the stack's writable ranges (non-empty stack) -/
theorem WC.win_out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) (hl : 0 < ℓ) :
    ∀ a k, sp - 8 - K ≤ a → a + k ≤ sp + 0x230 → Outside a k (R.rt ++ stkWs M st) := by
  have hout := hP.win_rt
  obtain ⟨⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, ⟨hal', hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro',
    f1, f2, f3, f4, f5, f6⟩, hsv⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hro, hwt, hlm2, hlm, hyO,
    hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc, hzp, hzc, hz, hgO, ⟨k1, k2, k3, k4, k5, hlc, k7⟩,
    hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0, hone, hinv⟩ := hP
  have hlc := h.sok.2.2.2.2.2.1
  have hlen := h.len
  intro a k h1 h2
  rw [outside_append]
  refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
  simp only [stkWs, outside_cons, outside_nil, and_true]
  unfold Apart at hstw
  refine ⟨by omega, ?_⟩
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · have := (harr (by rw [← e2]; omega)).1
    rw [← e1, ← e2] at this; unfold Apart at this; omega
  · have := hin.apart (hout.of_sub (a := a) (n := k) (by omega) (by omega)); unfold Apart at this; omega

end

end FvModexp.Amd64.P2W2
