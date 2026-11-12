import FvModexp.Proofs.Arm64.Exp.P2W2Defs
import FvModexp.Proofs.Arm64.Nat.StackNatCall

/-!
# `expNNPowerOfTwoWindowSize2` entry (arm64): the grow path of the inline `stk.reserve(8w)` (`slices.Grow`, nat.go:335)

`enG3`: entry of `memclrNoHeapPointers(p + 8·cap, 8·(len + nr - cap))` → the join `enJ`;
(`nr = 8w`, `n := w`); `enG2` (P2W2EnG) is the growslice part.
Ported from agent expmc's window-2 `W2En.enG3/enG2` (themselves adapted from divmc's `(*stack).nat` grow path):
frame 464, window `[sp - K, sp + 560)`, slots `240` (len+nr), `176` (len), `192` (len+nr-cap), `232` (cap),
`312` (new array), `184` (new cap), `248` (w).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the call environment of the entry segment (entry state `s`, frame `sp = SP(s) - 464`, window `[sp - K, sp + 560)`) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g sp K : Nat) (s : State) : Prop :=
  s.sp = BitVec.ofNat 64 (sp + 464) ∧ s.regs 28 = BitVec.ofNat 64 g ∧
  g + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (g + 16) 8 false = true ∧ s.mem.readLE (g + 16) 8 + K < sp ∧
  Outside (g + 16) 8 ((sp - K, sp + 560) :: R.rt) ∧ sp % 16 = 0 ∧ 4304 ≤ K ∧ K ≤ sp ∧ sp + 560 ≤ 2 ^ 48 ∧
  s.mem.accessible (sp - K) (K + 560) true = true ∧ LiveSep [(sp - K, sp + 560)] R.rt ∧
  LiveSep L [(sp - K, sp + 560)] ∧ Extracted.program.DataLoaded s.mem ∧ RunIface.Serves R

theorem EEnv.sp {R : RtInv} {L : List (Nat × Nat)} {g sp K : Nat} {s : State} (h : EEnv R L g sp K s) :
    s.sp.toNat = sp + 464 := by
  rw [h.1, BitVec.toNat_ofNat]; have := h.2.2.2.2.2.2.2.2.2.1; omega

theorem EEnv.g {R : RtInv} {L : List (Nat × Nat)} {g sp K : Nat} {s : State} (h : EEnv R L g sp K s) :
    (s.regs 28).toNat = g := by
  rw [h.2.1, BitVec.toNat_ofNat]; have := h.2.2.1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enG3 (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibW.program.link impl) mcE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp K st n len0 cap0 p gc : Nat) (s : State)
    (he : EEnv R L g sp K s) (hk : cap0 < len0 + (8 * n)) (hgc : len0 + (8 * n) ≤ gc)
    (hgc40 : gc < 2 ^ 40) (hn : n ≤ 128) (hl16 : len0 ≤ 2 ^ 16)
    (hpin : InRanges p (8 * gc) R.rt) (hp48 : p + 8 * gc ≤ 2 ^ 48) (hal8 : p % 8 = 0)
    (S : State) (M : Memory) (hpc : S.pc = BitVec.ofNat 64 mcE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h30 : S.regs 30 = BitVec.ofNat 64 mcRet)
    (h0 : S.regs 0 = BitVec.ofNat 64 (p + 8 * cap0))
    (h1 : S.regs 1 = BitVec.ofNat 64 (8 * (len0 + (8 * n) - cap0))) (hmem : S.mem = M)
    (hF : MemFrame s.mem M (R.rt ++ [(sp - K, sp + 560)]))
    (hpacc : M.accessible p (8 * gc) true = true)
    (hinv : R.inv (b - 8 * gc) (L ++ [(p, p + 8 * gc)]) g (view R.rt (L ++ [(p, p + 8 * gc)]) M))
    (r184 : M.readLE (sp + 184) 8 = gc) (r176 : M.readLE (sp + 176) 8 = len0) (r312 : M.readLE (sp + 312) 8 = p)
    (r240 : M.readLE (sp + 240) 8 = len0 + (8 * n)) (r496 : M.readLE (sp + 496) 8 = st)
    (r248 : M.readLE (sp + 248) 8 = n)
    (K' : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 enJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 13 = BitVec.ofNat 64 p → S'.regs 14 = BitVec.ofNat 64 len0 →
      S'.regs 12 = BitVec.ofNat 64 gc → S'.regs 9 = BitVec.ofNat 64 (len0 + (8 * n)) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = S.regs 29 →
      S'.mem = M' → MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 24)]) →
      LiveFrame M M' (L ++ [(p, p + 8 * gc)]) [(p + 8 * cap0, p + 8 * (len0 + (8 * n)))] →
      M'.regions = M.regions →
      R.inv (b - 8 * gc) (L ++ [(p, p + 8 * gc)]) g (view R.rt (L ++ [(p, p + 8 * gc)]) M') →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have he' := he
  obtain ⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩ := he'
  have esp := he.sp
  have eg := he.g
  have hrn : (8 * n) ≤ 8 * n + 3 := by omega
  have tsp : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t0 : (S.regs 0).toNat = p + 8 * cap0 := by rw [h0, BitVec.toNat_ofNat]; omega
  have t1 : (S.regs 1).toNat = 8 * (len0 + (8 * n) - cap0) := by rw [h1, BitVec.toNat_ofNat]; omega
  have hout : Outside (sp - K) (K + 560) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 560 - (sp - K) = K + 560 by omega] at this
  have hpw := hpin.apart hout
  unfold Apart at hpw
  have hLw : LiveSep (L ++ [(p, p + 8 * gc)]) [(sp - K, sp + 560)] := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [outside_cons, outside_nil, and_true]; omega
  have hc := call_pre R (L ++ [(p, p + 8 * gc)]) (b - 8 * gc) 0 mcE [(S.regs 0).toNat, (S.regs 1).toNat]
    (s := s) (S := S) (lo := sp - K) (hi := sp + 560) (stack := 4096) (nargs := 2) (fr := 464)
    (by rw [eg]; exact hg1) (by rw [eg]; exact hg2) (by rw [eg, esp]; omega) (by rw [eg]; exact hgo) (by rw [hmem]; exact hF)
    (h28.trans hs28.symm) (by rw [tsp, esp]) (by rw [tsp]; omega) (by rw [h30]; decide) (by rw [h30]; decide)
    (by decide) (by rw [tsp]; omega) (by rw [tsp]; omega) (by rw [tsp]; omega) (by omega)
    (by rw [show sp + 560 - (sp - K) = K + 560 by omega]; exact hacc) hwrt hLw
    (by rw [← mcE_eq, t1]; exact hsv.2.2.1 _ _ (by omega))
    (by rw [h28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hmem]; exact hinv)
    (Nat.zero_le _)
  obtain ⟨hco, ⟨hgk, hgout⟩, hok', hinv', -, hcs1, hcs2⟩ := hc
  refine ReachesRet.call_regions ((hmc _ _)) hpc
    ⟨⟨(guardOK_iff _ _).1 hgk, hco, hgout⟩, ⟨hok', hinv', hcs1, hcs2⟩, by rw [t0, t1]; omega, ?acc, ?cs, ?dest⟩ ?_
  case acc => rw [t0, t1, hmem]; exact Memory.accessible_mono _ hpacc (by omega) (by omega)
  case cs => simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [t0, t1, tsp]; omega
  case dest =>
    left; rw [t0, t1]
    exact ⟨(p, p + 8 * gc), List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
      by simp only; omega⟩
  intro S3 hpc3 ⟨junk, f3, v3, m3, ex3, ep3, hs3, hMF3, hLF3, hinv3, _⟩ hrg
  subst hs3
  simp only [calleeStack, tsp, t0, t1, hmem] at hMF3 hLF3 hrg
  have hrd : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 560 → m3.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hMF3.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
    have := (hpin.sub (a := p + 8 * cap0) (n := 8 * (len0 + (8 * n) - cap0)) (by omega)
      (by omega)).apart (hout.of_sub (a := a) (n := 8) (by omega) (by omega))
    unfold Apart at this; omega
  have q184 := (hrd _ (by omega) (by omega)).trans r184
  have q176 := (hrd _ (by omega) (by omega)).trans r176
  have q312 := (hrd _ (by omega) (by omega)).trans r312
  have q240 := (hrd _ (by omega) (by omega)).trans r240
  have q496 := (hrd _ (by omega) (by omega)).trans r496
  have q248 := (hrd _ (by omega) (by omega)).trans r248
  have hacc3 : m3.accessible (sp - K) (K + 560) true = true := by
    rw [hMF3.accessible, hF.accessible]; exact hacc
  have h30' : S.regs 30 = 1795368#64 := h30
  generalize e18 : S.regs 18 = x18 at K'
  generalize e29 : S.regs 29 = x29 at K'
  janus_run [q184, q176, q312, q240, q496, q248, h30', tsp] until [enJ]
  refine K' _ m3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?lf ?rg ?inv
  case mf =>
    refine hMF3.mono fun a k h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    refine ⟨⟨h.1, by omega, by omega⟩, ?_⟩
    have := (hpin.sub (a := p + 8 * cap0) (n := 8 * (len0 + (8 * n) - cap0)) (by omega)
      (by omega)).apart h.1
    unfold Apart at this; omega
  case lf =>
    rw [show p + 8 * cap0 + 8 * (len0 + (8 * n) - cap0) =
      p + 8 * (len0 + (8 * n)) by omega] at hLF3; exact hLF3
  case rg => exact hrg
  case inv =>
    simp only [callRegs_apply, h28] at hinv3
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hinv3
  all_goals first | (janus_simp; done) | skip
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]
  all_goals first | janus_assumption | skip


end FvModexp.Arm64.P2W2
