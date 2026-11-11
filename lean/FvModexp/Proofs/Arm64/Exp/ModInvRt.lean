import FvModexp.Proofs.Arm64.Exp.ModInvAlloc

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): runtime facts across a call (agent infra)

`rtM_call`: `RtM` (writes so far in `R.rt`, the window, `z`'s array, the stack's writable parts) survives a call whose
frame `R.rt ++ ws` stays inside those ranges (for the memory) and whose `ws` meets no live object of the entry live set
outside them; the stack object comes back by the callee's `StackBack`. `alloc_jm`: the facts `JM` needs after the
allocating `z.make`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

theorem apartAll_old {R : RtInv} {L L1 : List (Nat × Nat)} (h : LiveExt R L L1) {p n : Nat}
    (ha : ApartAll p n L1) : ApartAll p n L := fun r hr => ha r (h.mem_old hr)

theorem rtM_call {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {s : State} {zp zc st : Nat} {M0 M1 : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 : Nat} {ws : List (Nat × Nat)}
    (hrt : RtM R kc L s zp zc st M0 L1 b1) (hreg : M1.regions = M0.regions) (hF : MemFrame M0 M1 (R.rt ++ ws))
    (hws : ∀ a k, Outside a k (R.rt ++ winA s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (R.rt ++ ws))
    (hLF : LiveFrame M0 M1 L1 ws)
    (hwsL : ∀ a k, InRanges a k L → Outside a k ([(zp, zp + 8 * zc)] ++ stWs s.mem st) → Outside a k ws)
    (hLE : LiveExt R L1 L2) (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M1))
    (hstk : StackBack R L1 L2 st M0 M1) : RtM R kc L s zp zc st M1 L2 b2 := by
  obtain ⟨r0, F0, LF0, LE0, -, -, len0, arr0⟩ := hrt
  obtain ⟨hk1, hk2, hk3⟩ := hstk
  refine ⟨hreg.trans r0, F0.trans hF (fun a k h => ⟨h, hws a k h⟩),
    ⟨fun a k hin hout => (hLF.readLE a k (LE0.inRanges_old hin) (hwsL a k hin hout)).trans (LF0.readLE a k hin hout)⟩,
    LE0.trans hLE, hinv, hk1, hk2.trans len0, ?_⟩
  rcases hk3 with ⟨e1, e2⟩ | ⟨i1, i2⟩
  · rw [e1, e2]; exact arr0
  · exact Or.inr ⟨i1, apartAll_old LE0 (apartAll_old (L1 := L1) (LiveExt.refl R L1) i2)⟩

/-- a fresh runtime object is apart from every held range -/
theorem fresh_apart {R : RtInv} {L : List (Nat × Nat)} {p n a k : Nat} (hIn : InRanges p n R.rt) (hAp : ApartAll p n L)
    (h : Held R L a k) : Apart p n a k := by
  rcases h with h | h
  · obtain ⟨r, hr, h1, h2⟩ := h
    have := hAp r hr; unfold Apart at this ⊢; omega
  · obtain ⟨r, hr, h1, h2⟩ := hIn
    have := MemFrame.outside_mem h hr; unfold Apart; omega

/-- a fresh runtime object is outside a range that is outside the runtime ranges -/
theorem fresh_out {R : RtInv} {p n a k : Nat} (hIn : InRanges p n R.rt) (h : Outside a k R.rt) : Apart p n a k := by
  obtain ⟨r, hr, h1, h2⟩ := hIn
  have := MemFrame.outside_mem h hr; unfold Apart; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the facts at `JM` after the allocating `z.make(numWords + 1)` (pure) -/
theorem alloc_jm {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {Mc m : Memory} {p r k : Nat}
    (hF0 : MemFrame s.mem Mc (winA s (K kc) A)) (hreg0 : Mc.regions = s.mem.regions)
    (hfw : Fw1 s Mc st xp xl xc n k)
    (hap : AllocPost R L b (s.regs 28).toNat (s.sp.toNat - 240) (NW n) Mc m p r) :
    Fw1 s m st xp xl xc n k ∧ RtM R kc L s zp zc st m (L ++ [(p, p + r)]) (b - r) ∧
      b - makeCost (NW n + 1) ≤ b - r ∧ Own R kc L (L ++ [(p, p + r)]) s zp zc st xp xl m p (NW n + 5) := by
  have hrt := rt0 hkc hpre hF0 hreg0
  obtain ⟨⟨-, ⟨-, hal, -, -⟩, -, hout, hga, hgrt, hLs, -⟩, -, -, hn1, hn2, -, -, -, -, -, -, -, -,
    ⟨-, -, -, hxh, -⟩, -, -, -, ⟨-, hstw, hsta⟩, -, -, -, -, -, -⟩ := hpre
  obtain ⟨hMF, hLF, hrg, hIn, hAp, hle, hacc, h8, hsz, hbr, hinv⟩ := hap
  have hstk := hrt.1.2.2.2.2.2.1
  have hmc : makeCost (NW n + 1) = allocCost (8 * (NW n + 5)) := by
    unfold makeCost makeCap; rw [if_neg (show ¬ (NW n + 1 = 1) by simp only [NW]; omega)]
  have hbl := blockSize_le_allocCost (8 * (NW n + 5)) true
  simp only [K, A] at hal hout hga hstw
  simp only [NW] at hMF hsz hbr hacc hmc hbl ⊢
  have hws : ∀ a k, Outside a k (winA s (240 + kc) 72) →
      Outside a k [(s.sp.toNat - 240 - 4096, s.sp.toNat - 240 - 8), (s.sp.toNat - 240 + 8, s.sp.toNat - 240 + 32),
        (s.sp.toNat - 240 + 104, s.sp.toNat - 240 + 112), (s.sp.toNat - 240 + 144, s.sp.toNat - 240 + 152)] := by
    intro a k h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hwo : Outside (s.sp.toNat - (240 + kc)) (240 + kc + 72) R.rt := hout
  have hrd : ∀ a, s.sp.toNat - (240 + kc) ≤ a → a + 8 ≤ s.sp.toNat - 240 - 4096 ∨
      (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232) ∨
      (s.sp.toNat - 240 + 32 ≤ a ∧ a + 8 ≤ s.sp.toNat - 240 + 104) ∨
      (s.sp.toNat - 240 + 112 ≤ a ∧ a + 8 ≤ s.sp.toNat - 240 + 144) ∨
      (s.sp.toNat - 240 + 152 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72) → m.readLE a 8 = Mc.readLE a 8 := by
    intro a h1 h2
    refine hMF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwo.of_sub h1 (by omega), by omega, by omega, by omega, by omega⟩
  obtain ⟨⟨f1, f2⟩, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hfw
  have hLF' : LiveFrame Mc m L [(s.sp.toNat - 240 - 4096, s.sp.toNat - 240 - 8),
      (s.sp.toNat - 240 + 8, s.sp.toNat - 240 + 32), (s.sp.toNat - 240 + 104, s.sp.toNat - 240 + 112),
      (s.sp.toNat - 240 + 144, s.sp.toNat - 240 + 152)] :=
    ⟨fun a k h _ => hLF.readLE a k h (by simp only [outside_nil])⟩
  have hLE : LiveExt R L (L ++ [(p, p + r)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hstO : Outside (s.regs 28).toNat 0 [] := by simp only [outside_nil]
  have hhdr : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = Mc.readLE (st + j) 8 := by
    intro j hj
    refine Held.readLE ((hstk.2.1).sub (by omega) (by omega)) hMF hLF' ?_
    have h := hstw.of_sub (a := st + j) (n := 8) (by omega) (by omega)
    exact hws _ _ (by simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
  have e0 : stW m st = stW Mc st := by have := hhdr 0 (by omega); simpa using this
  have e1 : stLen m st = stLen Mc st := hhdr 8 (by omega)
  have e2 : stCap m st = stCap Mc st := hhdr 16 (by omega)
  have hsb : StackBack R L (L ++ [(p, p + r)]) st Mc m := stackBack_hdr hstk hMF e0 e1 e2 hLE
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rtM_call hrt.1 hrg hMF ?_ hLF' ?_ hLE hinv hsb, by omega, ?_⟩
  · rw [hrd _ (by omega) (by omega)]; exact f1
  · rw [hrd _ (by omega) (by omega)]; exact f2
  · rw [hrd _ (by omega) (by omega)]; exact f3
  · rw [hrd _ (by omega) (by omega)]; exact f4
  · rw [hrd _ (by omega) (by omega)]; exact f5
  · rw [hrd _ (by omega) (by omega)]; exact f6
  · rw [hrd _ (by omega) (by omega)]; exact f7
  · rw [hrd _ (by omega) (by omega)]; exact f8
  · rw [hrd _ (by omega) (by omega)]; exact f9
  · rw [hrd _ (by omega) (by omega)]; exact f10
  · intro a k h; simp only [outside_append] at h ⊢; exact ⟨h.1.1.1, hws a k h.1.1.2⟩
  · intro a k hin _
    obtain ⟨q, hq, h1, h2⟩ := hin
    have := hLs q hq
    simp only [win, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega
  · have hc : 8 * ((n + 63) / 64 + 5) ≤ r := hsz
    have hIn' : InRanges p (8 * ((n + 63) / 64 + 5)) R.rt := hIn.sub (Nat.le_refl _) (by omega)
    have hAp' : ApartAll p (8 * ((n + 63) / 64 + 5)) L := fun q hq => by
      have := hAp q hq; unfold Apart at this ⊢; omega
    have hw1 := fresh_out hIn' hwo
    unfold Apart at hw1
    refine ⟨by omega, by omega, fun _ => ⟨h8, Or.inl ⟨(p, p + r), by simp, by omega, by simp only; omega⟩, hacc,
      by omega⟩, Or.inr ⟨hIn', hAp'⟩, by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega,
      fresh_out hIn' hgrt, fresh_apart hIn' hAp' hxh, fun _ => ⟨fresh_apart hIn' hAp' hstk.2.1, ?_⟩⟩
    rw [e0, e1, e2]
    intro hlt
    obtain ⟨-, hh, -, -⟩ := hstk.2.2.2.2.1 (by omega)
    exact fresh_apart hIn' hAp' (hh.sub (by omega) (by rw [Nat.mul_sub]; omega))

/-- the frame environment at a memory reached by stack-only stores -/
theorem env_of {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} (hF : MemFrame s.mem M (winA s (K kc) A)) :
    Env R L (s.regs 28).toNat (s.sp.toNat - 240) kc M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, hLs, -⟩, -⟩ := hpre
  simp only [K, A] at hw hout hb' ha hga hg3 hLs
  unfold Apart at hga
  have hgr : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hF.readLE _ _ (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
  refine ⟨by omega, by omega, by omega, ?_, hg1, by rw [hF.accessible]; exact hg2, by rw [hgr]; omega, ?_, ?_, hgrt, ?_⟩
  · rw [hF.accessible]; rw [show s.sp.toNat - 240 - kc = s.sp.toNat - (240 + kc) by omega,
      show kc + 312 = 240 + kc + 72 by omega]; exact hw
  · rw [show s.sp.toNat - 240 - kc = s.sp.toNat - (240 + kc) by omega, show kc + 312 = 240 + kc + 72 by omega]
    exact hout
  · unfold Apart; omega
  · intro q hq
    have := hLs q hq
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega

end FvModexp.Arm64.ModInv
