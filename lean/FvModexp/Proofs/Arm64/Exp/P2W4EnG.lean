import FvModexp.Proofs.Arm64.Exp.P2W4EnG3

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` entry (arm64): `growslice(arr, len + nr, cap, len + nr - cap, Word)` of the inline
`stk.reserve(20w)` → `enG3` (window-4 copy of `P2W2.enG2`, ported from agent expmc's `W2En.enG2`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enG2 (impl : List Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibW.program.link impl) mcE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp K st n w0 len0 cap0 : Nat) (s : State)
    (he : EEnv R L g sp K s) (hk : cap0 < len0 + (20 * n)) (hn : n ≤ 128)
    (hl16 : len0 + 20 * n + 3 ≤ 2 ^ 16) (hw64 : w0 < 2 ^ 64)
    (hold : 0 < cap0 → w0 + 8 * cap0 ≤ 2 ^ 48 ∧ s.mem.accessible w0 (8 * cap0) false = true)
    (hcost : 8 * growCap8 (len0 + (20 * n)) cap0 ≤ b) (hinv : R.inv b L g (view R.rt L s.mem))
    (S : State) (M1 : Memory) (hpc : S.pc = BitVec.ofNat 64 grE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 w0) (h1 : S.regs 1 = BitVec.ofNat 64 (len0 + (20 * n)))
    (h2 : S.regs 2 = BitVec.ofNat 64 cap0) (h3 : S.regs 3 = BitVec.ofNat 64 (len0 + (20 * n) - cap0))
    (h4 : S.regs 4 = BitVec.ofNat 64 wTy) (h30 : S.regs 30 = BitVec.ofNat 64 grRet)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M1)
    (hF : MemFrame s.mem M1 [(sp - 8, sp + 848)])
    (r240 : M1.readLE (sp + 240) 8 = len0 + (20 * n)) (r176 : M1.readLE (sp + 176) 8 = len0)
    (r192 : M1.readLE (sp + 192) 8 = len0 + (20 * n) - cap0) (r232 : M1.readLE (sp + 232) 8 = cap0)
    (r784 : M1.readLE (sp + 784) 8 = st)
    (r248 : M1.readLE (sp + 248) 8 = n)
    (K' : ∀ (S' : State) (M' : Memory) (p gc : Nat),
      S'.pc = BitVec.ofNat 64 enJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st →
      S'.regs 9 = BitVec.ofNat 64 n → S'.regs 13 = BitVec.ofNat 64 p → S'.regs 14 = BitVec.ofNat 64 len0 →
      S'.regs 12 = BitVec.ofNat 64 gc → S'.regs 11 = BitVec.ofNat 64 (len0 + (20 * n)) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = S.regs 29 → S'.mem = M' →
      gc = growCap8 (len0 + (20 * n)) cap0 → InRanges p (8 * gc) R.rt → ApartAll p (8 * gc) L →
      p % 8 = 0 → p + 8 * gc ≤ 2 ^ 48 → M'.accessible p (8 * gc) true = true →
      MemFrame M1 M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 48), (sp + 184, sp + 192), (sp + 312, sp + 320)]) →
      LiveFrame M1 M' L [] →
      M'.regions = M1.regions →
      R.inv (b - 8 * gc) (L ++ [(p, p + 8 * gc)]) g (view R.rt (L ++ [(p, p + 8 * gc)]) M') →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have he' := he
  obtain ⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩ := he'
  have esp := he.sp
  have eg := he.g
  have hrn : (20 * n) ≤ 20 * n + 3 := by omega
  have tsp : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t0 : (S.regs 0).toNat = w0 := by rw [h0, BitVec.toNat_ofNat]; omega
  have t1 : (S.regs 1).toNat = len0 + (20 * n) := by rw [h1, BitVec.toNat_ofNat]; omega
  have t2 : (S.regs 2).toNat = cap0 := by rw [h2, BitVec.toNat_ofNat]; omega
  have t3 : (S.regs 3).toNat = len0 + (20 * n) - cap0 := by rw [h3, BitVec.toNat_ofNat]; omega
  have t4 : (S.regs 4).toNat = 2641088 := by rw [h4, BitVec.toNat_ofNat]; rfl
  have hout : Outside (sp - K) (K + 848) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 848 - (sp - K) = K + 848 by omega] at this
  have hwT : Apart StackNat.wT 16 (sp - K) (K + 848) := apart_of_data hd 1 (by decide) (by decide) hacc
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts hd
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3 hwT
  unfold Apart at hwT
  have hFw : MemFrame s.mem S.mem (R.rt ++ [(sp - K, sp + 848)]) := by
    rw [hmem]; refine hF.mono fun a k h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hinvS : R.inv b L g (view R.rt L S.mem) := by
    rw [hmem]; refine RtInv.inv_frame hF (fun r hr => ?_) hinv
    simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)
  have hc := call_pre R L b (growsliceRound S) grE (growsliceArgs S)
    (s := s) (S := S) (lo := sp - K) (hi := sp + 848) (stack := 4096) (nargs := 5) (fr := 752)
    (by rw [eg]; exact hg1) (by rw [eg]; exact hg2) (by rw [eg, esp]; omega) (by rw [eg]; exact hgo) hFw
    (h28.trans hs28.symm) (by rw [tsp, esp]) (by rw [tsp]; omega) (by rw [h30]; decide) (by rw [h30]; decide)
    (by decide) (by rw [tsp]; omega) (by rw [tsp]; omega) (by rw [tsp]; omega) (by omega)
    (by rw [show sp + 848 - (sp - K) = K + 848 by omega]; exact hacc) hwrt hLs
    (by simp only [growsliceArgs, t0, t1, t2, t3, t4]; rw [← grE_eq]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega))
    (by rw [h28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hinvS)
    (by simp only [growsliceRound, t1, t2]; exact hcost)
  refine ReachesRet.call_regions ((hgr L b)) hpc
    ⟨⟨⟨hc.1, ?ty1, ?ty2, ?ty3, by omega, by omega, by omega, by omega⟩, fun hp => ?old⟩, hc.2⟩ ?_
  case ty1 => rw [t4]; exact ⟨by omega, by rw [hFw.accessible]; exact ht3⟩
  case ty2 =>
    simp only [typSize, t4]; rw [hmem, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact ht1
  case ty3 =>
    simp only [typPtrBytes, t4]; rw [hmem, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact ht2
  case old =>
    unfold GrowsliceOld
    have e : (S.regs 1).toNat - (S.regs 3).toNat = cap0 := by rw [t1, t3]; omega
    rw [e] at hp ⊢
    obtain ⟨a1, a2⟩ := hold hp
    rw [t0, hmem, hF.accessible]; exact ⟨a1, a2⟩
  intro S1 hpc1 ⟨ptr, junk, f1, v1, m1, ex1, ep1, hs1, hMF, hLF, ⟨hobj, hapL⟩, hapS, hinv1⟩ hrg
  subst hs1
  have hround : growsliceRound S = 8 * growCap8 (len0 + (20 * n)) cap0 := by
    simp only [growsliceRound, t1, t2]
  simp only [growsliceObj, Fresh, t1, t2, t3] at hobj
  rw [hround] at hapL hinv1
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, -, -⟩ := hobj
  have hgcl := le_growCap8 (len0 + (20 * n)) cap0
  have hgcb : growCap8 (len0 + 20 * n) cap0 < 2 ^ 40 := by
    have := growCap_lt len0 (20 * n) cap0 (by omega) (by omega)
    rwa [show (20 * n + 3) / 4 * 4 = 20 * n by omega] at this
  have egc : growCap8 (len0 + (20 * n)) cap0 = growCap8 (len0 + (20 * n)) cap0 := rfl
  have hpw := hpin.apart hout
  unfold Apart at hpw
  simp only [calleeStack, tsp, hmem] at hMF hLF hrg hinv1
  have hrd : ∀ a, sp + 48 ≤ a → a + 8 ≤ sp + 848 → m1.readLE a 8 = M1.readLE a 8 := by
    intro a ha1 ha2
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have q240 := (hrd _ (by omega) (by omega)).trans r240
  have q176 := (hrd _ (by omega) (by omega)).trans r176
  have q192 := (hrd _ (by omega) (by omega)).trans r192
  have q232 := (hrd _ (by omega) (by omega)).trans r232
  have hp64 : ptr.toNat < 2 ^ 64 := ptr.isLt
  have esub : BitVec.ofNat 64 cap0 + BitVec.ofNat 64 (len0 + (20 * n)) -
      BitVec.ofNat 64 (len0 + (20 * n)) = BitVec.ofNat 64 cap0 := BitVec.add_sub_cancel _ _
  have hl3 := lsl3_ofNat (len0 + (20 * n) - cap0) (by omega)
  have hl3c := lsl3_ofNat cap0 (by omega)
  have h30' : S.regs 30 = 1793164#64 := h30
  generalize e18 : S.regs 18 = x18 at K'
  generalize e29 : S.regs 29 = x29 at K'
  janus_run [q240, q176, q192, q232, h30', h1, esub, hl3, hl3c, tsp] until [mcE]
  have hst2 : MemFrame m1 ((m1.writeLE (sp + 184) 8 (growCap8 (len0 + (20 * n)) cap0)).writeLE (sp + 312) 8 ptr.toNat)
      [(sp + 184, sp + 192), (sp + 312, sp + 320)] := by janus_frame
  have hF1 : MemFrame s.mem ((m1.writeLE (sp + 184) 8 (growCap8 (len0 + (20 * n)) cap0)).writeLE (sp + 312) 8 ptr.toNat)
      (R.rt ++ [(sp - K, sp + 848)]) := by
    refine MemFrame.trans (rs'' := R.rt ++ [(sp - K, sp + 848)]) (MemFrame.trans (rs'' := R.rt ++ [(sp - K, sp + 848)])
      (hmem ▸ hFw : MemFrame s.mem M1 _) hMF fun a k ho => ?_) hst2 fun a k ho => ?_
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, ho.2⟩, ho.1, by omega, by omega⟩
    · refine ⟨ho, ?_⟩
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hk2 : ∀ a, sp + 48 ≤ a → a + 8 ≤ sp + 848 → (a + 8 ≤ sp + 184 ∨ sp + 192 ≤ a) → (a + 8 ≤ sp + 312 ∨ sp + 320 ≤ a) →
      ((m1.writeLE (sp + 184) 8 (growCap8 (len0 + (20 * n)) cap0)).writeLE (sp + 312) 8 ptr.toNat).readLE a 8 = M1.readLE a 8 := fun a h1 h2 h3 h4 => by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hrd a h1 h2
  have hinv2 := RtInv.inv_frame hst2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)) hinv1
  rw [h28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hinv2
  refine enG3 impl R hmc ret0 Q b L g sp K st n len0 cap0 ptr.toNat (growCap8 (len0 + (20 * n)) cap0) s he hk (by omega)
    hgcb hn (by omega) hpin hp48 (hal8 (Or.inr (by omega))) _ ((m1.writeLE (sp + 184) 8 (growCap8 (len0 + (20 * n)) cap0)).writeLE (sp + 312) 8 ptr.toNat) ?_ ?_ ?_ ?_ ?_ ?_ rfl hF1
    (by simp only [Memory.accessible_writeLE]; exact hpacc) hinv2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left 6
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), q176]
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), q240]
  · rw [hk2 _ (by omega) (by omega) (by omega) (by omega)]; exact r784
  · rw [hk2 _ (by omega) (by omega) (by omega) (by omega)]; exact r248
  · intro S' M' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hMF' hLF' hrg' hinv'
    have hLw2 : LiveSep L [(sp + 184, sp + 192), (sp + 312, sp + 320)] := fun r hr => by
      have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    have hdsep : LiveSep L [(ptr.toNat + 8 * cap0, ptr.toNat + 8 * (len0 + (20 * n)))] := fun r hr => by
      have := hapL r hr; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    refine K' S' M' ptr.toNat (growCap8 (len0 + (20 * n)) cap0) a1 a2 a3 a4 a5 a6 a7 a8
      ?_ a10 ?_ a12 rfl hpin hapL (hal8 (Or.inr (by omega))) hp48 ?_ ?_ ?_ ?_ hinv'
    · exact a9.trans (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact e18)
    · exact a11.trans (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact e29)
    · rw [hMF'.accessible]; simp only [Memory.accessible_writeLE]; exact hpacc
    · refine MemFrame.trans (rs'' := R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 48), (sp + 184, sp + 192),
          (sp + 312, sp + 320)])
        (MemFrame.trans (rs'' := R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 48), (sp + 184, sp + 192),
          (sp + 312, sp + 320)]) hMF hst2 fun a k ho => ?_) hMF' fun a k ho => ?_
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨⟨ho.1, by omega⟩, by omega⟩
      · refine ⟨ho, ?_⟩
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega⟩
    · exact (hLF.trans (LiveFrame.of_win hst2 hLw2) fun a n h => h).trans
        (LiveFrame.of_sep hLF' hdsep fun r hr => List.mem_append_left _ hr) fun a n h => h
    · rw [hrg', Memory.regions_writeLE, Memory.regions_writeLE]; exact hrg
  all_goals first | (janus_simp; done) | skip
  all_goals (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.P2W4
