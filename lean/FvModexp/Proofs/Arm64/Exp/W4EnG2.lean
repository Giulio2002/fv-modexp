import FvModexp.Proofs.Arm64.Exp.W4EnG

/-!
# window-4 entry (arm64): `growslice(w, len + nr, cap, len + nr - cap, Word)` of the inline `stk.reserve(23n)` → `enJ`
(adapted from agent divmc's `(*stack).nat` `g2`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enG2 (impl : List Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract (LibExp.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibExp.program.link impl) mcE 4096 R)
    (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp K st xp xl xc ylen mp n w0 len0 cap0 : Nat) (s : State)
    (he : EEnv R L g sp K s) (hk : cap0 < len0 + StackNat.rnd (23 * n)) (hn : n ≤ 128)
    (hl16 : len0 + 23 * n + 3 ≤ 2 ^ 16) (hw64 : w0 < 2 ^ 64)
    (hold : 0 < cap0 → w0 + 8 * cap0 ≤ 2 ^ 48 ∧ s.mem.accessible w0 (8 * cap0) false = true)
    (hcost : 8 * growCap8 (len0 + StackNat.rnd (23 * n)) cap0 ≤ b) (hinv : R.inv b L g (view R.rt L s.mem))
    (S : State) (M1 : Memory) (hpc : S.pc = BitVec.ofNat 64 grE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 w0) (h1 : S.regs 1 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)))
    (h2 : S.regs 2 = BitVec.ofNat 64 cap0) (h3 : S.regs 3 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n) - cap0))
    (h4 : S.regs 4 = BitVec.ofNat 64 wTy) (h30 : S.regs 30 = BitVec.ofNat 64 grRet)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M1)
    (hF : MemFrame s.mem M1 [(sp - 8, sp + 1040)])
    (r328 : M1.readLE (sp + 328) 8 = len0 + StackNat.rnd (23 * n)) (r192 : M1.readLE (sp + 192) 8 = len0)
    (r216 : M1.readLE (sp + 216) 8 = len0 + StackNat.rnd (23 * n) - cap0) (r320 : M1.readLE (sp + 320) 8 = cap0)
    (r960 : M1.readLE (sp + 960) 8 = st)
    (r968 : M1.readLE (sp + 968) 8 = xp) (r976 : M1.readLE (sp + 976) 8 = xl) (r984 : M1.readLE (sp + 984) 8 = xc)
    (r1000 : M1.readLE (sp + 1000) 8 = ylen) (r1016 : M1.readLE (sp + 1016) 8 = mp)
    (r1024 : M1.readLE (sp + 1024) 8 = n)
    (K' : ∀ (S' : State) (M' : Memory) (p gc : Nat),
      S'.pc = BitVec.ofNat 64 enJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 xp → S'.regs 5 = BitVec.ofNat 64 xl →
      S'.regs 6 = BitVec.ofNat 64 xc → S'.regs 8 = BitVec.ofNat 64 ylen → S'.regs 10 = BitVec.ofNat 64 mp →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 13 = BitVec.ofNat 64 p → S'.regs 14 = BitVec.ofNat 64 len0 →
      S'.regs 15 = BitVec.ofNat 64 gc → S'.regs 9 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = S.regs 29 → S'.mem = M' →
      gc = growCap8 (len0 + StackNat.rnd (23 * n)) cap0 → InRanges p (8 * gc) R.rt → ApartAll p (8 * gc) L →
      p % 8 = 0 → p + 8 * gc ≤ 2 ^ 48 → M'.accessible p (8 * gc) true = true →
      MemFrame M1 M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 424)]) → LiveFrame M1 M' L [] →
      M'.regions = M1.regions →
      R.inv (b - 8 * gc) (L ++ [(p, p + 8 * gc)]) g (view R.rt (L ++ [(p, p + 8 * gc)]) M') →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  have he' := he
  obtain ⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩ := he'
  have esp := he.sp
  have eg := he.g
  have hrn : StackNat.rnd (23 * n) ≤ 23 * n + 3 := by simp only [StackNat.rnd]; omega
  have tsp : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t0 : (S.regs 0).toNat = w0 := by rw [h0, BitVec.toNat_ofNat]; omega
  have t1 : (S.regs 1).toNat = len0 + StackNat.rnd (23 * n) := by rw [h1, BitVec.toNat_ofNat]; omega
  have t2 : (S.regs 2).toNat = cap0 := by rw [h2, BitVec.toNat_ofNat]; omega
  have t3 : (S.regs 3).toNat = len0 + StackNat.rnd (23 * n) - cap0 := by rw [h3, BitVec.toNat_ofNat]; omega
  have t4 : (S.regs 4).toNat = 2641088 := by rw [h4, BitVec.toNat_ofNat]; rfl
  have hout : Outside (sp - K) (K + 1040) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1040 - (sp - K) = K + 1040 by omega] at this
  have hwT : Apart StackNat.wT 16 (sp - K) (K + 1040) := apart_of_data hd 1 (by decide) (by decide) hacc
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts hd
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3 hwT
  unfold Apart at hwT
  have hFw : MemFrame s.mem S.mem (R.rt ++ [(sp - K, sp + 1040)]) := by
    rw [hmem]; refine hF.mono fun a k h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hinvS : R.inv b L g (view R.rt L S.mem) := by
    rw [hmem]; refine RtInv.inv_frame hF (fun r hr => ?_) hinv
    simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)
  have hc := call_pre R L b (growsliceRound S) grE (growsliceArgs S)
    (s := s) (S := S) (lo := sp - K) (hi := sp + 1040) (stack := 4096) (nargs := 5) (fr := 928)
    (by rw [eg]; exact hg1) (by rw [eg]; exact hg2) (by rw [eg, esp]; omega) (by rw [eg]; exact hgo) hFw
    (h28.trans hs28.symm) (by rw [tsp, esp]) (by rw [tsp]; omega) (by rw [h30]; decide) (by rw [h30]; decide)
    (by decide) (by rw [tsp]; omega) (by rw [tsp]; omega) (by rw [tsp]; omega) (by omega)
    (by rw [show sp + 1040 - (sp - K) = K + 1040 by omega]; exact hacc) hwrt hLs
    (by simp only [growsliceArgs, t0, t1, t2, t3, t4]; rw [← grE_eq]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega))
    (by rw [h28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hinvS)
    (by simp only [growsliceRound, t1, t2]; exact hcost)
  refine Reaches.call_regions ((hgr L b).withExit hret) hpc
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
  have hround : growsliceRound S = 8 * growCap8 (len0 + StackNat.rnd (23 * n)) cap0 := by
    simp only [growsliceRound, t1, t2]
  simp only [growsliceObj, Fresh, t1, t2, t3] at hobj
  rw [hround] at hapL hinv1
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, -, -⟩ := hobj
  have hgcl := le_growCap8 (len0 + StackNat.rnd (23 * n)) cap0
  have hgcb := growCap_lt len0 (23 * n) cap0 hk (by omega)
  have egc : growCap8 (len0 + StackNat.rnd (23 * n)) cap0 = growCap8 (len0 + StackNat.rnd (23 * n)) cap0 := rfl
  have hpw := hpin.apart hout
  unfold Apart at hpw
  simp only [calleeStack, tsp, hmem] at hMF hLF hrg hinv1
  have hrd : ∀ a, sp + 48 ≤ a → a + 8 ≤ sp + 1040 → m1.readLE a 8 = M1.readLE a 8 := by
    intro a ha1 ha2
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have q328 := (hrd _ (by omega) (by omega)).trans r328
  have q192 := (hrd _ (by omega) (by omega)).trans r192
  have q216 := (hrd _ (by omega) (by omega)).trans r216
  have q320 := (hrd _ (by omega) (by omega)).trans r320
  have hp64 : ptr.toNat < 2 ^ 64 := ptr.isLt
  have esub : BitVec.ofNat 64 cap0 + BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) -
      BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) = BitVec.ofNat 64 cap0 := BitVec.add_sub_cancel _ _
  have hl3 := lsl3_ofNat (len0 + StackNat.rnd (23 * n) - cap0) (by omega)
  have hl3c := lsl3_ofNat cap0 (by omega)
  have h30' : S.regs 30 = 1798764#64 := h30
  generalize e18 : S.regs 18 = x18 at K'
  generalize e29 : S.regs 29 = x29 at K'
  janus_run [q328, q192, q216, q320, h30', h1, esub, hl3, hl3c, tsp] until [mcE]
  have hst2 : MemFrame m1 ((m1.writeLE (sp + 416) 8 ptr.toNat).writeLE (sp + 200) 8 (growCap8 (len0 + StackNat.rnd (23 * n)) cap0))
      [(sp + 200, sp + 208), (sp + 416, sp + 424)] := by janus_frame
  have hF1 : MemFrame s.mem ((m1.writeLE (sp + 416) 8 ptr.toNat).writeLE (sp + 200) 8 (growCap8 (len0 + StackNat.rnd (23 * n)) cap0))
      (R.rt ++ [(sp - K, sp + 1040)]) := by
    refine MemFrame.trans (rs'' := R.rt ++ [(sp - K, sp + 1040)]) (MemFrame.trans (rs'' := R.rt ++ [(sp - K, sp + 1040)])
      (hmem ▸ hFw : MemFrame s.mem M1 _) hMF fun a k ho => ?_) hst2 fun a k ho => ?_
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, ho.2⟩, ho.1, by omega, by omega⟩
    · refine ⟨ho, ?_⟩
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hk2 : ∀ a, sp + 424 ≤ a → a + 8 ≤ sp + 1040 →
      ((m1.writeLE (sp + 416) 8 ptr.toNat).writeLE (sp + 200) 8 (growCap8 (len0 + StackNat.rnd (23 * n)) cap0)).readLE a 8 = M1.readLE a 8 := fun a h1 h2 => by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hrd a (by omega) h2
  have hinv2 := RtInv.inv_frame hst2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)) hinv1
  rw [h28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hinv2
  refine enG3 impl R hmc ret0 hret Q b L g sp K st xp xl xc ylen mp n len0 cap0 ptr.toNat (growCap8 (len0 + StackNat.rnd (23 * n)) cap0) s he hk (by omega)
    hgcb hn (by omega) hpin hp48 (hal8 (Or.inr (by omega))) _ ((m1.writeLE (sp + 416) 8 ptr.toNat).writeLE (sp + 200) 8 (growCap8 (len0 + StackNat.rnd (23 * n)) cap0)) ?_ ?_ ?_ ?_ ?_ ?_ rfl hF1
    (by simp only [Memory.accessible_writeLE]; exact hpacc) hinv2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left 6
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), q192]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), q328]
  · rw [hk2 _ (by omega) (by omega)]; exact r960
  · rw [hk2 _ (by omega) (by omega)]; exact r968
  · rw [hk2 _ (by omega) (by omega)]; exact r976
  · rw [hk2 _ (by omega) (by omega)]; exact r984
  · rw [hk2 _ (by omega) (by omega)]; exact r1000
  · rw [hk2 _ (by omega) (by omega)]; exact r1016
  · rw [hk2 _ (by omega) (by omega)]; exact r1024
  · intro S' M' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 hMF' hLF' hrg' hinv'
    have hLw2 : LiveSep L [(sp + 200, sp + 208), (sp + 416, sp + 424)] := fun r hr => by
      have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    have hdsep : LiveSep L [(ptr.toNat + 8 * cap0, ptr.toNat + 8 * (len0 + StackNat.rnd (23 * n)))] := fun r hr => by
      have := hapL r hr; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    refine K' S' M' ptr.toNat (growCap8 (len0 + StackNat.rnd (23 * n)) cap0) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
      ?_ a15 ?_ a17 rfl hpin hapL (hal8 (Or.inr (by omega))) hp48 ?_ ?_ ?_ ?_ hinv'
    · exact a14.trans (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact e18)
    · exact a16.trans (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact e29)
    · rw [hMF'.accessible]; simp only [Memory.accessible_writeLE]; exact hpacc
    · refine MemFrame.trans (rs'' := R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 424)])
        (MemFrame.trans (rs'' := R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 424)]) hMF hst2 fun a k ho => ?_)
        hMF' fun a k ho => ?_
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨⟨ho.1, by omega, by omega⟩, by omega, by omega⟩
      · refine ⟨ho, ?_⟩
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
    · exact (hLF.trans (LiveFrame.of_win hst2 hLw2) fun a n h => h).trans
        (LiveFrame.of_sep hLF' hdsep fun r hr => List.mem_append_left _ hr) fun a n h => h
    · rw [hrg', Memory.regions_writeLE, Memory.regions_writeLE]; exact hrg
  all_goals first | (janus_simp; done) | skip
  all_goals (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.W4En
