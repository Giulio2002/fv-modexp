import FvModexp.Proofs.Arm64.NatQ.MulIPre

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/MulIRet.lean — TIGHT COSTS, divmc s34] `(*Int).mul` (arm64): the state `IR` at the return `0x1b0d00` of the inner `nat.mul` call (int.go:201)

`ir_of`: the inner call's `MPost` (one frame down: `S1.sp = SP - 96`, window `W - 96`, `above = 88`) lifted to the
caller's entry state `s` (result pointer taken mod `2^64`, as the register holds it; `kind`'s fresh case is stated for a
non-empty array only) (window `W`, `above = 40`): value, live set, budget, kind, `Exact`, `StackBackL` and frames
relative to `s`, plus the caller's spills (`z`, `x`, `y` at `104/120/128(SP')`), saved `FP`/`LR`, and the operands'
sign bytes (kept: the headers are held, outside the window and apart from `z.abs` and the stack's writes).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

/-- the facts at `0x1b0d00` (see the module doc); `p', l', c'` the inner result, `L1`/`b1` its live set / budget -/
structure IR (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W z st x y : Nat) (s : State)
    (p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State) : Prop where
  pre : IPre R b H L W z st x y s
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  sp : S.sp = s.sp - 96#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 104#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 p'
  p64 : p' < 2 ^ 64
  r1 : S.regs 1 = BitVec.ofNat 64 l'
  r2 : S.regs 2 = BitVec.ofNat 64 c'
  fp : S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat
  lr : S.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat
  zs : S.mem.readLE (s.sp.toNat + 8) 8 = z
  xs : S.mem.readLE (s.sp.toNat + 24) 8 = x
  ys : S.mem.readLE (s.sp.toNat + 32) 8 = y
  nx : S.mem.readLE x 1 = hNeg s.mem x
  ny : S.mem.readLE y 1 = hNeg s.mem y
  val : natVal S.mem p' l' = natVal s.mem (hP s.mem x) (hL s.mem x) * natVal s.mem (hP s.mem y) (hL s.mem y)
  norm : NatNorm S.mem p' l'
  lc : l' ≤ c'
  lxy : l' ≤ hL s.mem x + hL s.mem y
  c40 : c' < 2 ^ 40
  ext : LiveExt R L L1
  bud : b - (mulCQ (hL s.mem x) (hL s.mem y) + stkR H s.mem st) + stkR H S.mem st ≤ b1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S.mem)
  live : NatLive S.mem R L1 p' c'
  kind : (p' = hP s.mem z ∧ c' = hC s.mem z) ∨
    (0 < c' → hL s.mem x + hL s.mem y ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)
  fa : ¬ (p' = hP s.mem z ∧ c' = hC s.mem z) → 0 < c' → 0 < stCap S.mem st →
    Apart p' (8 * c') (stW S.mem st) (8 * stCap S.mem st)
  ex : Exact R L (winA s W 40) (hL s.mem x + hL s.mem y) (hP s.mem z) (hC s.mem z) st (hP s.mem x) (hC s.mem x)
    (hP s.mem y) (hC s.mem y) (natVal s.mem (hP s.mem x) (hL s.mem x) * natVal s.mem (hP s.mem y) (hL s.mem y)) p' c'
    s.mem S.mem
  sb : StackBackL R L L1 st s.mem S.mem
  mf : MemFrame s.mem S.mem (R.rt ++ winA s W 40 ++ [(hP s.mem z, hP s.mem z + 8 * hC s.mem z)] ++ stkWs s.mem st)
  lf : LiveFrame s.mem S.mem L ([(hP s.mem z, hP s.mem z + 8 * hC s.mem z)] ++ stkWs s.mem st)

/-- the callee's window (one frame down) lies in the caller's -/
theorem win96 {s S1 : State} {W : Nat} (hsp1 : S1.sp.toNat = s.sp.toNat - 96) (hW : 96 ≤ W) (hb' : W ≤ s.sp.toNat) :
    ∀ a n, Outside a n (winA s W 40) → Outside a n (winA S1 (W - 96) 88) := by
  intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp1]; omega

/-- the caller's slots miss the inner call's frame -/
theorem slot96 {rt : List (Nat × Nat)} {s S1 : State} {W zp zn st fp fe a n : Nat}
    (hsp1 : S1.sp.toNat = s.sp.toNat - 96) (hW : 104 ≤ W) (hb' : W ≤ s.sp.toNat)
    (hout : Outside (s.sp.toNat - W) (W + 40) rt) (hz : Outside zp zn (win s W 40)) (hst : Outside st 24 (win s W 40))
    (hfr : fe ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ fp)
    (ha : (s.sp.toNat - 104 ≤ a ∧ a + n ≤ s.sp.toNat - 88) ∨ (s.sp.toNat - 8 ≤ a ∧ a + n ≤ s.sp.toNat + 40)) :
    Outside a n (rt ++ winA S1 (W - 96) 88 ++ [(zp, zp + zn)] ++ [(st, st + 24), (fp, fe)]) := by
  simp only [win, winA, outside_append, outside_cons, outside_nil, and_true] at hz hst ⊢
  rw [hsp1]
  exact ⟨⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩, by omega, by omega⟩

/-- the stack's free part, as the end points of `stkWs` -/
theorem free_out {m : Memory} {st lo hi : Nat} (hlc : stLen m st ≤ stCap m st)
    (h : BasicSqr.freeP m st + BasicSqr.freeN m st ≤ lo ∨ hi ≤ BasicSqr.freeP m st) :
    stW m st + 8 * stCap m st ≤ lo ∨ hi ≤ stW m st + 8 * stLen m st := by
  simp only [BasicSqr.freeP, BasicSqr.freeN] at h; omega

/-- a sign byte misses `z.abs` and the stack's writes -/
theorem byte_out {a zp zc st fp fe : Nat} (hz : 0 < zc → Apart zp (8 * zc) a 32) (hst : Apart a 32 st 24)
    (hfr : a + 32 ≤ fp ∨ fe ≤ a) : Outside a 1 ([(zp, zp + 8 * zc)] ++ [(st, st + 24), (fp, fe)]) := by
  simp only [List.singleton_append, outside_cons, outside_nil, and_true]
  unfold Apart at hst
  rcases Nat.eq_zero_or_pos zc with h0 | h0
  · subst h0; omega
  · have := hz h0; unfold Apart at this; omega

theorem slots96 {x : Nat} (h : 104 ≤ x) : (x - 104 ≤ x - 104 ∧ x - 104 + 8 ≤ x - 88) ∧
    (x - 104 ≤ x - 96 ∧ x - 96 + 8 ≤ x - 88) ∧ (x - 8 ≤ x + 8 ∧ x + 8 + 8 ≤ x + 40) ∧
    (x - 8 ≤ x + 24 ∧ x + 24 + 8 ≤ x + 40) ∧ (x - 8 ≤ x + 32 ∧ x + 32 + 8 ≤ x + 40) := by omega

theorem le_add_c {a k c : Nat} (h : k ≤ c) : a + k ≤ a + c := Nat.add_le_add_left h a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`IR` from the inner call's `MPost`** (see the module doc) -/
theorem ir_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s S1 S : State}
    (hpre : IPre R b H L W z st x y s) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hsp1 : S1.sp.toNat = s.sp.toNat - 96) (hg1 : S1.regs 28 = s.regs 28) (hF1 : MemFrame s.mem S1.mem (winA s W 40))
    (q104 : S1.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat)
    (q96 : S1.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat)
    (q8 : S1.mem.readLE (s.sp.toNat + 8) 8 = z) (q24 : S1.mem.readLE (s.sp.toNat + 24) 8 = x)
    (q32 : S1.mem.readLE (s.sp.toNat + 32) 8 = y)
    (hq : MPost R b H L (W - 96) (hP s.mem z) (hC s.mem z) st (hP s.mem x) (hL s.mem x) (hC s.mem x) (hP s.mem y)
      (hL s.mem y) (hC s.mem y) S1 S)
    (hsp : S.sp = s.sp - 96#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 104#64)
    (h18 : S.regs 18 = s.regs 18) :
    ∃ (p' l' c' b1 : Nat) (L1 : List (Nat × Nat)), IR R b H L W z st x y s p' l' c' b1 L1 S := by
  have hpre' := hpre
  obtain ⟨hce, hiw, -, -, -, -, ⟨-, -, -, hxw, hxH, hxst, hxfr⟩, ⟨-, -, -, hyw, hyH, hyst, hyfr⟩, -, -, -, -, -, -, -,
    -, -, -, hzarr, ⟨⟨-, -, -, -, -, hxaw⟩, ⟨-, -, -, -, -, hyaw⟩, ⟨-, -, hzw, -, -, -⟩, -⟩, hstk, -, -⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  obtain ⟨-, hsok, hstw, -, -, -, hfw, -⟩ := hstk
  have hW4 : 4704 ≤ W := Nat.le_trans (Nat.add_le_add_right (mulW_ge (hL s.mem x) (hL s.mem y)) 96) hiw
  have hW : 96 ≤ W := Nat.le_trans (by decide) hW4
  obtain ⟨k1, k2, k3, k4, k5⟩ := slots96 (Nat.le_trans (Nat.le_trans (by decide) hW4) hb')
  have hsubA := win96 hsp1 hW hb'
  have hstA := winA_of_win' hstw
  obtain ⟨eW, eL, eC⟩ := hdr_frame hF1 hstA
  have hxS : natVal S1.mem (hP s.mem x) (hL s.mem x) = natVal s.mem (hP s.mem x) (hL s.mem x) := by
    rcases Nat.eq_zero_or_pos (hL s.mem x) with h0 | h0
    · rw [h0]; simp
    · exact natVal_frame hF1 (winA_of_win' (hxaw h0).1)
  have hyS : natVal S1.mem (hP s.mem y) (hL s.mem y) = natVal s.mem (hP s.mem y) (hL s.mem y) := by
    rcases Nat.eq_zero_or_pos (hL s.mem y) with h0 | h0
    · rw [h0]; simp
    · exact natVal_frame hF1 (winA_of_win' (hyaw h0).1)
  obtain ⟨p', l', c', q0, q1, q2, hv, hn, hlc, hll, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex, hsb,
    hMF, hLF⟩ := hq
  have hwS : stkWs S1.mem st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  rw [hwS] at hMF hLF
  rw [hxS, hyS] at hv hex
  rw [stkR_congr eC] at hbud
  have hfw' : stW s.mem st + 8 * stCap s.mem st ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ stW s.mem st + 8 * stLen s.mem st :=
    free_out hsok.2.2.2.2.2.1 (by simpa only [win, outside_cons, outside_nil, and_true] using hfw)
  have hLs' : LiveSep L (win s W 40) := hLs
  have hFL : MemFrame s.mem S.mem (R.rt ++ winA s W 40 ++ [(hP s.mem z, hP s.mem z + 8 * hC s.mem z)] ++
      stkWs s.mem st) :=
    MemFrame.trans hF1 hMF fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨⟨h.1.1.1, hsubA _ _ h.1.1.2⟩, h.1.2⟩, h.2⟩
  have hLL : ∀ ws : List (Nat × Nat), LiveFrame S1.mem S.mem L ws → LiveFrame s.mem S.mem L ws := fun ws h =>
    LiveFrame.trans (lf_win' _ hF1 hLs') h fun _ _ h => h
  -- the caller's slots: outside the callee's window, `R.rt`, `z.abs` and the stack's writes
  -- the result pointer as the register holds it
  have hzP : hP s.mem z < 2 ^ 64 := Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide)
  have hPP : c' = 0 ∨ p' % 2 ^ 64 = p' := by
    rcases Nat.eq_zero_or_pos c' with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (hlive h0).2.2.2)
        (by decide)))
  have hzr : p' = hP s.mem z → p' % 2 ^ 64 = p' := fun h => Nat.mod_eq_of_lt (h ▸ hzP)
  have q0' : S.regs 0 = BitVec.ofNat 64 (p' % 2 ^ 64) := by rw [q0]; exact BitVec.eq_of_toNat_eq (by simp)
  have hl0 : c' = 0 → l' = 0 := fun h => Nat.eq_zero_of_le_zero (h ▸ hlc)
  have hv' : natVal S.mem (p' % 2 ^ 64) l' = natVal s.mem (hP s.mem x) (hL s.mem x) * natVal s.mem (hP s.mem y) (hL s.mem y) := by
    rcases hPP with h0 | e
    · have := hl0 h0; subst this; exact hv
    · rw [e]; exact hv
  have hn' : NatNorm S.mem (p' % 2 ^ 64) l' := by
    rcases hPP with h0 | e
    · exact Or.inl (hl0 h0)
    · rw [e]; exact hn
  have hlive' : NatLive S.mem R L' (p' % 2 ^ 64) c' := by
    rcases hPP with h0 | e
    · intro h; exact absurd (h0 ▸ h) (Nat.lt_irrefl 0)
    · rw [e]; exact hlive
  have hkind' : (p' % 2 ^ 64 = hP s.mem z ∧ c' = hC s.mem z) ∨
      (0 < c' → hL s.mem x + hL s.mem y ≤ c' ∧ InRanges (p' % 2 ^ 64) (8 * c') R.rt ∧ ApartAll (p' % 2 ^ 64) (8 * c') L) := by
    rcases hkind with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨by rw [hzr h1]; exact h1, h2⟩
    · refine Or.inr fun hc => ?_
      rcases hPP with h0 | e
      · exact absurd (h0 ▸ hc) (Nat.lt_irrefl 0)
      · rw [e]; exact h
  have hfa' : ¬ (p' % 2 ^ 64 = hP s.mem z ∧ c' = hC s.mem z) → 0 < c' → 0 < stCap S.mem st →
      Apart (p' % 2 ^ 64) (8 * c') (stW S.mem st) (8 * stCap S.mem st) := by
    intro h1 hc
    rcases hPP with h0 | e
    · exact absurd (h0 ▸ hc) (Nat.lt_irrefl 0)
    · rw [e] at h1 ⊢; exact hfa h1 hc
  have hp64 : p' % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hkeep : ∀ a n, (s.sp.toNat - 104 ≤ a ∧ a + n ≤ s.sp.toNat - 88) ∨
      (s.sp.toNat - 8 ≤ a ∧ a + n ≤ s.sp.toNat + 40) → S.mem.readLE a n = S1.mem.readLE a n := fun a n h =>
    hMF.readLE _ _ (slot96 hsp1 (Nat.le_trans (by decide) hW4) hb' hout hzw hstw hfw' h)
  have hneg : ∀ a, Outside a 32 (win s W 40) → Held R L a 32 → Apart a 32 st 24 →
      Apart a 32 (BasicSqr.freeP s.mem st) (BasicSqr.freeN s.mem st) →
      (0 < hC s.mem z → Apart (hP s.mem z) (8 * hC s.mem z) a 32) → S.mem.readLE a 1 = s.mem.readLE a 1 := by
    intro a hw' hH hst hfr hza
    have h1 : S1.mem.readLE a 1 = s.mem.readLE a 1 :=
      hF1.readLE _ _ ((winA_of_win' hw').of_sub (Nat.le_refl _) (le_add_c (by decide)))
    rw [← h1]
    exact Held.readLE2 (ws1 := winA S1 (W - 96) 88) (hH.sub (Nat.le_refl _) (le_add_c (by decide)))
      (by simpa only [List.append_assoc] using hMF) hLF
      (hsubA _ _ ((winA_of_win' hw').of_sub (Nat.le_refl _) (le_add_c (by decide))))
      (byte_out hza hst (free_out (lo := a) (hi := a + 32) hsok.2.2.2.2.2.1 (by unfold Apart at hfr; exact hfr.symm)).symm)
  refine ⟨p' % 2 ^ 64, l', c', b', L', IR.mk (hpre) (hl4) (hl48) (hsp) (h28) (h29) (h18) (q0') (hp64) (q1) (q2) ((hkeep _ _ (Or.inl k1)).trans q104) ((hkeep _ _ (Or.inl k2)).trans q96) ((hkeep _ _ (Or.inr k3)).trans q8) ((hkeep _ _ (Or.inr k4)).trans q24) ((hkeep _ _ (Or.inr k5)).trans q32) (hneg x hxw hxH hxst hxfr (fun h => (hzarr h).1)) (hneg y hyw hyH hyst hyfr (fun h => (hzarr h).2.1)) (hv') (hn') (hlc) (hll) (hc40) (hext) (hbud) (by rw [← hg1]; exact hinv) (hlive') (hkind') (hfa') (?_) (?_) (hFL) (hLL _ hLF)⟩
  · intro h1 h2 h3
    obtain ⟨e1, e2, hvz, hF', hLF'⟩ := hex h1 h2 h3
    rw [hwS] at hF' hLF'
    rw [hzr e1]
    have hzN : Outside (hP s.mem z) (8 * (hL s.mem x + hL s.mem y)) (winA s W 40) :=
      (winA_of_win' hzw).of_sub (Nat.le_refl _) (le_add_c (Nat.mul_le_mul_left 8 h1))
    refine ⟨e1, e2, ?_, MemFrame.trans hF1 hF' fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨⟨h.1.1.1, hsubA _ _ h.1.1.2⟩, h.1.2⟩, h.2⟩, hLL _ hLF'⟩
    rcases hvz with h | ⟨h0, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, by rw [h, natVal_frame hF1 hzN]⟩
  · obtain ⟨⟨sbok, sblen, sbor⟩, sbm⟩ := hsb
    refine ⟨⟨sbok, by rw [sblen, eL], ?_⟩, ?_⟩
    · rcases sbor with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by rw [h1, eW], by rw [h2, eC]⟩
      · exact Or.inr h
    · unfold ArrIn; intro hn'; apply sbm; rw [eW, eC]; exact hn'

end FvModexp.Arm64.Q.NatMul
