import FvModexp.Proofs.Arm64.Nat.DivLargeCall

/-!
# `divLarge` (arm64): the copy path's memory facts at the alias test (pure)

From `joinU` (memory `M0`): `SP - 120 := 0` (`M1`), `memmove(t, vIn, 8n)` (`m3`), optionally `memmove(P, uIn, 8 il)`
(`m4`; `m4 = m3` when `P = uIn`), `u[il] := 0` → `MemU`, `UArr`, values (`shift = 0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

namespace FvModexp.Arm64.DivLarge

/-- the callee window of a runtime call from the frame -/
@[reducible] def csW (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 304 - 4096, s.sp.toNat - 304 - 8), (s.sp.toNat - 304 + 8, s.sp.toNat - 304 + 8 + 8 * 3)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem cp_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (hclz : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0)
    {m3 m4 : Memory}
    (hMF1 : MemFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 (R.rt ++ csW s ++ [(t, t + 8 * vl)]))
    (hLF1 : LiveFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 Lk [(t, t + 8 * vl)])
    (hcp1 : Mem.Copied (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 t vp (8 * vl))
    (hMF2 : MemFrame m3 m4 (R.rt ++ csW s ++ [(P, P + 8 * il)]))
    (hLF2 : LiveFrame m3 m4 Lk [(P, P + 8 * il)])
    (hinv4 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m4))
    (hval : natVal m4 P il = natVal s.mem ip il) :
    MemU R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk P C 0 (m4.writeLE (P + 8 * il) 8 0) ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C (m4.writeLE (P + 8 * il) 8 0) ∧
      natVal (m4.writeLE (P + 8 * il) 8 0) t vl = natVal s.mem vp vl * 2 ^ 0 ∧
      2 ^ 63 ≤ (m4.writeLE (P + 8 * il) 8 0).readLE (t + 8 * (vl - 1)) 8 ∧
      natVal (m4.writeLE (P + 8 * il) 8 0) P (il + 1) = natVal s.mem ip il * 2 ^ 0 := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvil := hl.vil; have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hpw := hU.pw; have hp48 := hU.p48
  have hpt := hU.pt; have hpv := hU.pv
  unfold Apart at hpt hpv
  have htw := hl.tw; have hvw := hl.vw; have htv := hl.tv
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hW1 : MemFrame S.mem (S.mem.writeLE (s.sp.toNat - 120) 8 0) [(s.sp.toNat - 120, s.sp.toNat - 112)] := by
    janus_frame
  have hW2 : MemFrame m4 (m4.writeLE (P + 8 * il) 8 0) [(P + 8 * il, P + 8 * il + 8)] := by janus_frame
  have hF : MemFrame S.mem (m4.writeLE (P + 8 * il) 8 0) (R.rt ++ scrA s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := by
    refine (mfTrans (mfTrans (mfTrans hW1 hMF1) hMF2) hW2).mono fun a n ho => ?_
    have ho' := ho
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho'
    obtain ⟨⟨⟨hrt, hsc⟩, hws⟩, hP⟩ := ho'
    have ht := (wsL_parts hws).1
    simp only [csW, outside_append, outside_cons, outside_nil, and_true]
    repeat' apply And.intro
    all_goals first | exact hrt | omega
  have hLF : LiveFrame S.mem (m4.writeLE (P + 8 * il) 8 0) L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := by
    refine ⟨fun a n hin ho => ?_⟩
    have hin' : InRanges a n Lk := hS.ext2.inRanges_old (hE.ext.inRanges_old hin)
    have hw0 : a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r (hE.ext.mem_old hr); omega
    rw [outside_append] at ho
    have ht := (wsL_parts ho.1).1
    have hP : a + n ≤ P ∨ P + 8 * C ≤ a := by simpa only [outside_cons, outside_nil, and_true] using ho.2
    rw [hW2.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF2.readLE a n hin' (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF1.readLE a n hin' (by simp only [outside_cons, outside_nil, and_true]; omega),
      hW1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hinv5 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk (m4.writeLE (P + 8 * il) 8 0)) :=
    inv_store_held hinv4 (hU.pheld.sub (by omega) (by omega))
  have hacc : ∀ a n w, (m4.writeLE (P + 8 * il) 8 0).accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hW2.accessible, hMF2.accessible, hMF1.accessible, hW1.accessible]
  have hM := hS.mem
  have rdF : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat - 96 → Outside a 8 (scrA s) →
      (m4.writeLE (P + 8 * il) 8 0).readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 h3 =>
    hF.readLE _ _ (out4 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega))
  -- `t`'s words: `m4` = `m3` there, = `vIn` in `M1`
  have hth : Held R Lk t (8 * vl) := hS.ext2.held hl.theld
  have hT4 : natVal (m4.writeLE (P + 8 * il) 8 0) t vl = natVal m3 t vl := by
    unfold natVal
    rw [hW2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rcases hth with hi | ho
    · exact hLF2.readLE _ _ hi (by simp only [outside_cons, outside_nil, and_true]; omega)
    · exact hMF2.readLE _ _ (by
        simp only [csW, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨ho, by omega, by omega⟩, by omega⟩)
  have hV : natVal m3 t vl = natVal s.mem vp vl := by
    unfold natVal
    rw [FvModexp.Asm.readLE_of_copied hcp1, hW1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hM.vs _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hval' : natVal (m4.writeLE (P + 8 * il) 8 0) t vl = natVal s.mem vp vl * 2 ^ 0 := by
    rw [hT4, hV, Nat.pow_zero, Nat.mul_one]
  refine ⟨⟨Mem.frame hE hM hU hF hLF hinv5, (rdF _ (by omega) (by omega) (by
      simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans hS.sC,
    (rdF _ (by omega) (by omega) (by simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans hS.sL,
    (rdF _ (by omega) (by omega) (by simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans hS.sP, ?_, ?_⟩,
    UArr.frame hU hacc, hval', ?_, ?_⟩
  · -- the `shift` slot
    rw [hW2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hMF2.readLE _ _ (by
        simp only [csW, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩),
      hMF1.readLE _ _ (by
        simp only [csW, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩),
      Memory.readLE_writeLE_self]
  · have hga := hE.pre.ce.2.2.2.2.1; have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.1
    have hpg := hU.pg
    unfold Apart at hga hpg
    rw [hF.readLE _ _ (out4 hgr (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) (g_wsL hE) (by omega))]
    exact Mem.grd hE hM
  · rw [top_of_natVal _ _ _ (by omega), hval', Nat.pow_zero, Nat.mul_one, ← top_of_natVal _ _ _ (by omega)]
    have hn : s.mem.readLE (vp + 8 * (vl - 1)) 8 ≠ 0 := by
      rcases hE.pre.vn with h | h
      · omega
      · exact h
    have := (AsmDiv.clz_norm64 _ hn (Memory.readLE_lt _ _ _)).2.1
    rw [hclz, Nat.pow_zero, Nat.mul_one] at this; exact this
  · rw [natVal_store_top _ _ _ _ (by decide), hval]; simp

end FvModexp.Arm64.DivLarge
