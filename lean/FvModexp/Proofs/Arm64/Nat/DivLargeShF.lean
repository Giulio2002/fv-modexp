import FvModexp.Proofs.Arm64.Nat.DivLargeCall
import FvModexp.Proofs.Common.SetBytesMath

/-!
# `divLarge` (arm64): the shift path's memory facts at the alias test (pure)

From `joinU` (memory `M0`): `SP - 120 := shift` and the ABI0 arguments (`A1`), `lshVU(v, vIn, shift)` (`m3`), the ABI0
arguments (`A2`), `lshVU(u[:il], uIn, shift)` (`m4`, carry at `SP - 240`), `u[il] := carry` → `MemU`, `UArr`, values.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sh_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    {sh : Nat} (hsh : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh)
    {A1 m3 A2 m4 : Memory}
    (hA1 : MemFrame S.mem A1 [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112)])
    (hA1sh : A1.readLE (s.sp.toNat - 120) 8 = sh)
    (hQ1f : MemFrame A1 m3 [(t, t + 8 * vl), (s.sp.toNat - 240, s.sp.toNat - 232)])
    (hQ1v : natVal m3 t vl = natVal A1 vp vl * 2 ^ sh % 2 ^ (64 * vl))
    (hA2 : MemFrame m3 A2 [(s.sp.toNat - 296, s.sp.toNat - 232)])
    (hQ2f : MemFrame A2 m4 [(P, P + 8 * il), (s.sp.toNat - 240, s.sp.toNat - 232)])
    (hQ2v : natVal m4 P il = natVal A2 ip il * 2 ^ sh % 2 ^ (64 * il))
    (hQ2c : m4.readLE (s.sp.toNat - 240) 8 = natVal A2 ip il * 2 ^ sh / 2 ^ (64 * il))
    (hinv4 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m4)) :
    MemU R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk P C sh
        (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) ∧
      natVal (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) t vl = natVal s.mem vp vl * 2 ^ sh ∧
      2 ^ 63 ≤ (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)).readLE (t + 8 * (vl - 1)) 8 ∧
      natVal (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) P (il + 1) = natVal s.mem ip il * 2 ^ sh := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvil := hl.vil; have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hpw := hU.pw; have hp48 := hU.p48
  have hpt := hU.pt; have hpv := hU.pv
  unfold Apart at hpt hpv
  have htw := hl.tw; have hvw := hl.vw; have htv := hl.tv; have hiw := hl.iw; have hti := hl.ti
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hM := hS.mem
  have hW2 : MemFrame m4 (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) [(P + 8 * il, P + 8 * il + 8)] := by janus_frame
  have hF0 : MemFrame S.mem (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) (scrA s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := by
    refine (mfTrans (mfTrans (mfTrans (mfTrans hA1 hQ1f) hA2) hQ2f) hW2).mono fun a n ho => ?_
    have ho' := ho
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho'
    obtain ⟨⟨hsc, hws⟩, hP⟩ := ho'
    have ht := hws.1
    simp only [outside_append, outside_cons, outside_nil, and_true]
    repeat' apply And.intro
    all_goals omega
  have hF : MemFrame S.mem (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) (R.rt ++ scrA s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) :=
    hF0.mono fun a n ho => by
      simp only [outside_append] at ho ⊢; exact ⟨⟨ho.1.1.2, ho.1.2⟩, ho.2⟩
  have hLF : LiveFrame S.mem (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := by
    refine ⟨fun a n hin ho => hF0.readLE a n ?_⟩
    have hw0 : a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r (hE.ext.mem_old hr); omega
    rw [outside_append] at ho ⊢
    refine ⟨?_, ho.2⟩
    rw [outside_append]
    exact ⟨by simp only [scrA, outside_cons, outside_nil, and_true]; omega, ho.1⟩
  have hinv5 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8))) :=
    inv_store_held hinv4 (hU.pheld.sub (by omega) (by omega))
  have hacc : ∀ a n w, (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)).accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hW2.accessible, hQ2f.accessible, hA2.accessible, hQ1f.accessible, hA1.accessible]
  have rdF : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat - 96 → Outside a 8 (scrA s) →
      (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)).readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 h3 =>
    hF.readLE _ _ (out4 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega))
  -- values
  have hV1 : natVal A1 vp vl = natVal s.mem vp vl := by
    unfold natVal
    rw [hA1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hM.vs _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hI2 : natVal A2 ip il = natVal s.mem ip il := by
    unfold natVal
    rw [hA2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ1f.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hA1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hS.is _ _ (Nat.le_refl _) (Nat.le_refl _)
  -- the scaled divisor
  have hvn : s.mem.readLE (vp + 8 * (vl - 1)) 8 ≠ 0 := by
    rcases hE.pre.vn with h | h
    · omega
    · exact h
  have hsv := natVal_succ s.mem vp (vl - 1)
  rw [show vl - 1 + 1 = vl by omega] at hsv
  have hlo : natVal s.mem vp (vl - 1) < 2 ^ (64 * (vl - 1)) := by
    unfold natVal
    have := Memory.readLE_lt s.mem vp (8 * (vl - 1))
    rw [show (256 : Nat) ^ (8 * (vl - 1)) = 2 ^ (64 * (vl - 1)) by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this
    exact this
  obtain ⟨hsc1, hsc2⟩ := DivLargeMath.scale_v (natVal s.mem vp (vl - 1)) (s.mem.readLE (vp + 8 * (vl - 1)) 8) (vl - 1) hlo hvn
    (Memory.readLE_lt _ _ _)
  rw [← hsv, hsh, show vl - 1 + 1 = vl by omega] at hsc1
  rw [← hsv, hsh] at hsc2
  have hT : natVal (m4.writeLE (P + 8 * il) 8 (m4.readLE (s.sp.toNat - 240) 8)) t vl = natVal s.mem vp vl * 2 ^ sh := by
    unfold natVal
    rw [hW2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ2f.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hA2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    have := hQ1v; unfold natVal at this; rw [this]
    unfold natVal at hV1; rw [hV1, Nat.mod_eq_of_lt hsc1]
  refine ⟨⟨Mem.frame hE hM hU hF hLF hinv5, (rdF _ (by omega) (by omega) (by
      simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans hS.sC,
    (rdF _ (by omega) (by omega) (by simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans hS.sL,
    (rdF _ (by omega) (by omega) (by simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans hS.sP, ?_, ?_⟩,
    UArr.frame hU hacc, hT, ?_, ?_⟩
  · rw [hW2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ2f.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hA2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ1f.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hA1sh
  · have hga := hE.pre.ce.2.2.2.2.1; have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.1
    have hpg := hU.pg
    unfold Apart at hga hpg
    rw [hF.readLE _ _ (out4 hgr (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) (g_wsL hE) (by omega))]
    exact Mem.grd hE hM
  · rw [top_of_natVal _ _ _ (by omega), hT]; exact hsc2
  · rw [natVal_store_top _ _ _ _ (Memory.readLE_lt _ _ _), hQ2v, hQ2c, hI2]
    exact Nat.mod_add_div _ _

end FvModexp.Arm64.DivLarge
