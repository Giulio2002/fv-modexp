import FvModexp.Proofs.Amd64.Exp.W4Mid

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the facts `zjRet` needs, bundled, and their transport along `z.make`/`zz.make`
(agent expmc s48)

`Pre4` = everything `W4Mid.zjRet` takes about the memory and the live set except the two buffers. `Pre4.frame`
moves it along a frame that writes only `R.rt` and low frame words (`[sp-4296, sp+0xd8)`, `[sp+0x168, sp+0x170)`)
with the live set extended by fresh `R.rt` ranges (the `ZPost`s of `W4Zm`/`W4Zm2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv)

/-- the memory facts of `zjRet` besides the buffers -/
@[reducible] def Pre4 (R : RtInv) (L : List (Nat × Nat)) (sp n mp mc k0 yp ylen Y yi Mv : Nat) (pp tbl : Nat → Nat)
    (onep st n0 bp r : Nat) (M : Memory) : Prop :=
  Extracted.program.DataLoaded M ∧ Inp R L sp n M mp ∧ Inp R L sp ylen M yp ∧ M.readLE yp (8 * ylen) = Y ∧
  M.readLE (yp + 8 * (ylen - 1)) 8 = yi ∧
  (∀ d, d < 16 → Ent sp n pp (fun _ => 2 * n) tbl M d) ∧ (∀ d, d < 16 → Inp R L sp n M (pp d)) ∧
  M.readLE (sp + 0x398) 8 = ylen ∧ M.readLE (sp + 0x390) 8 = yp ∧ M.readLE (sp + 0x3a8) 8 = mp ∧
  M.readLE (sp + 0xd8) 8 = k0 ∧ M.readLE (sp + 0x3b0) 8 = n ∧ M.readLE (sp + 0x3b8) 8 = mc ∧
  NatNorm M mp n ∧ M.readLE mp (8 * n) = Mv ∧
  OneIn R L sp n M onep ∧ M.readLE onep (8 * n) = 1 ∧ M.readLE (sp + 0x328) 8 = onep ∧
  FinEnv sp st n0 bp r M ∧ (InRanges st 24 L ∨ Outside st 24 R.rt)

/-- the frame words the two `make`s may write -/
@[reducible] def LowW (sp : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ q ∈ ws, (sp - 4296 ≤ q.1 ∧ q.2 ≤ sp + 0xd8) ∨ (sp + 0x168 ≤ q.1 ∧ q.2 ≤ sp + 0x170)

theorem out_low {a k sp : Nat} (h : Apart a k (sp - 4296) (4296 + 0x3c0)) (hs : 4296 ≤ sp) :
    ∀ ws, LowW sp ws → Outside a k ws
  | [], _ => trivial
  | q :: ws, hq => by
    have h1 := hq q (by simp)
    refine ⟨by unfold Apart at h; omega, out_low h hs ws (fun q' hq' => hq q' (by simp [hq']))⟩

theorem out_slot {a k sp : Nat} (h1 : sp + 0xd8 ≤ a) (h2 : a + k ≤ sp + 0x168 ∨ sp + 0x170 ≤ a) :
    ∀ ws, LowW sp ws → Outside a k ws
  | [], _ => trivial
  | q :: ws, hq => by
    have h3 := hq q (by simp)
    refine ⟨by omega, out_slot h1 h2 ws (fun q' hq' => hq q' (by simp [hq']))⟩

set_option maxRecDepth 20000 in
theorem Pre4.frame {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y yi Mv : Nat}
    {pp tbl : Nat → Nat} {onep st n0 bp r : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Pre4 R L sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M) (he : Env R L g fs sp M)
    (hF : MemFrame M M' (R.rt ++ ws)) (hL : LiveFrame M M' L []) (hx : LiveExt R L L')
    (hrg : M'.regions = M.regions) (hro : RoOut R)
    (hwa : ∀ q ∈ ws, q.1 < q.2 → M.accessible q.1 (q.2 - q.1) true = true) (hlw : LowW sp ws)
    (hn : 0 < n) (hyl : 0 < ylen) :
    Pre4 R L' sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M' := by
  obtain ⟨hd, hm, hy, hY, hyi, hent, hbuf, s1, s2, s3, s4, s5, s6, hnm, hmv, hone, hone1, r328, hfe, hsth⟩ := h
  have hs1 : 4296 ≤ sp := he.2.1
  have hs2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt := he.2.2.2.2.2.2.2.1
  have hF0 : MemFrame M M' (R.rt ++ ws ++ []) := by rw [List.append_nil]; exact hF
  have rdh : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Outside a k ws → M'.readLE a k = M.readLE a k :=
    fun a k hh ho => FvModexp.Expmc.held_readLE hh hF0 hL ho trivial
  have rdi : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x3c0) →
      M'.readLE a k = M.readLE a k := fun a k hh ha => rdh a k hh (out_low ha hs1 ws hlw)
  have rds : ∀ K, 0xd8 ≤ K → K + 8 ≤ 0x3c0 → (K + 8 ≤ 0x168 ∨ 0x170 ≤ K) →
      M'.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K k1 k2 k3 =>
    rdh _ _ (Or.inr (hwrt.of_sub (by omega) (by omega))) (out_slot (by omega) (by omega) ws hlw)
  have inp : ∀ k p, Inp R L sp k M p → Inp R L' sp k M' p := fun k p hp =>
    ⟨by rw [hF.accessible]; exact hp.1, hp.2.1, hx.held hp.2.2.1, hp.2.2.2⟩
  refine ⟨FvModexp.dataLoaded_frame64 hd hrg hro hF hwa, inp _ _ hm, inp _ _ hy,
    by rw [rdi _ _ hy.2.2.1 hy.2.2.2]; exact hY, ?_, fun d hd => ?_, fun d hd => inp _ _ (hbuf d hd),
    by rw [rds 0x398 (by omega) (by omega) (by omega)]; exact s1, by rw [rds 0x390 (by omega) (by omega) (by omega)]; exact s2,
    by rw [rds 0x3a8 (by omega) (by omega) (by omega)]; exact s3, by rw [rds 0xd8 (by omega) (by omega) (by omega)]; exact s4,
    by rw [rds 0x3b0 (by omega) (by omega) (by omega)]; exact s5, by rw [rds 0x3b8 (by omega) (by omega) (by omega)]; exact s6,
    ?_, by rw [rdi _ _ hm.2.2.1 hm.2.2.2]; exact hmv, ?_, ?_, by rw [rds 0x328 (by omega) (by omega) (by omega)]; exact r328,
    ?_, hsth.imp (fun h => hx.inRanges_old h) id⟩
  · have hyw := hy.2.2.2
    unfold Apart at hyw
    rw [rdh _ _ (hy.2.2.1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (out_low (by unfold Apart; omega) hs1 ws hlw)]; exact hyi
  · obtain ⟨e1, e2, e3, e4⟩ := hent d hd
    have hbd := hbuf d hd
    refine ⟨by rw [rdi _ _ hbd.2.2.1 hbd.2.2.2]; exact e1, ?_, ?_, ?_⟩
    · rw [show sp + 0x1a8 + 24 * d = sp + (0x1a8 + 24 * d) by omega, rds _ (by omega) (by omega) (by omega),
        ← Nat.add_assoc]; exact e2
    · rw [show sp + 0x1b0 + 24 * d = sp + (0x1b0 + 24 * d) by omega, rds _ (by omega) (by omega) (by omega),
        ← Nat.add_assoc]; exact e3
    · rw [show sp + 0x1b8 + 24 * d = sp + (0x1b8 + 24 * d) by omega, rds _ (by omega) (by omega) (by omega),
        ← Nat.add_assoc]; exact e4
  · rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2
      unfold Apart at hm4
      rw [rdh _ _ (hm.2.2.1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
        (out_low (by unfold Apart; omega) hs1 ws hlw)]; exact h
  · rcases hone with h | h
    · exact Or.inl (inp _ _ h)
    · exact Or.inr h
  · rcases hone with h | ⟨rfl, h4⟩
    · rw [rdi _ _ h.2.2.1 h.2.2.2]; exact hone1
    · rw [rdh _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))]
      · exact hone1
      · exact out_slot (by omega) (Or.inl (by omega)) ws hlw
  · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
    have hstw := f12
    unfold Apart at hstw
    refine ⟨f1, f2, f3, by rw [hF.accessible]; exact f4, by rw [rds 0x378 (by omega) (by omega) (by omega)]; exact f5,
      by rw [rds 0x340 (by omega) (by omega) (by omega)]; exact f6, by rw [rds 0x348 (by omega) (by omega) (by omega)]; exact f7,
      by rw [rds 0x350 (by omega) (by omega) (by omega)]; exact f8, f9, by rw [hF.accessible]; exact f10, ?_, f12,
      by rw [rds 0x380 (by omega) (by omega) (by omega)]; exact f13, by rw [rds 0x388 (by omega) (by omega) (by omega)]; exact f14,
      f15⟩
    rw [rdh _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (out_low (by unfold Apart; omega) hs1 ws hlw)]; exact f11

end FvModexp.Amd64.W4Pro
