import FvModexp.Proofs.Arm64.Exp.W4PowDefs

/-!
# window-4 prologue (arm64): `powers[0]`, `powers[1]` (nat.go:1413-1414) — definitions

From the return of `buf := stk.nat(17·numWords)` (pc `p01`, `+0x5ac`): `k0 = -k0'` stored, `powers[0] =
buf[0:n:2n].montgomery(one, RR, …)`, `powers[1] = buf[n:2n:3n].montgomery(x, RR, …)`, `i = 2`, jump to the table loop head.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the return address of `stk.nat(17·numWords)` -/
abbrev p01 : Nat := 1799964

/-- `one` (nat.go:1407): a held array apart from the window, or (`n ≤ 4`) the frame buffer `[sp + 336, sp + 368)` -/
@[reducible] def OneIn (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  Inp R L sp n M0 p ∨ (p = sp + 336 ∧ n ≤ 4)

/-- the input facts `MontW.MCall` needs of an operand (window `[sp - 4288, sp + 120)` only) -/
@[reducible] def InpC (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧
  Apart p (8 * n) (sp - 4288) (4288 + 120)

theorem Inp.c {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M0 : Memory} (h : Inp R L sp n M0 p) :
    InpC R L sp n M0 p := ⟨h.1, h.2.1, h.2.2.1, by have := h.2.2.2; unfold Apart at this ⊢; omega⟩

theorem OneIn.c {R : RtInv} {L : List (Nat × Nat)} {g sp n p : Nat} {M0 : Memory} (he : Env R L g sp M0)
    (h : OneIn R L sp n M0 p) : InpC R L sp n M0 p := by
  obtain ⟨hal, hsp1, hsp2, hwacc, -, -, -, hwrt, -, -, -⟩ := he
  rcases h with h | ⟨rfl, hn⟩
  · exact Inp.c h
  · exact ⟨M0.accessible_sub hwacc (Or.inr rfl) (by omega) (by omega), by omega,
      Or.inr (hwrt.of_sub (by omega) (by omega)), by unfold Apart; omega⟩

theorem mcall_ofC {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc rp rc xp yp : Nat} {M0 : Memory}
    (he : Env R L g sp M0) (hn : 0 < n) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hr : Buf R L g sp n M0 rp rc)
    (hx : InpC R L sp n M0 xp) (hy : InpC R L sp n M0 yp) (hm : Inp R L sp n M0 mp)
    (hrx : Apart rp (8 * rc) xp (8 * n)) (hry : Apart rp (8 * rc) yp (8 * n)) (hrm : Apart rp (8 * rc) mp (8 * n))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n]) :
    MontW.MCall R L g (M0.readLE (g + 16) 8) sp n mp mc rp rc xp yp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hr
  have sub : ∀ p k, Apart p k (sp - 4288) (4288 + 1040) → Apart p k (sp - 4288) (4288 + 120) := by
    intro p k h; unfold Apart at h; unfold Apart; omega
  refine ⟨h1, h2, by omega, h5, h7,
    h8.of_sub (Nat.le_refl _) (by omega), sub _ _ h9, h10, ?_, hn, r1, r2, hmc, hmc', r4, r5, sub _ _ r6, r7,
    ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, hy.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, hok.1, hok.2⟩
  intro r hr
  have := h11 r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- the frame words `p01 → powHead` writes besides `buf` (callee window, `k0`, `len(buf)`, `3n`, headers 0-1, `&buf`) -/
@[reducible] def qw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4288, sp - 8), (sp + 8, sp + 120), (sp + 224, sp + 232), (sp + 248, sp + 256), (sp + 312, sp + 320),
    (sp + 432, sp + 480), (sp + 824, sp + 832)]

@[reducible] def FQ (R : RtInv) (L : List (Nat × Nat)) (sp bp bc : Nat) (M0 M : Memory) : Prop :=
  MemFrame M0 M (R.rt ++ qw sp ++ [(bp, bp + 8 * bc)]) ∧ LiveFrame M0 M L [(bp, bp + 8 * bc)]

theorem FQ.write {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M : Memory}
    (h : FQ R L sp bp bc M0 M) (hLs : LiveSep L [(sp - 4288, sp + 1040)]) {a k : Nat} (v : Nat)
    (hw : (sp - 4288 ≤ a ∧ a + k ≤ sp - 8) ∨ (sp + 8 ≤ a ∧ a + k ≤ sp + 120) ∨ (sp + 224 ≤ a ∧ a + k ≤ sp + 232) ∨
      (sp + 248 ≤ a ∧ a + k ≤ sp + 256) ∨ (sp + 312 ≤ a ∧ a + k ≤ sp + 320) ∨ (sp + 432 ≤ a ∧ a + k ≤ sp + 480) ∨
      (sp + 824 ≤ a ∧ a + k ≤ sp + 832)) :
    FQ R L sp bp bc M0 (M.writeLE a k v) := by
  refine ⟨h.1.writeLE_inRanges v ?_, h.2.writeLE v (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))⟩
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4288, sp - 8), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 8, sp + 120), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 224, sp + 232), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 248, sp + 256), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 312, sp + 320), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 432, sp + 480), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 824, sp + 832), by simp [qw], h1, h2⟩

theorem FQ.call {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M M' : Memory} {rp rc : Nat}
    (h : FQ R L sp bp bc M0 M)
    (hc : MemFrame M M' (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(rp, rp + 8 * rc)]))
    (hl : LiveFrame M M' L [(rp, rp + 8 * rc)]) (hr : bp ≤ rp ∧ rp + 8 * rc ≤ bp + 8 * bc) :
    FQ R L sp bp bc M0 M' := by
  refine ⟨h.1.trans hc (fun a n ho => ⟨ho, ?_⟩),
    h.2.trans (FvModexp.Expmc.liveFrame_widen hl (fun a n ho => ?_)) (fun _ _ h => h)⟩
  · simp only [qw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega

/-- `Env` survives a frame that keeps the guard word -/
theorem env_frame {R : RtInv} {L : List (Nat × Nat)} {g sp : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Env R L g sp M) (hf : MemFrame M M' (R.rt ++ ws)) (hg : Outside (g + 16) 8 ws) : Env R L g sp M' := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs⟩ := h
  have hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨hgrt, hg⟩)
  exact ⟨hal, hsp1, hsp2, by rw [hf.accessible]; exact hacc, hg1, by rw [hf.accessible]; exact hg2,
    by rw [hgr]; exact hg3, hrt, hga, hgrt, hLs⟩

theorem inp_frame {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Inp R L sp n M p) (hf : MemFrame M M' ws) : Inp R L sp n M' p :=
  ⟨by rw [hf.accessible]; exact h.1, h.2⟩

/-- a frame word above the callee window and outside the result buffer reads through a montgomery call -/
theorem rd_call {R : RtInv} {sp a rp rc : Nat} {M M' : Memory}
    (F : MemFrame M M' (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(rp, rp + 8 * rc)]))
    (hwrt : Outside (sp - 4288) (4288 + 1040) R.rt) (hs : 4288 ≤ sp) (h1 : sp + 120 ≤ a) (h2 : a + 8 ≤ sp + 1040)
    (h3 : a + 8 ≤ rp ∨ rp + 8 * rc ≤ a) : M'.readLE a 8 = M.readLE a 8 := by
  refine F.readLE _ _ ?_
  have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
  simp only [outside_append, outside_cons, outside_nil, and_true, hro, true_and]
  omega

theorem OneIn.disj {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M : Memory} (h : OneIn R L sp n M p) :
    (p = sp + 336 ∧ n ≤ 4) ∨ (p + 8 * n ≤ sp - 4288 ∨ sp + 1040 ≤ p) := by
  rcases h with ⟨-, -, -, h⟩ | h
  · right; unfold Apart at h; omega
  · left; exact h

theorem rd_self8 {m : Memory} {a v : Nat} : (m.writeLE a 8 v).readLE a 8 = v % 18446744073709551616 := by
  rw [Memory.readLE_writeLE_self]

end FvModexp.Arm64.W4Pro
