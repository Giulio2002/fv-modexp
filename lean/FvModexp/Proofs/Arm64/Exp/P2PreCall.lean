import FvModexp.Proofs.Arm64.Exp.P2PreBld

/-!
# `buildPrecomputationWindowModPower2` (arm64): call helpers of the main loop (agent infra)

`ra_bp` (return addresses inside the function's segment `seg60`), `bufArr` (an array inside `buf` as a callee operand /
result: `WrOut`, `RdIn`, `CapIn`, stack-apart), arithmetic bounds (`nb_le`, `rnd_le`, `bud_room`), and `ctxAfter`:
the context after a `sqr` / `mul` / `trunc` call whose result array lies in `buf`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

set_option maxRecDepth 20000 in
/-- a return address inside the function's own segment (`seg60`, base `1790928`) is a return address of every callee
program that does not contain it -/
theorem ra_bp {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 300) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (1790928 + 4 * i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg60) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x1b53d0 + 4 * i < 2 ^ 48; omega) (by decide)
  simpa only [Extracted.seg60] using this

theorem nb_le {pl lm : Nat} (hpl : pl ≤ 16) (hw : W lm ≤ 128) : NB pl lm ≤ 2176 := by
  simp only [NB]
  exact Nat.le_trans (Nat.mul_le_mul (Nat.succ_le_succ hpl) hw) (by decide)

theorem rnd_le (n : Nat) : StackNat.rnd n ≤ n + 3 := by simp only [StackNat.rnd]; omega

/-- the budget left in round `i` covers a whole round -/
theorem bud_room {c0 rc pl i b b1 : Nat} (hc : c0 + (pl / 2 - 1) * rc ≤ b) (hi : i + 2 ≤ pl) (h2 : 2 ≤ i)
    (hb : b - (c0 + (i / 2 - 1) * rc) ≤ b1) : rc ≤ b1 := by
  have : (i / 2 - 1) * rc + rc ≤ (pl / 2 - 1) * rc := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem bud_step {b b1 b' S c m : Nat} (hb : b - S ≤ b1) (h1 : b1 - m ≤ b') (h2 : m ≤ c) : b - (S + c) ≤ b' := by
  omega

/-- `powers[j]`'s words lie in `buf` -/
theorem pw_in {pl lm j bp : Nat} (hj : j + 2 ≤ pl + 1) :
    bp + 8 * (j * W lm) + 8 * (2 * W lm) ≤ bp + 8 * NB pl lm := by
  have : (j + 2) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ hj
  simp only [NB]; rw [Nat.add_mul] at this; omega

/-- two `powers` slots `j < k` do not overlap -/
theorem pw_sep {lm j k : Nat} (h : j < k) : j * W lm + W lm ≤ k * W lm := by
  have : (j + 1) * W lm ≤ k * W lm := Nat.mul_le_mul_right _ h
  rw [Nat.add_mul, Nat.one_mul] at this; exact this

section
variable {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- an array `[a, a + 8 c)` inside `buf` as a callee operand / result -/
theorem bufArr (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) (hf : PF R kc L st pw pl s)
    {S' : State} (hsp : S'.sp.toNat = s.sp.toNat - 208) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {a c : Nat} (h1 : bp ≤ a)
    (h2 : a + 8 * c ≤ bp + 8 * NB pl lm) (h0 : 0 < c) (hal : a % 8 = 0) (hc40 : c < 2 ^ 40) :
    WrOut R L1 S' stk above a c ∧ (∀ l, l ≤ c → RdIn R L1 S' stk above a l) ∧ (∀ l, l ≤ c → CapIn R L1 a l c) ∧
      StkApart M st a (8 * c) := by
  obtain ⟨o48, oacc, oheld, owin, og, osa⟩ := bufObj hpre hc hf hsp hstk habove h1 h2 (by omega)
  subst hm
  refine ⟨⟨hc40, fun _ => ⟨hal, oheld, oacc, o48⟩, fun _ => ⟨owin, by rw [h28]; exact og⟩⟩, fun l hl => ?_,
    fun l hl => ⟨hl, hc40, oheld, o48⟩, osa⟩
  refine ⟨by omega, Memory.accessible_weaken _ (Memory.accessible_mono _ oacc (Nat.le_refl _) (by omega)), by omega,
    oheld.sub (Nat.le_refl _) (by omega), owin.of_sub (Nat.le_refl _) (by omega)⟩

end

end FvModexp.Arm64.P2Pre
