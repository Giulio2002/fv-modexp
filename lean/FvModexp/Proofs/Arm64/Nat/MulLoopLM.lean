import FvModexp.Proofs.Arm64.Nat.MulLoopHead

/-!
# `nat.mul` (arm64), chunk loop: `LM` from the chunk product's post (`lm_of`)

`LB.calleeKeep` (a callee at `SP - 256` keeps our frame slots above its `above` area), `LB.xval` / `LB.yval` (operand
words keep their entry values), `lm_of`: the head's facts at the call memory + `MPost` of `t.mul(stk, x[i:i+cc], y)`
⟹ `LM` at the return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

set_option maxRecDepth 20000 in
/-- a callee at `SP - 256` (window `k`, above `a ≤ 88`, classified writes) keeps the bytes of our frame from
`SP - 264` up to its return-address slot and from `SP - 168` (`SP' + 88`) up to `SP + 88` -/
theorem LB.calleeKeep (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    {k a : Nat} (hk : 256 + k ≤ W) (ha : a ≤ 88) {ws : List (Nat × Nat)} (hws : LCls R L1 M st p (xl + yl) ws)
    (hF : MemFrame Mi Mi' (R.rt ++ [(s.sp.toNat - 256 - k, s.sp.toNat - 256 - 8), (s.sp.toNat - 256 + 8,
      s.sp.toNat - 256 + a)] ++ ws)) :
    ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat + 88 → (x + m ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 168 ≤ x) →
      Mi'.readLE x m = Mi.readLE x m := by
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hcl := h.cls hws
  have hko := h.lwsOut
  intro x m h1 h2 h3
  refine hF.readLE _ _ ?_
  simp only [outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, outside_of_forall fun r hr => ?_⟩
  obtain ⟨hle, hc⟩ := hcl r hr
  rcases hc with ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
  · have := hko q hq; omega
  · have := NatSub.outside_of_inRanges (hout.of_sub (a := x) (n := m) (by omega) (by omega)) hin; omega

/-- `x`'s words keep their entry values -/
theorem LB.xval (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi)
    (hpx : Apart p (8 * c) xp (8 * xl)) {a n : Nat} (h1 : xp ≤ a) (h2 : a + 8 * n ≤ xp + 8 * xl) :
    natVal Mi a n = natVal s.mem a n := by
  obtain ⟨-, -, -, -, -, ⟨⟨hxlc, -, -, -, hxh, hxw⟩, -⟩, -⟩ := h.core.pre
  have hcap := h.core.cap
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [natVal, Memory.readLE]
  obtain ⟨hxo, hxs⟩ := hxw (by omega)
  have hH : Held R L xp (8 * xl) := (hxh (by omega)).1.sub (Nat.le_refl _) (by omega)
  unfold natVal
  exact h.rd (hH.sub h1 h2) (hxo.of_sub h1 h2) (stkSep_sub hxs h1 h2) (by unfold Apart at hpx ⊢; omega)

/-- `y`'s words keep their entry values -/
theorem LB.yval (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi)
    (hpy : Apart p (8 * c) yp (8 * yl)) : natVal Mi yp yl = natVal s.mem yp yl := by
  obtain ⟨-, -, -, -, -, ⟨-, ⟨hylc, -, -, -, hyh, hyw⟩, -⟩, -⟩ := h.core.pre
  have hcap := h.core.cap
  have h40 := h.h40
  obtain ⟨hyo, hys⟩ := hyw (by omega)
  have hH : Held R L yp (8 * yl) := (hyh (by omega)).1.sub (Nat.le_refl _) (by omega)
  unfold natVal
  exact h.rd hH hyo hys (by unfold Apart at hpy ⊢; omega)

end

set_option maxRecDepth 20000 in
/-- **`LM` from the chunk product's post** -/
theorem lm_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tc : Nat}
    {Mc : Memory} (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp (stLen M st) yl k) Mc)
    (ht : TOK R L1 Lk M Mc st tp tc) (hpx : Apart p (8 * c) xp (8 * xl)) (hpy : Apart p (8 * c) yp (8 * yl))
    (hilt : (k + 1) * yl < xl) (hv : natVal Mc p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl)
    (m128 : Mc.readLE (s.sp.toNat - 128) 8 = (k + 1) * yl)
    (m136 : Mc.readLE (s.sp.toNat - 120) 8 = (k + 1) * yl + yl)
    {cc : Nat} (hcc : cc = min yl (xl - (k + 1) * yl))
    {S1 s2 : State} (hsp1 : S1.sp.toNat = s.sp.toNat - 256) (hg1 : S1.regs 28 = s.regs 28) (hm1 : S1.mem = Mc)
    (hq : MPost R bk Lk (W - 256) tp tc st (xp + 8 * ((k + 1) * yl)) cc (xc - (k + 1) * yl) yp yl yc S1 s2)
    (hreg : s2.mem.regions = Mc.regions)
    (hpc : s2.pc = BitVec.ofNat 64 0x1bb264) (hsp : s2.sp = s.sp - 256#64) (hg : s2.regs 28 = s.regs 28)
    (hfp : s2.regs 29 = s.sp - 264#64) (h18 : s2.regs 18 = s.regs 18) :
    ∃ (Lk' : List (Nat × Nat)) (bk' tp' tl' tc' : Nat),
      LM R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' k tp' tl' tc' s2 := by
  obtain ⟨p', l', c', q0, q1, q2, hval, -, hlc, hll, hc40, Lk', bk', hext, hbud, hinv, hlive, hkind, hfresh, -, hsb,
    hMF, hLF⟩ := hq
  rw [hm1] at hval hbud hsb hMF hLF
  obtain ⟨hW, -⟩ := h.lay
  have h40 := h.h40
  have hWm : 256 + (W - 256) ≤ W := by omega
  have hF : MemFrame Mc s2.mem (R.rt ++ [(s.sp.toNat - 256 - (W - 256), s.sp.toNat - 256 - 8),
      (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 88)] ++ ([(tp, tp + 8 * tc)] ++ stkWs Mc st)) := by
    simpa only [List.append_assoc, winA, hsp1] using hMF
  have hcls : LCls R L1 M st p (xl + yl) ([(tp, tp + 8 * tc)] ++ stkWs Mc st) := (ht.cls _).append h.stkCls
  have hsl := h.slen
  have hcost : mulC (stLen Mc st) cc yl ≤ MC (stLen M st + rnd (2 * yl)) yl yl := by
    rw [hsl]; exact mulC_le_chunk (by omega)
  have h' := (h.step hWm (Nat.le_refl _) hcls hF hLF hreg hext hbud (by rw [hg1] at hinv; exact hinv) hsb).wk
    (spent' := lsp (stLen M st) yl (k + 1)) (by rw [← lsp_step]; omega)
  have hkeep := h.calleeKeep hWm (Nat.le_refl _) hcls hF
  have ht' : TOK R L1 Lk' M s2.mem st p' c' := by
    refine TOK.after h ht h' hsb.1 hext hc40 hlive ?_
    by_cases he : p' = tp ∧ c' = tc
    · exact Or.inl he
    · rcases hkind with he' | ⟨hcc', hin, hap⟩
      · exact absurd he' he
      · have hc0 : 0 < c' := by omega
        exact Or.inr ⟨hc0, hin, hap, hfresh he hc0 h'.cap0⟩
  have hpk := h.pkeep ht hWm (Nat.le_refl _) hF hLF
  have hxv := h.xval hpx (a := xp + 8 * ((k + 1) * yl)) (n := cc) (by omega) (by omega)
  have hyv := h.yval hpy
  have htll : (k + 1) * yl + l' ≤ xl + yl := by
    have : cc ≤ xl - (k + 1) * yl := by rw [hcc]; exact Nat.min_le_right _ _
    omega
  have htv : natVal s2.mem p' l' =
      natVal s.mem (xp + 8 * ((k + 1) * yl)) (min yl (xl - (k + 1) * yl)) * natVal s.mem yp yl := by
    rw [hval, hxv, hyv, hcc]
  have hval' : natVal s2.mem p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl := by
    rw [hpk, hv]
  refine ⟨Lk', bk', p', l', c',
    { lb := h', pc := hpc, sp := hsp, g := hg, fp := hfp, x18 := h18, r0 := q0, r1 := q1, r2 := q2, ilt := hilt,
      m128 := by rw [hkeep _ _ (by omega) (by omega) (by omega)]; exact m128,
      m136 := by rw [hkeep _ _ (by omega) (by omega) (by omega)]; exact m136,
      tok := ht', px := hpx, py := hpy, tlc := hlc, tll := htll,
      tv := htv,
      val := hval' }⟩

end FvModexp.Arm64.NatMul
