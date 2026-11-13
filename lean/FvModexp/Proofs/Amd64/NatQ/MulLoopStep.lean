import FvModexp.Proofs.Amd64.NatQ.MulLoopT

/-!
# [amd64 port (divmc s45) of the Q-form Arm64/NatQ/MulLoopStep.lean — TIGHT COSTS] `nat.mul` (amd64), chunk loop: pure step lemmas between the call segments

`LB.stkCls` (the stack's current header / free part are `LCls` ranges), `TOK.after` (`t`'s facts after an inner call:
`t` kept or replaced by a fresh array), `LB.pkeep` (`p[0:m+n]` is untouched by a callee writing only `t`, the stack and
fresh memory), `chunk_val` (the value after `addTo(z[i:], t)`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory} {tp tc : Nat}

/-- the stack's current header and free part are classified write ranges -/
theorem LB.stkCls (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    LCls R L1 M st p (xl + yl) (stkWs Mi st) := by
  have hlc := h.sok.2.2.2.2.2.1
  intro r hr
  simp only [stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by simp only; omega, Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)⟩
  · refine ⟨by simp only; omega, ?_⟩
    rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
    · simp only; rw [e1, e2]; rw [e2] at hlc
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hin.sub (by simp only; omega) (by simp only; omega),
        ApartAll.sub' hap (by simp only; omega) (by simp only; omega)⟩))

/-- the stack's array is never empty inside the loop -/
theorem LB.cap0 (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) : 0 < stCap Mi st := by
  have hlc := h.sok.2.2.2.2.2.1
  have := h.slen; have := h.h40; simp only [rnd] at *; omega

/-- **`t` after an inner call** that brought the stack back: the old `t` (kept), or a fresh array (inside `R.rt`,
apart from the old live set and from the final stack array) -/
theorem TOK.after (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi)
    (ht : TOK R L1 Lk M Mi st tp tc) {Lk' : List (Nat × Nat)} {bk' spent' : Nat} {Mi' : Memory}
    (h' : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' spent' Mi')
    (hsb : StackBack R Lk Lk' st Mi Mi') (hext : LiveExt R Lk Lk') {tp' tc' : Nat} (hc40 : tc' < 2 ^ 40)
    (hl : NatLive Mi' R Lk' tp' tc')
    (hk : (tp' = tp ∧ tc' = tc) ∨ (0 < tc' ∧ InRanges tp' (8 * tc') R.rt ∧ ApartAll tp' (8 * tc') Lk ∧
      Apart tp' (8 * tc') (stW Mi' st) (8 * stCap Mi' st))) :
    TOK R L1 Lk' M Mi' st tp' tc' := by
  obtain ⟨ht0, ht40, htl, hloc, hts⟩ := ht
  have hlc' := h'.sok.2.2.2.2.2.1
  obtain ⟨-, hlen, harr⟩ := hsb
  rcases hk with ⟨rfl, rfl⟩ | ⟨h0, hin, hap, hst⟩
  · refine ⟨ht0, ht40, hl, hloc, hts.1, ?_, hts.2.2⟩
    have hf := hts.2.1
    simp only [BasicSqr.freeP, BasicSqr.freeN] at hf ⊢
    rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2, hlen]; exact hf
    · have := apart_of_held (htl ht0).2.1 hin hap
      unfold Apart at this ⊢; omega
  · refine ⟨h0, hc40, hl, Or.inr ⟨hin, fun r hr => hap r (h.ext.mem_old hr)⟩, ?_, ?_, ?_⟩
    · have := apart_of_held h.sok.2.1 hin hap; unfold Apart at this ⊢; omega
    · simp only [BasicSqr.freeP, BasicSqr.freeN]; unfold Apart at hst ⊢; omega
    · have hgrt : Outside RunIface.gA 32 R.rt := h.core.pre.2.2.2.1.2.2.2.2.2.2.2.2.1
      have := NatSub.outside_of_inRanges hgrt hin; unfold Apart; omega

/-- `p[0:m+n]` survives a callee entered at `RSP - 264` writing `R.rt`, its window, `t` and the stack's header / free part -/
theorem LB.pkeep (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi)
    (ht : TOK R L1 Lk M Mi st tp tc) {Mi' : Memory} {k a : Nat} (hk : 264 + k ≤ W) (ha : a ≤ 88)
    (hF : MemFrame Mi Mi' (R.rt ++ [((s.regs 4).toNat - 264 - k, (s.regs 4).toNat - 264 + a)] ++
      ([(tp, tp + 8 * tc)] ++ stkWs Mi st)))
    (hLF : LiveFrame Mi Mi' Lk ([(tp, tp + 8 * tc)] ++ stkWs Mi st)) :
    natVal Mi' p (xl + yl) = natVal Mi p (xl + yl) := by
  obtain ⟨hW, hWs, -, -, -, -, -, hcap, hc40, hpw, -⟩ := h.lay
  obtain ⟨-, -, htp, -⟩ := h.tsep ht
  have h40 := h.h40
  have hpst := h.core.pst (by omega)
  have hpf := h.core.pfree (by omega)
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have hpH1 : Held R L1 p (8 * (xl + yl)) := by
    rcases h.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := h.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact h.core.ext.held ((hzl (by omega)).2.1.sub (Nat.le_refl _) (by omega))
    · exact Or.inl (hin1.sub (Nat.le_refl _) (by omega))
  have hfree : Apart p (8 * (xl + yl)) (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) := by
    have hlc := h.sok.2.2.2.2.2.1
    simp only [BasicSqr.freeP, BasicSqr.freeN] at hpf ⊢
    rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
    · rw [e1, e2, eW, eC]; rw [eL] at e3; unfold Apart at hpf ⊢; omega
    · have := apart_of_held hpH1 hin hap
      unfold Apart at this ⊢; omega
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfree
  unfold Apart at htp hpst hfree
  unfold natVal
  refine Held.readLE2 (h.ext.held hpH1) hF hLF ?_ ?_
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega

/-- **the value after `addTo(z[i:], t)`**: `z = lo + B^i·hi` held `X[0:i]·Y`, `t = X[i:i+cc]·Y`, and the full product
fits in `i + k` words, so `hi + t` does not wrap -/
theorem chunk_val (lo hi T Xi Xc Y i k : Nat) (hA : lo + 2 ^ (64 * i) * hi = Xi * Y)
    (hlt : (Xi + 2 ^ (64 * i) * Xc) * Y < 2 ^ (64 * (i + k))) (hT : T = Xc * Y) :
    lo + 2 ^ (64 * i) * ((hi + T) % 2 ^ (64 * k)) = (Xi + 2 ^ (64 * i) * Xc) * Y := by
  have e : 2 ^ (64 * (i + k)) = 2 ^ (64 * i) * 2 ^ (64 * k) := by rw [Nat.mul_add, Nat.pow_add]
  have hsum : lo + 2 ^ (64 * i) * (hi + T) = (Xi + 2 ^ (64 * i) * Xc) * Y := by
    rw [Nat.mul_add, ← Nat.add_assoc, hA, hT, Nat.add_mul, Nat.mul_assoc]
  have h1 : hi + T < 2 ^ (64 * k) := by
    have : 2 ^ (64 * i) * (hi + T) < 2 ^ (64 * i) * 2 ^ (64 * k) := by rw [← e]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  rw [Nat.mod_eq_of_lt h1]; exact hsum

end

end FvModexp.Amd64.Q.NatMul
