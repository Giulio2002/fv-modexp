import FvModexp.Proofs.Amd64.Exp.W4FunO
import FvModexp.Proofs.Amd64.Exp.W4FunV
import FvModexp.Proofs.Common.SqrCost

set_option autoImplicit false
set_option maxRecDepth 20000

/-!
# `nat.expNNOddMontgomeryWindowSize4` (amd64): costs and small helpers of the function-level post (agent expmc s58;
twin of the helper part of `Arm64.ExpW4` `W4Fun`)

`xnPreM`: the division prefix cost of the `x` normalisation (MAXIMUM over its four paths, TIGHT COSTS); `lvT`: the
stack level bound at the `stk.nat(17n)`; `W4Cost`: what the post charges. The helpers decompose the function-level
frame (`final_out`/`final_outL`), locate held ranges w.r.t. the window (`zw_of_ap`/`zw_of_sep`), move the result
array and the invariant through the epilogue (`out10_p`, `out10_fresh`, `inv_fin`), and pick the result's location
(`res_of`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- the division prefix cost of the `x` normalisation at level `l` (max over the paths C, B, A·C, A·B) -/
def xnPreM (n costD l xl : Nat) : Nat :=
  max (max (xjPre n costD l) (stackNatCost l n + xjPre n costD (l + StackNat.rnd n)))
    (max (stackNatCost l (xl - n + 1) + (stackNatCost (l + StackNat.rnd (xl - n + 1)) n +
      (costD + xjPre n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n))))
    (stackNatCost l (xl - n + 1) + (stackNatCost (l + StackNat.rnd (xl - n + 1)) n +
      (costD + (stackNatCost (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
        xjPre n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n))))))

/-- `XnBudA` at the lower bound `b1 - xnPreM` (any `b1` that `XnB` admits) -/
theorem xnBudA_of {costF : Nat → Nat → Nat → Nat} {n costD l xl b1 : Nat} (h : W4En.XnB costF n costD l xl b1) :
    XnBudA n costD l xl (b1 - xnPreM n costD l xl) b1 := by
  obtain ⟨-, -, a3, a4, -, -, -, -, a9, a10⟩ := h
  have p1 := xjPre_le n costD l
  have p2 := xjPre_le n costD (l + StackNat.rnd n)
  have p3 := xjPre_le n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n)
  have p4 := xjPre_le n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n)
  simp only [XnBudA, xnPreM]
  generalize xjPre n costD l = x1 at *
  generalize xjPre n costD (l + StackNat.rnd n) = x2 at *
  generalize xjPre n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n) = x3 at *
  generalize xjPre n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n) = x4 at *
  omega

/-- the stack level bound at the `stk.nat(17n)` (`l` = the entry length) -/
@[reducible] def lvT (n xl l : Nat) : Nat := lvU n xl (l + StackNat.rnd (23 * n))

/-- the cost the postcondition charges -/
def W4Cost (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + xnPreM n costD (l + StackNat.rnd (23 * n)) xl + blockSize (8 * n) true +
    stackNatCost (lvT n xl l) (17 * n) + 2 * blockSize (8 * (2 * n + 4)) true + makeCost n

theorem snc_le {l l' n : Nat} (h : l ≤ l') : stackNatCost l n ≤ stackNatCost l' n :=
  FvModexp.stackNatCost_mono h (Nat.le_refl n)

theorem if_le (n : Nat) : (if 4 < n then blockSize (8 * n) true else 0) ≤ blockSize (8 * n) true := by
  split <;> omega

/-- the budget along the chain -/
theorem bud_fin {b b1 bA bd b2 b3 b4 b5 s0 P blk blk' s17 s17' bs mk : Nat} (hb1 : b - s0 ≤ b1) (hbA : bA = b1 - P)
    (hbd : bA ≤ bd) (hb2 : bd - (blk' + s17') ≤ b2) (hb3 : b2 - bs ≤ b3) (hb4 : b3 - bs ≤ b4) (hb5 : b4 - mk ≤ b5)
    (h1 : blk' ≤ blk) (h2 : s17' ≤ s17) : b - (s0 + P + blk + s17 + 2 * bs + mk) ≤ b5 := by omega


/-- the function-level frame, decomposed -/
theorem final_out {R : RtInv} {s : State} {M : Memory} {sp K st zp zc a k : Nat}
    (ho : Outside a k (R.rt ++ win s (K + 0x390) 0x70 ++ [(zp, zp + 8 * zc)] ++ stkWs M st))
    (hS : (s.regs 4).toNat = sp + 0x388) (hKs : K + 8 ≤ sp) :
    Outside a k R.rt ∧ Zw sp K a k ∧ (a + k ≤ st ∨ st + 24 ≤ a) ∧
      (a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) ∧ (a + k ≤ zp ∨ zp + 8 * zc ≤ a) := by
  simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true, hS] at ho
  obtain ⟨⟨⟨h0, h1⟩, h3⟩, h4, h5⟩ := ho
  exact ⟨h0, by simp only [Zw]; omega, h4, h5, h3⟩

theorem final_outL {M : Memory} {st zp zc a k : Nat} (ho : Outside a k ([(zp, zp + 8 * zc)] ++ stkWs M st)) :
    (a + k ≤ st ∨ st + 24 ≤ a) ∧ (a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) ∧
      (a + k ≤ zp ∨ zp + 8 * zc ≤ a) := by
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
  exact ⟨ho.2.1, ho.2.2, ho.1⟩

theorem zw_of_ap {sp K a k : Nat} (h : Apart a k (sp - 8 - K) (K + 0x400)) (hKs : K + 8 ≤ sp) : Zw sp K a k := by
  have h' : a + k ≤ sp - 8 - K ∨ sp - 8 - K + (K + 0x400) ≤ a := h
  simp only [Zw]; omega

theorem zw_of_sep {L : List (Nat × Nat)} {sp K a k : Nat} (hLs : LiveSep L [(sp - 8 - K, sp - 8 + 0x400)])
    (h : InRanges a k L) (hKs : K + 8 ≤ sp) : Zw sp K a k := by
  have := apart_of_inRanges_sep hLs h (by omega)
  unfold Apart at this; simp only [Zw]; omega

theorem out10_p {sp st p q : Nat} (hw : Apart p q (sp - 4296) (4296 + 0x3c0)) (hd : Apart p q st 24) (hs : 4296 ≤ sp) :
    Outside p q [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188), (st + 8, st + 16)] := by
  unfold Apart at hw hd; simp only [outside_cons, outside_nil, and_true]; omega

theorem out10_fresh {R : RtInv} {sp K st p q : Nat} (hrt : Outside (sp - 8 - K) (K + 0x400) R.rt)
    (hin : InRanges p q R.rt) (hd : p + q ≤ st ∨ st + 24 ≤ p) (hK : 4296 ≤ K) (hKs : K + 8 ≤ sp) :
    Outside p q [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188), (st + 8, st + 16)] := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have h3 := MemFrame.outside_mem hrt hr
  simp only [outside_cons, outside_nil, and_true] at h3 ⊢
  omega

theorem natLive_tr {R : RtInv} {L L' : List (Nat × Nat)} {M M' : Memory} {p c : Nat} (h : NatLive M R L p c)
    (hx : LiveExt R L L') (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w) : NatLive M' R L' p c :=
  fun hc => ⟨(h hc).1, hx.held (h hc).2.1, by rw [hacc]; exact (h hc).2.2.1, (h hc).2.2.2⟩

theorem inv_fin {R : RtInv} {b g sp K st : Nat} {L : List (Nat × Nat)} {M M' : Memory}
    (hF : MemFrame M M' [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188), (st + 8, st + 16)])
    (hrt : Outside (sp - 8 - K) (K + 0x400) R.rt) (hst : Held R L st 24) (hK : 4296 ≤ K) (hKs : K + 8 ≤ sp)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L M') := by
  refine FvModexp.Expmc.inv_frame hF (fun r hr => ?_) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inr (hrt.of_sub (by omega) (by omega))
  · exact Or.inr (hrt.of_sub (by omega) (by omega))
  · exact Or.inr (hrt.of_sub (by omega) (by omega))
  · exact hst.sub (by simp only; omega) (by simp only; omega)

/-- the result array: `z`'s or a fresh runtime object -/
theorem res_of {R : RtInv} {L L1 L2 L' : List (Nat × Nat)} {zp zc zp' zc' zzp zzc zp'' zc'' zzp'' zzc'' p c : Nat}
    (hor : (p = zzp'' ∧ c = zzc'') ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L'))
    (hP : (zp'' = zp' ∧ zc'' = zc' ∧ zzp'' = zzp ∧ zzc'' = zzc) ∨ (zp'' = zzp ∧ zc'' = zzc ∧ zzp'' = zp' ∧ zzc'' = zc'))
    (hzo : (zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L2))
    (hzz : InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L1)
    (x1 : LiveExt R L L1) (x2 : LiveExt R L L2) (x5 : LiveExt R L L') :
    (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L) := by
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · have hz' : (zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L) :=
      hzo.imp id fun h => ⟨h.1, apartAll_old x2 h.2⟩
    rcases hP with ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · exact Or.inr ⟨hzz.1, apartAll_old x1 hzz.2⟩
    · exact hz'
  · exact Or.inr ⟨hin, apartAll_old x5 hap⟩

theorem norm_tr {M M' : Memory} {p l c : Nat} (hn : NatNorm M p l) (hl : l ≤ c)
    (hr : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k) : NatNorm M' p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact Or.inl h0
  rcases hn with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hr _ _ (by omega) (by omega)]; exact h)

theorem top_ne {M : Memory} {yp ylen : Nat} (h : NatNorm M yp ylen) (hy : 0 < ylen) :
    M.readLE (yp + 8 * (ylen - 1)) 8 ≠ 0 := by
  rcases h with h | h
  · omega
  · exact h

end FvModexp.Amd64.W4Pro
