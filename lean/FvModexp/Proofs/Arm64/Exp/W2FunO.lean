import FvModexp.Proofs.Arm64.Exp.W2Anc
import FvModexp.Proofs.Arm64.Exp.W2RR

/-!
# window-2 (arm64): the written ranges of each segment of the post chain, as `Outside` facts

For a range `(a, k)` outside the function-level frame of window-2 (window minus the caller's FP/LR slots, the stack
header, the entry free part, `z`), and apart from the buffers a segment writes, the segment's write lists miss it.
Small separate lemmas: `omega` runs in a tiny context.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

/-- outside window-2's frame (except the caller's saved FP/LR) -/
@[reducible] def Zw (sp K a k : Nat) : Prop := (a + k ≤ sp - K ∨ sp + 632 ≤ a) ∧ (a + k ≤ sp + 648 ∨ sp + 752 ≤ a)

theorem out_S0 {sp K st a k : Nat} (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a) :
    Outside a k [(sp - K, sp + 632), (sp + 648, sp + 752), (st, st + 24)] ∧ Outside a k [(st, st + 24)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem out_S1 {sp K st a k : Nat} {M : Memory} (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hf : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) (hlc : stLen M st ≤ stCap M st) :
    Outside a k (aw sp K st M) ∧ Outside a k [(st, st + 24), frA st M] := by
  simp only [aw, frA, outside_cons, outside_nil, and_true]; omega

theorem out_S2 {sp K n zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K) (hz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a)
    (hn : n ≤ zzc) : Outside a k (rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ Outside a k [(zzp, zzp + 8 * n)] := by
  simp only [rw4, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S3 {sp K st a k : Nat} {M : Memory} (hw : Zw sp K a k) (hK : 4304 ≤ K) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hf : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) :
    Outside a k (ow sp ++ ([(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M st)) ∧ Outside a k (stkWs M st) := by
  simp only [ow, stkWs, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S4 {sp K n bp a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K)
    (hb : a + k ≤ bp ∨ bp + 8 * (5 * n) ≤ a) :
    Outside a k (tw sp bp n) ∧ Outside a k [(bp, bp + 8 * (5 * n))] := by
  simp only [tw, qw, pw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S5 {sp K a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K) :
    Outside a k [(sp - 4096, sp - 8), (sp + 8, sp + 152)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem out_S6 {sp K n zp zc a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K) (hz : a + k ≤ zp ∨ zp + 8 * zc ≤ a)
    (hn : n ≤ zc) : Outside a k (cw sp ++ [(zp, zp + 8 * n)]) ∧ Outside a k [(zp, zp + 8 * n)] := by
  simp only [cw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S7 {sp K zp zc zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K) (hz : a + k ≤ zp ∨ zp + 8 * zc ≤ a)
    (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    Outside a k (W2Loop.fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]) ∧
      Outside a k [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)] := by
  simp only [W2Loop.fw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S8 {sp K zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K) (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    Outside a k ([(sp - 4304, sp - 8), (sp + 8, sp + 80), (sp + 160, sp + 176), (sp + 400, sp + 408)] ++
      [(zzp, zzp + 8 * zzc)]) ∧ Outside a k [(zzp, zzp + 8 * zzc)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S9 {sp K st a k : Nat} (hw : Zw sp K a k) (hK : 4304 ≤ K) (hd : a + k ≤ st ∨ st + 24 ≤ a) :
    Outside a k [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

/-- a read unchanged by one segment: outside `R.rt` and the segment's ranges, or in the live set outside its
`LiveFrame` ranges -/
theorem rd_step {R : RtInv} {L Li ws ws' : List (Nat × Nat)} {M M' : Memory} {a k : Nat}
    (hF : MemFrame M M' (R.rt ++ ws)) (hL : LiveFrame M M' Li ws') (hx : LiveExt R L Li)
    (hh : Outside a k R.rt ∨ InRanges a k L) (h1 : Outside a k ws) (h2 : Outside a k ws') :
    M'.readLE a k = M.readLE a k := by
  rcases hh with h | h
  · exact hF.readLE a k (by rw [outside_append]; exact ⟨h, h1⟩)
  · exact hL.readLE a k (hx.inRanges_old h) h2

/-- a held range is apart from a fresh object of a larger live set -/
theorem ap_fresh {R : RtInv} {L L' : List (Nat × Nat)} {p q a k : Nat} (hin : InRanges p q R.rt)
    (hap : ApartAll p q L') (hx : LiveExt R L L') (hh : Outside a k R.rt ∨ InRanges a k L) :
    a + k ≤ p ∨ p + q ≤ a := by
  have := apart_held' hin hap (hh.symm.imp hx.inRanges_old id); unfold Apart at this; omega

/-- the stack's array at `M` (the entry's or a fresh one) above the entry length misses a held range outside the
entry's free part -/
theorem arr_ap {R : RtInv} {L : List (Nat × Nat)} {st a k l : Nat} {M0 M : Memory}
    (hkf : (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
      (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L))
    (hh : Outside a k R.rt ∨ InRanges a k L)
    (hf : a + k ≤ stW M0 st + 8 * stLen M0 st ∨ stW M0 st + 8 * stCap M0 st ≤ a) (hl : stLen M0 st ≤ l) :
    a + k ≤ stW M st + 8 * l ∨ stW M st + 8 * stCap M st ≤ a := by
  rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]; omega
  · have := ap_fresh hin hap (LiveExt.refl R L) hh; omega

/-- kept-or-fresh arrays compose -/
theorem akf_trans {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {M0 M M' : Memory}
    (h : (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
      (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L))
    (hx : LiveExt R L L')
    (h' : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L')) :
    (stW M' st = stW M0 st ∧ stCap M' st = stCap M0 st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L) := by
  rcases h' with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]; exact h
  · exact Or.inr ⟨hin, apartAll_ext hx hap⟩

/-- the stack array after a split stack-nat-like step (kept when it fits, else a fresh element of `L'`) -/
theorem arrIn_split {L' : List (Nat × Nat)} {st r : Nat} {M M' : Memory}
    (hk : stLen M st + r ≤ stCap M st → stW M' st = stW M st ∧ stCap M' st = stCap M st)
    (hm : stCap M st < stLen M st + r → (stW M' st, stW M' st + 8 * stCap M' st) ∈ L') : ArrIn L' st M M' := by
  intro hn
  by_cases hc : stLen M st + r ≤ stCap M st
  · exact absurd (hk hc) hn
  · exact hm (by omega)

/-- `ArrIn` along the window's chain: reserve, prologue (`Anc`), header-keeping steps, the `stk.nat` step -/
theorem arrIn_chain {R : RtInv} {L1 Ld L2 L'' : List (Nat × Nat)} {st : Nat} {M0 M Md M1 M2 M' : Memory}
    (h0 : ArrIn L1 st M0 M) (hd : ArrIn Ld st M Md) (hxd : LiveExt R L1 Ld)
    (e1 : stW M1 st = stW Md st ∧ stCap M1 st = stCap Md st) (hs : ArrIn L2 st M1 M2) (hx3 : LiveExt R Ld L2)
    (e2 : stW M' st = stW M2 st ∧ stCap M' st = stCap M2 st) (hx : LiveExt R L2 L'') : ArrIn L'' st M0 M' := by
  intro hn
  have a1 := ArrIn.trans h0 hd hxd
  have a1' : ArrIn Ld st M0 M1 := by
    intro h; rw [e1.1, e1.2] at h ⊢; exact a1 h
  have a2 := ArrIn.trans a1' hs hx3
  rw [e2.1, e2.2] at hn ⊢; exact hx.mem_old (a2 hn)

end FvModexp.Arm64.W2Pro
