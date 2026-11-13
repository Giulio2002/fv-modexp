import FvModexp.Proofs.Amd64.Exp.W4FunB
import FvModexp.Proofs.Amd64.Exp.W4En

set_option autoImplicit false

/-!
# window-4 (amd64): the written ranges of each segment of the post chain, as `Outside` facts (agent expmc s58;
twin of `Arm64.W4Pro` `W4FunO`)

For a range `(a, k)` outside window-4's frame window `[sp - 8 - K, sp + 0x3f8)` (`Zw`), the stack header, the entry
free part, `z`, and apart from the buffers a segment writes, the segment's write lists miss it. The chain:
`S0` entry (`EnPost`) · `S1` prologue up to the division's return (`Anc.frame`) · `S2` `RR` (`RRPost`) · `S3`
`stk.nat(17n)` (`OneChain`) · `S4` table (`FP`) · `S5`/`S6` `z`/`zz` make (`ZPost`) · `S7` `z` clear (`ZjPost`) ·
`S8` loop (`FL`) · `S9` join (`JoinPost`) · `S10` epilogue (`FinPost`). Small separate lemmas: `omega` runs in a
tiny context.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- outside window-4's frame window -/
@[reducible] def Zw (sp K a k : Nat) : Prop := a + k ≤ sp - 8 - K ∨ sp + 0x3f8 ≤ a

theorem out_S0 {sp K st a k : Nat} (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a) :
    Outside a k [(sp - 8 - K, sp + 0x3f8), (st, st + 24)] ∧ Outside a k [(st, st + 24)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem out_S1 {sp K st a k : Nat} {M : Memory} (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hf : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) :
    Outside a k ([(sp - 8 - K, sp + 0x3c0)] ++ stkWs M st) ∧ Outside a k (stkWs M st) := by
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S2 {sp K n zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a)
    (hn : n ≤ zzc) : Outside a k (rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ Outside a k [(zzp, zzp + 8 * n)] := by
  simp only [rw4, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S3 {sp K st a k : Nat} {M : Memory} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hf : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) :
    Outside a k (ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st) ∧ Outside a k (stkWs M st) := by
  simp only [ow, stkWs, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S4 {sp K bp bc a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hb : a + k ≤ bp ∨ bp + 8 * bc ≤ a) :
    Outside a k (pw sp ++ [(bp, bp + 8 * bc)]) ∧ Outside a k [(bp, bp + 8 * bc)] := by
  simp only [pw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S5 {sp K a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) : Outside a k (zw1 sp) := by
  simp only [zw1, outside_cons, outside_nil, and_true]; omega

theorem out_S6 {sp K a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) : Outside a k (zw2 sp) := by
  simp only [zw2, outside_cons, outside_nil, and_true]; omega

theorem out_S7 {sp K n zp zc a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hz : a + k ≤ zp ∨ zp + 8 * zc ≤ a)
    (hn : n ≤ zc) : Outside a k (cw sp ++ [(zp, zp + 8 * n)]) ∧ Outside a k [(zp, zp + 8 * n)] := by
  simp only [cw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S8 {sp K zp zc zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hz : a + k ≤ zp ∨ zp + 8 * zc ≤ a)
    (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    Outside a k (W4Loop.fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]) ∧
      Outside a k [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)] := by
  simp only [W4Loop.fw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S9 {sp K zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    Outside a k ([(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x188, sp + 0x190)] ++
      [(zzp, zzp + 8 * zzc)]) ∧ Outside a k [(zzp, zzp + 8 * zzc)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S10 {sp K st a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hd : a + k ≤ st ∨ st + 24 ≤ a) :
    Outside a k [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188), (st + 8, st + 16)] := by
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
  · exact Or.inr ⟨hin, apartAll_old hx hap⟩

/-- the stack array after a split stack-nat-like step (kept when it fits, else a fresh element of `L'`) -/
theorem arrIn_split {L' : List (Nat × Nat)} {st r : Nat} {M M' : Memory}
    (hlc : stLen M' st ≤ stCap M' st) (hl : stLen M' st = stLen M st + r)
    (hk : stLen M st + r ≤ stCap M st → stW M' st = stW M st ∧ stCap M' st = stCap M st)
    (hm : stCap M st < stLen M st + r → (stW M' st, stW M' st + 8 * stCap M' st) ∈ L') : ArrIn L' st M M' :=
  ArrIn.of_nat hlc hl hk hm

/-- `ArrIn` along the window's chain: reserve, prologue (`Anc`), header-keeping steps, the `stk.nat(17n)` step -/
theorem arrIn_chain {R : RtInv} {L1 Ld L2 L'' : List (Nat × Nat)} {st : Nat} {M0 M Md M1 M2 M' : Memory}
    (h0 : ArrIn L1 st M0 M) (hd : ArrIn Ld st M Md) (hxd : LiveExt R L1 Ld)
    (e1 : stW M1 st = stW Md st ∧ stCap M1 st = stCap Md st) (hs : ArrIn L2 st M1 M2) (hx3 : LiveExt R Ld L2)
    (e2 : stW M' st = stW M2 st ∧ stCap M' st = stCap M2 st) (hx : LiveExt R L2 L'') : ArrIn L'' st M0 M' := by
  intro hn
  have a1 := ArrIn.trans h0 hd hxd
  have a1' : ArrIn Ld st M0 M1 := by
    intro h; rw [e1.1, e1.2] at h ⊢; exact a1 h
  have a2 := ArrIn.trans a1' hs hx3
  rw [e2.1, e2.2] at hn ⊢; exact ⟨hx.mem_old (a2 hn).1, (a2 hn).2⟩

end FvModexp.Amd64.W4Pro
