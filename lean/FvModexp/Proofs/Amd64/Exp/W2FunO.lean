import FvModexp.Proofs.Amd64.Exp.W2FunB
import FvModexp.Proofs.Amd64.Exp.W2En

set_option autoImplicit false

/-!
# window-2 (amd64): the written ranges of each segment of the post chain, as `Outside` facts (agent expmc s58;
twin of `Arm64.W2Pro` `W2FunO`)

For a range `(a, k)` outside window-2's frame window `[sp - 8 - K, sp + 0x2e0)` (`Zw`), the stack header, the entry
free part, `z`, and apart from the buffers a segment writes, the segment's write lists miss it. The chain:
`S0` entry (`EnPost`) · `S1` prologue up to the division's return (`Anc.frame`) · `S2` `RR` (`RRPost`) · `S3`
`stk.nat(5n)` (`OneChain`) · `S4` table (`FP`) · `S5`/`S6` `z`/`zz` make (`ZPost`) · `S7` `z` clear (`ZjPost`) ·
`S8` loop (`FL`) · `S9` join (`JoinPost`) · `S10` epilogue (`FinPost`). Small separate lemmas: `omega` runs in a
tiny context.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

/-- outside window-2's frame window -/
@[reducible] def Zw (sp K a k : Nat) : Prop := a + k ≤ sp - 8 - K ∨ sp + 0x2e0 ≤ a

theorem out_S0 {sp K st a k : Nat} (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a) :
    Outside a k [(sp - 8 - K, sp + 0x2e0), (st, st + 24)] ∧ Outside a k [(st, st + 24)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem out_S1 {sp K st a k : Nat} {M : Memory} (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hf : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) :
    Outside a k ([(sp - 8 - K, sp + 0x2a8)] ++ stkWs M st) ∧ Outside a k (stkWs M st) := by
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
    Outside a k (W2Loop.fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]) ∧
      Outside a k [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)] := by
  simp only [W2Loop.fw, outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S9 {sp K zzp zzc a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    Outside a k ([(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x190, sp + 0x198)] ++
      [(zzp, zzp + 8 * zzc)]) ∧ Outside a k [(zzp, zzp + 8 * zzc)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; omega

theorem out_S10 {sp K st a k : Nat} (hw : Zw sp K a k) (hK : 4296 ≤ K) (hd : a + k ≤ st ∨ st + 24 ≤ a) :
    Outside a k [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x178, sp + 0x190), (st + 8, st + 16)] := by
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

/-- `ArrIn` along the window's chain: reserve, prologue (`Anc`), header-keeping steps, the `stk.nat(5n)` step -/
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

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

/-- the segment chain from the entry memory `M0` to the return memory `Me`: a held range outside window-2's frame
window, the stack header, the entry free part and every buffer written on the way reads the same at the loop anchor
`M0z` and at the return -/
theorem chainA {R : RtInv} {L L1 Ld L2 L3 L4 : List (Nat × Nat)} {sp K st n zzp zzc bp bc zp1 zc1 zp' zc' zzp' zzc' : Nat}
    {M0 M Md M1 M2 Mj Ma Mb M0z M' Mj2 Me : Memory} (hK : 4296 ≤ K)
    (hF0 : MemFrame M0 M (R.rt ++ [(sp - 8 - K, sp + 0x2e0), (st, st + 24)]))
    (hLF0 : LiveFrame M0 M L [(st, st + 24)]) (hx1 : LiveExt R L L1)
    (hF1 : MemFrame M Md (R.rt ++ [(sp - 8 - K, sp + 0x2a8)] ++ stkWs M st)) (hLF1 : LiveFrame M Md L1 (stkWs M st))
    (hxd : LiveExt R L Ld)
    (hF2 : MemFrame Md M1 (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)])) (hLF2 : LiveFrame Md M1 Ld [(zzp, zzp + 8 * n)])
    (hF3 : MemFrame M1 M2 (R.rt ++ (ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M1 st)))
    (hLF3 : LiveFrame M1 M2 Ld (stkWs M1 st)) (hx2 : LiveExt R L L2)
    (hF4 : MemFrame M2 Mj (pl R sp bp bc)) (hLF4 : LiveFrame M2 Mj L2 [(bp, bp + 8 * bc)])
    (hF5 : MemFrame Mj Ma (R.rt ++ zw1 sp)) (hLF5 : LiveFrame Mj Ma L2 []) (hx3 : LiveExt R L L3)
    (hF6 : MemFrame Ma Mb (R.rt ++ zw2 sp)) (hLF6 : LiveFrame Ma Mb L3 []) (hx4 : LiveExt R L L4)
    (hF7 : MemFrame Mb M0z (R.rt ++ cw sp ++ [(zp1, zp1 + 8 * n)])) (hLF7 : LiveFrame Mb M0z L4 [(zp1, zp1 + 8 * n)])
    (hF8 : MemFrame M0z M' (W2Loop.lw R sp zp' zc' zzp' zzc'))
    (hLF8 : LiveFrame M0z M' L4 [(zp', zp' + 8 * zc'), (zzp', zzp' + 8 * zzc')])
    (hF9 : MemFrame M' Mj2 (W2Loop.jw R sp zzp' zzc')) (hLF9 : LiveFrame M' Mj2 L4 [(zzp', zzp' + 8 * zzc')])
    (hF10 : MemFrame Mj2 Me [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x178, sp + 0x190), (st + 8, st + 16)])
    {a k : Nat} (hh : Outside a k R.rt ∨ InRanges a k L) (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hM : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a)
    (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) (hnz : n ≤ zzc)
    (hM1 : a + k ≤ stW M1 st + 8 * stLen M1 st ∨ stW M1 st + 8 * stCap M1 st ≤ a)
    (hbp : a + k ≤ bp ∨ bp + 8 * bc ≤ a)
    (hz1 : a + k ≤ zp1 ∨ zp1 + 8 * zc1 ≤ a) (hnz1 : n ≤ zc1)
    (hz' : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a) (hzz' : a + k ≤ zzp' ∨ zzp' + 8 * zzc' ≤ a) :
    M0z.readLE a k = M0.readLE a k ∧ Me.readLE a k = M0.readLE a k := by
  simp only [List.append_assoc] at hF1 hF2 hF7
  simp only [pl, List.append_assoc] at hF4
  simp only [W2Loop.lw, W2Loop.jw, List.append_assoc] at hF8 hF9
  have e0 := rd_step hF0 hLF0 (LiveExt.refl R L) hh (out_S0 hw hd).1 (out_S0 hw hd).2
  have e1 := rd_step hF1 hLF1 hx1 hh (out_S1 hw hd hM).1 (out_S1 hw hd hM).2
  have e2 := rd_step hF2 hLF2 hxd hh (out_S2 hw hK hzz hnz).1 (out_S2 hw hK hzz hnz).2
  have e3 := rd_step hF3 hLF3 hxd hh (out_S3 hw hK hd hM1).1 (out_S3 hw hK hd hM1).2
  have e4 := rd_step hF4 hLF4 hx2 hh (out_S4 hw hK hbp).1 (out_S4 hw hK hbp).2
  have e5 := rd_step hF5 hLF5 hx2 hh (out_S5 hw hK) trivial
  have e6 := rd_step hF6 hLF6 hx3 hh (out_S6 hw hK) trivial
  have e7 := rd_step hF7 hLF7 hx4 hh (out_S7 hw hK hz1 hnz1).1 (out_S7 hw hK hz1 hnz1).2
  have e8 := rd_step hF8 hLF8 hx4 hh (out_S8 hw hK hz' hzz').1 (out_S8 hw hK hz' hzz').2
  have e9 := rd_step hF9 hLF9 hx4 hh (out_S9 hw hK hzz').1 (out_S9 hw hK hzz').2
  have e10 := hF10.readLE a k (out_S10 hw hK hd)
  have h7 : M0z.readLE a k = M0.readLE a k := by rw [e7, e6, e5, e4, e3, e2, e1, e0]
  exact ⟨h7, by rw [e10, e9, e8, h7]⟩

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

/-- the chain from the `stk.nat(5n)` return `M2` to the join `Mj2` (the stack header is written only by
`stk.nat(5n)` and the epilogue's restore) -/
theorem chainT {R : RtInv} {L L2 L3 L4 : List (Nat × Nat)} {sp K n bp bc zp1 zc1 zp' zc' zzp' zzc' : Nat}
    {M2 Mj Ma Mb M0z M' Mj2 : Memory} (hK : 4296 ≤ K) (hx2 : LiveExt R L L2)
    (hF4 : MemFrame M2 Mj (pl R sp bp bc)) (hLF4 : LiveFrame M2 Mj L2 [(bp, bp + 8 * bc)])
    (hF5 : MemFrame Mj Ma (R.rt ++ zw1 sp)) (hLF5 : LiveFrame Mj Ma L2 []) (hx3 : LiveExt R L L3)
    (hF6 : MemFrame Ma Mb (R.rt ++ zw2 sp)) (hLF6 : LiveFrame Ma Mb L3 []) (hx4 : LiveExt R L L4)
    (hF7 : MemFrame Mb M0z (R.rt ++ cw sp ++ [(zp1, zp1 + 8 * n)])) (hLF7 : LiveFrame Mb M0z L4 [(zp1, zp1 + 8 * n)])
    (hF8 : MemFrame M0z M' (W2Loop.lw R sp zp' zc' zzp' zzc'))
    (hLF8 : LiveFrame M0z M' L4 [(zp', zp' + 8 * zc'), (zzp', zzp' + 8 * zzc')])
    (hF9 : MemFrame M' Mj2 (W2Loop.jw R sp zzp' zzc')) (hLF9 : LiveFrame M' Mj2 L4 [(zzp', zzp' + 8 * zzc')])
    {a k : Nat} (hh : Outside a k R.rt ∨ InRanges a k L) (hw : Zw sp K a k)
    (hbp : a + k ≤ bp ∨ bp + 8 * bc ≤ a)
    (hz1 : a + k ≤ zp1 ∨ zp1 + 8 * zc1 ≤ a) (hnz1 : n ≤ zc1)
    (hz' : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a) (hzz' : a + k ≤ zzp' ∨ zzp' + 8 * zzc' ≤ a) :
    Mj2.readLE a k = M2.readLE a k := by
  simp only [List.append_assoc] at hF7
  simp only [pl, List.append_assoc] at hF4
  simp only [W2Loop.lw, W2Loop.jw, List.append_assoc] at hF8 hF9
  have e4 := rd_step hF4 hLF4 hx2 hh (out_S4 hw hK hbp).1 (out_S4 hw hK hbp).2
  have e5 := rd_step hF5 hLF5 hx2 hh (out_S5 hw hK) trivial
  have e6 := rd_step hF6 hLF6 hx3 hh (out_S6 hw hK) trivial
  have e7 := rd_step hF7 hLF7 hx4 hh (out_S7 hw hK hz1 hnz1).1 (out_S7 hw hK hz1 hnz1).2
  have e8 := rd_step hF8 hLF8 hx4 hh (out_S8 hw hK hz' hzz').1 (out_S8 hw hK hz' hzz').2
  have e9 := rd_step hF9 hLF9 hx4 hh (out_S9 hw hK hzz').1 (out_S9 hw hK hzz').2
  rw [e9, e8, e7, e6, e5, e4]

/-- the epilogue keeps the stack header's pointer and capacity words -/
theorem out10_hdr {sp K st : Nat} (hw : Zw sp K st 24) (hK : 4296 ≤ K) :
    Outside st 8 [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x178, sp + 0x190), (st + 8, st + 16)] ∧
      Outside (st + 16) 8 [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x178, sp + 0x190), (st + 8, st + 16)] := by
  simp only [Zw] at hw
  simp only [outside_cons, outside_nil, and_true]; omega

theorem hdr_fields {M M' : Memory} {st : Nat} (h : M'.readLE st 24 = M.readLE st 24) :
    stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st := by
  simp only [stW, stLen, stCap]
  exact ⟨readLE_sub_eq h (Nat.le_refl _) (by omega), readLE_sub_eq h (by omega) (by omega),
    readLE_sub_eq h (by omega) (by omega)⟩

end FvModexp.Amd64.W2Pro
