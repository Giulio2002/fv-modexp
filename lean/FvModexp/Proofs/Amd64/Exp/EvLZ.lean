import FvModexp.Proofs.Amd64.Exp.EvJ2

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `z` after `z = z.set(z2)` and the frames of `makeslice` / `memmove` (asm s60; twin of infra's arm64 `EvLZ`)

* `ZOK`: `z`'s array after `set` is `z`'s own (entry) array or fresh relative to the entry live set (then also an `Ob`);
  `LZ` = a live nat in such an array. `ZOK.ap`: held, apart from the window, the stack header and the stack's free
  part — so it survives every callee step (`LZ.step`, the `stepC` frame form) and every frame that writes only the
  runtime, the window and an apart range (`LZ.frm`; `LN.frm` for the local nats).
* `J9` (`mvJ`, after `set`): `J8`'s locals and `z = (pZ, lw, cZ)` of `z2`'s value in the slots `0x108/0xa0/0xa8`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- an array held and apart from the stack's CURRENT array (the result `ResSep` needs this form: a fresh `z` is
never inside the stack's used part) -/
@[reducible] def ObZ (R : RtInv) (L1 : List (Nat × Nat)) (st : Nat) (M : Memory) (t k : Nat) : Prop :=
  Held R L1 t (8 * k) ∧ Apart t (8 * k) (stW M st) (8 * stCap M st)

theorem ObZ.toOb {R : RtInv} {L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : ObZ R L1 st M t k) :
    Ob R L1 st M t k := ⟨h.1, Or.inr h.2⟩

/-- `ObZ` through a step where the array is kept or fresh relative to `L1` -/
theorem ObZ.mono {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : ObZ R L1 st M t k) (hx : LiveExt R L1 L2) (_hl : stLen M st ≤ stLen M' st)
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1)) :
    ObZ R L2 st M' t k := by
  refine ⟨hx.held h.1, ?_⟩
  rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]; exact h.2
  · exact (hfresh h.1 hap hin).symm

theorem ObZ.back {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : ObZ R L1 st M t k) (hx : LiveExt R L1 L2) (hsb : StackBack R L1 L2 st M M') : ObZ R L2 st M' t k :=
  h.mono hx (by rw [hsb.2.1]; exact Nat.le_refl _) hsb.2.2

theorem ObZ.out {R : RtInv} {L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : ObZ R L1 st M t k)
    (hlc : stLen M st ≤ stCap M st) (hst : Apart t (8 * k) st 24) : Outside t (8 * k) (stkWs M st) :=
  h.toOb.out hlc hst

/-- `ob_fresh` in the `ObZ` form -/
theorem ob_freshZ {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {p c : Nat}
    (hok : StkOK M R L1 st) (hc0 : stCap M st = 0 → stW M st = 0) (hin : InRanges p (8 * c) R.rt)
    (hap : ApartAll p (8 * c) L1) (hh : Held R L2 p (8 * c)) (hrs : ResSep M M' st p c) (hc : 0 < c) :
    ObZ R L2 st M' p c := by
  refine ⟨hh, ?_⟩
  by_cases e : stW M' st = stW M st ∧ stCap M' st = stCap M st
  · rw [e.1, e.2]
    rcases Nat.eq_zero_or_pos (stCap M st) with c0 | c0
    · rw [c0, hc0 c0]; unfold Apart; omega
    · exact hfresh (hok.2.2.2.2.1 c0).2.1 hap hin |>.symm |> fun h => h.symm
  · exact hrs hc e

/-- `z`'s array after `set`: the entry array, or fresh relative to the entry live set `L` -/
@[reducible] def ZOK (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p c : Nat) : Prop :=
  (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L ∧ ObZ R L1 st M p c)

/-- a live nat `p[0:l]` (cap `c`, value `v`) in a `ZOK` array -/
@[reducible] def LZ (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p l c v : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L1 p c ∧ (0 < c → ZOK R L st zp zc M L1 p c) ∧ l ≤ c ∧ natVal M p l = v ∧
    NatNorm M p l

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the facts of a `ZOK` array at a `WC` point -/
theorem ZOK.ap (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p c : Nat} (hc : 0 < c)
    (hz : ZOK R L st zp zc M L1 p c) :
    Held R L1 p (8 * c) ∧ Apart p (8 * c) (sp - 8 - K) (K + 0x1c0) ∧ Apart p (8 * c) st 24 ∧
      Outside p (8 * c) (stkWs M st) := by
  have hlc := h.sok.2.2.2.2.2.1
  rcases hz with ⟨rfl, rfl⟩ | ⟨hin, hap, hob⟩
  · obtain ⟨o1, o2, o3, o4⟩ := (hP.zF hc).1
    have hf := free_apart h o1 o4
    refine ⟨h.le.held o1, o2, o3, ?_⟩
    simp only [free, Apart] at hf o3
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega
  · have hst : Apart p (8 * c) st 24 := hfresh hP.stk0.2.1 hap hin
    exact ⟨hob.1, (hin.apart hP.win_rt).symm, hst, hob.out hlc hst⟩

end

/-- `LZ` through a step keeping its bytes -/
theorem LZ.keep {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {p l c v : Nat} (h : LZ R L st zp zc M L1 p l c v) (hx : LiveExt R L1 L2)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hb : 0 < c → ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k)
    (hz : 0 < c → ZOK R L st zp zc M' L2 p c) : LZ R L st zp zc M' L2 p l c v := by
  obtain ⟨c40, hlv, -, hlc, hv, hn⟩ := h
  refine ⟨c40, fun hc => ?_, hz, hlc, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hlv hc
    exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩
  · rcases Nat.eq_zero_or_pos c with c0 | c0
    · have : l = 0 := by omega
      subst this
      rw [← hv]; exact Janus.Arm64.Memory.readLE_congr fun i hi => absurd hi (by omega)
    · rw [← hv]; exact hb c0 _ _ (Nat.le_refl _) (by omega)
  · rcases hn with h0 | hne
    · exact Or.inl h0
    · rcases Nat.eq_zero_or_pos c with c0 | c0
      · exact Or.inl (by omega)
      · right; rw [hb c0 _ _ (by omega) (by omega)]; exact hne

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `LZ` through a callee step (the `stepC` frame form, callee at `RSP = sp - 8`), apart from the destination -/
theorem LZ.step (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0xb8) {M' : Memory} {L2 : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) (hx : LiveExt R L1 L2)
    (hsb : StackBackL R L1 L2 st M M') {p l c v : Nat} (hq : LZ R L st zp zc M L1 p l c v)
    (hqd : 0 < c → Apart p (8 * c) pd (8 * cd)) : LZ R L st zp zc M' L2 p l c v := by
  have hK := hP.kf
  refine hq.keep hx hF.accessible (fun c0 a k h1 h2 => ?_) (fun c0 => ?_)
  · obtain ⟨w0, w1, -, hout⟩ := ZOK.ap hP h c0 (hq.2.2.1 c0)
    unfold Apart at w1
    simp only [stkWs, outside_cons, outside_nil, and_true] at hout
    refine keepH (cw := [(sp - 8 - stk, sp - 8 + above)]) hF hLF (w0.sub h1 h2) ?_ ?_ ?_
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]
      have := hqd c0; unfold Apart at this; omega
    · simp only [stkWs, outside_cons, outside_nil, and_true]; omega
  · rcases hq.2.2.1 c0 with e | ⟨hin, hap, hob⟩
    · exact Or.inl e
    · exact Or.inr ⟨hin, hap, hob.back hx hsb.1⟩

/-- the stack header unchanged -/
@[reducible] def HdrEq (st : Nat) (M M' : Memory) : Prop :=
  stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st

/-- `LN` through a frame keeping every held range apart from the window and from `[d, d + n)` (stack header
unchanged) -/
theorem LN.frm (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} (hx : LiveExt R L1 L2) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hhd : HdrEq st M M') {d n : Nat}
    (hrd : ∀ a k, Held R L1 a k → Apart a k (sp - 8 - K) (K + 0x1c0) → Apart a k d n → M'.readLE a k = M.readLE a k)
    {q l c v : Nat} (hq : LN R L s.mem st M L1 q l c v) (hqd : 0 < c → Apart q (8 * c) d n) :
    LN R L s.mem st M' L2 q l c v := by
  refine hq.keep hx hacc (fun c0 a k h1 h2 => ?_)
    (fun c0 => ((hq.1.2.2 c0).2).mono hx (by rw [hhd.2.1]; exact Nat.le_refl _) (Or.inl ⟨hhd.1, hhd.2.2⟩))
  obtain ⟨w1, -, -, -⟩ := Loc.ap hP (hq.1.2.2 c0).1
  refine hrd a k ((hq.1.2.2 c0).2.1.sub h1 h2) ?_ ?_
  · unfold Apart at w1 ⊢; omega
  · have := hqd c0; unfold Apart at this ⊢; omega

/-- `LZ` through such a frame -/
theorem LZ.frm (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hx : LiveExt R L1 L2)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hhd : HdrEq st M M') {d n : Nat}
    (hrd : ∀ a k, Held R L1 a k → Apart a k (sp - 8 - K) (K + 0x1c0) → Apart a k d n → M'.readLE a k = M.readLE a k)
    {p l c v : Nat} (hq : LZ R L st zp zc M L1 p l c v) (hqd : 0 < c → Apart p (8 * c) d n) :
    LZ R L st zp zc M' L2 p l c v := by
  refine hq.keep hx hacc (fun c0 a k h1 h2 => ?_) (fun c0 => ?_)
  · obtain ⟨w0, w1, -, -⟩ := ZOK.ap hP h c0 (hq.2.2.1 c0)
    refine hrd a k (w0.sub h1 h2) ?_ ?_
    · unfold Apart at w1 ⊢; omega
    · have := hqd c0; unfold Apart at this ⊢; omega
  · rcases hq.2.2.1 c0 with e | ⟨hin, hap, hob⟩
    · exact Or.inl e
    · exact Or.inr ⟨hin, hap, hob.mono hx (by rw [hhd.2.1]; exact Nat.le_refl _) (Or.inl ⟨hhd.1, hhd.2.2⟩)⟩

end

/-- the join point `mvJ` (after `z = z.set(z2)`; `RAX`, `RCX`, `RSI` = `z2`'s pointer, capacity, length): `J8`'s
locals, `z2` in the slots `0xf8/0x80/0x88`, `z = (pZ, lw, cZ)` of `z2`'s value in the slots `0x108/0xa0/0xa8`, apart from
every local array -/
structure J9 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 mvJ
  r0 : S.regs 0 = BitVec.ofNat 64 pw
  r1 : S.regs 1 = BitVec.ofNat 64 cw
  r6 : S.regs 6 = BitVec.ofNat 64 lw
  s118 : S.mem.readLE (sp + 0x118) 8 = p1
  sc8 : S.mem.readLE (sp + 0xc8) 8 = l1
  sd0 : S.mem.readLE (sp + 0xd0) 8 = c1
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  s100 : S.mem.readLE (sp + 0x100) 8 = pz
  s90 : S.mem.readLE (sp + 0x90) 8 = lz
  s98 : S.mem.readLE (sp + 0x98) 8 = cz
  sf8 : S.mem.readLE (sp + 0xf8) 8 = pw
  s80 : S.mem.readLE (sp + 0x80) 8 = lw
  s88 : S.mem.readLE (sp + 0x88) 8 = cw
  s108 : S.mem.readLE (sp + 0x108) 8 = pZ
  sa0 : S.mem.readLE (sp + 0xa0) 8 = lw
  sa8 : S.mem.readLE (sp + 0xa8) 8 = cZ
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  pz64 : pz < 2 ^ 64
  z1e : EL R L pz cz
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  z2 : LN R L s.mem st S.mem L1 pw lw cw
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pw64 : pw < 2 ^ 64
  z2e : EL R L pw cw
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)
  zs : LZ R L st zp zc S.mem L1 pZ lw cZ
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  Za1 : 0 < cZ → Apart pZ (8 * cZ) p1 (8 * c1)
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz1 : 0 < cZ → 0 < cz → Apart pZ (8 * cZ) pz (8 * cz)
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)

end FvModexp.Amd64.ExpEven
