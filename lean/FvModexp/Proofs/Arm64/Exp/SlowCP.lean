import FvModexp.Proofs.Arm64.Exp.SlowLN
import FvModexp.Proofs.Arm64.Exp.SlowG
import FvModexp.Proofs.Arm64.Exp.SlowStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the callee-entry preconditions of the loop's `sqr` / `mul` / `div` (agent expmc)

At a callee entry `S'` (`SP = sp`, window `[sp - stk, sp + above)` inside ours, `above ≤ 120`), from the entry facts
`EPre`, the context `WC` and the buffer facts (`DL` destinations, `LN` operands, `Pw` apartness):
* `sqrPreG`: `SqrPreG ∧ CapIn0 ∧ SqrXG` for `zz.sqr(stk, z)` (premise `SqrHypG`);
* `mulPreS`: `MulPreG ∧ CapIn0 ∧ CapIn0 ∧ MulXG` for `zz.mul(stk, z, x)` (premise `MulHypG`; `x`'s capacity and
  `gA` facts from `SlowX`);
* `divPreG`: `DivPreG` for `zz.div(stk, r, z, m)` (premise `DivHypLG`).
Shared: `stkXS` (divmc's `StkX`), `DL.wr`, `LN.rd0`, `inRd` (an input as `RdIn`), `DL.op` / `inOp` (`StkApart`, `OpX`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpEven (CapIn0 MulPreG MulXG)
open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut)

theorem apart_shrinkR {a k b n n' : Nat} (h : Apart a k b n) (hn : n' ≤ n) : Apart a k b n' := by
  unfold Apart at h ⊢; omega

theorem apart_shrinkL {a k b n k' : Nat} (h : Apart a k b n) (hk : k' ≤ k) : Apart a k' b n := by
  unfold Apart at h ⊢; omega

theorem out_zero (xs : List (Nat × Nat)) : Outside 0 0 xs := by
  induction xs with
  | nil => exact trivial
  | cons r rs ih => obtain ⟨lo, hi⟩ := r; exact ⟨Or.inl (Nat.zero_le _), ih⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- the stack's array is `0` when empty (entry fact, kept or fresh with `0 < cap`) -/
theorem WC.cap0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) : stCap M st = 0 → stW M st = 0 := by
  intro h0
  by_cases e : stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  · rw [e.1]; exact hP.cap0 (by rw [← e.2]; exact h0)
  · have := (h.ain e).2; omega

set_option maxRecDepth 20000 in
/-- the stack facts every callee wants -/
theorem stkF (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    st ≠ 0 ∧ Apart st 24 StackNat.wbA 4 ∧ Apart st 24 RunIface.gA 32 ∧ Apart st 24 (frP M st) (frN M st) ∧
      Apart (frP M st) (frN M st) RunIface.gA 32 ∧ (stCap M st = 0 → stW M st = 0) ∧
      Apart st 24 ((g + 16)) 8 ∧ M.accessible StackNat.wbA 4 false = true := by
  have hc0 := WC.cap0 hP h
  have hsF := free_apart h hP.stk0.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hogA, -, -, hstg, -, hwbacc, hstwb, -,
    hst0, -⟩ := hP
  have hgF := (free_apart h hogA.1 hogA.2.2.2).symm
  exact ⟨hst0, hstwb, hogA.2.2.1.symm, hsF, hgF, hc0, hstg, by rw [h.fr.accessible]; exact hwbacc⟩

set_option maxRecDepth 20000 in
/-- divmc's `StkX` at a callee entry `S'` (`SP = sp`, window `[sp - stk, sp + above)` inside ours) -/
theorem stkXS (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {S' : State} (hsN : S'.sp.toNat = sp) (hgN : (S'.regs 28).toNat = g) (fm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 120) : StkX R L1 S' stk above st := by
  obtain ⟨x1, x2, x3, x4, x5, x6, -⟩ := stkF hP hw
  have hsi := hw.stkIn hP hsN hgN fm hstk habove
  have hok := hw.sok
  subst fm
  refine ⟨x1, x2, ?_, ?_, ?_, x4, x3, x5⟩
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with c0 | c0
    · have hl0 : stLen S'.mem st = 0 := by have := hok.2.2.2.2.2.1; omega
      simp only [frP, frN, c0, x6 c0, hl0, Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
      exact Or.inr (out_zero R.rt)
    · exact (hok.2.2.2.2.1 c0).2.1.sub (by simp only [frP]; omega)
        (by simp only [frP, frN]; have := hok.2.2.2.2.2.1; omega)
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with c0 | c0
    · have hl0 : stLen S'.mem st = 0 := by have := hok.2.2.2.2.2.1; omega
      simp only [frP, frN, c0, x6 c0, hl0, Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
      exact out_zero _
    · exact (hsi.2.2.2 c0).1.of_sub (by simp only [frP]; omega)
        (by simp only [frP, frN]; have := hok.2.2.2.2.2.1; omega)
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with c0 | c0
    · have hl0 : stLen S'.mem st = 0 := by have := hok.2.2.2.2.2.1; omega
      simp only [frP, frN, c0, x6 c0, hl0, Nat.zero_sub, Nat.mul_zero]
      unfold Apart; omega
    · have := (hsi.2.2.2 c0).2
      have := hok.2.2.2.2.2.1
      simp only [frP, frN]; unfold Apart at *; omega

/-- a destination as a callee's output array at `SP = sp` -/
theorem DL.wr (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : DL R L st zp zc M L1 p c) {S : State} (hsp : S.sp.toNat = sp) (h28 : (S.regs 28).toNat = g)
    (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 120) :
    WrOut R L1 S stk above p c := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨c40, hlv, hloc, -⟩ := h
  subst hm
  refine ⟨c40, hlv, fun hc => ?_⟩
  obtain ⟨w1, -, w3, -⟩ := Loc.ap hP hloc hc
  unfold Apart at w1
  refine ⟨?_, by rw [h28]; exact w3⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- a destination of any capacity is outside a callee window inside ours -/
theorem DL.out (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : DL R L st zp zc M L1 p c) {S : State} (hsp : S.sp.toNat = sp) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 120) : Outside p (8 * c) (win S stk above) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have := Loc.win hP h.2.2.1
  unfold Apart at this
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- a live local as a callee input (empty-tolerant) at `SP = sp` -/
theorem LN.rd0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p l c v : Nat}
    (h : LN R L st zp zc M L1 p l c v) {S : State} (hsp : S.sp.toNat = sp) (hm : S.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 120) : RdIn0 R L1 S stk above p l := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨c40, hlv, hloc, -⟩, hlc, -, -⟩ := h
  refine ⟨by omega, fun hl => ?_⟩
  obtain ⟨-, a2, a3, a4⟩ := hlv (by omega)
  obtain ⟨w1, -⟩ := Loc.ap hP hloc (by omega)
  unfold Apart at w1
  subst hm
  refine ⟨by omega, Memory.accessible_weaken _ (Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega)), by omega,
    a2.sub (by omega) (by omega), ?_⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- a live local's `CapIn0` -/
theorem LN.capIn0 {p l c v : Nat} (h : LN R L st zp zc M L1 p l c v) : CapIn0 R L1 p l c :=
  ⟨h.2.1, h.1.1, fun h0 => ⟨(h.1.2.1 h0).2.1, (h.1.2.1 h0).2.2.2⟩⟩

/-- a non-empty destination's `StkApart` and `OpX` (any prefix `k' ≤ 8 c`) -/
theorem DL.op (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : DL R L st zp zc M L1 p c) {k' : Nat} (hk : k' ≤ 8 * c) : StkApart M st p k' ∧ OpX M st p k' := by
  rcases Nat.eq_zero_or_pos k' with e | e
  · subst e; exact ⟨fun h0 => absurd h0 (Nat.lt_irrefl 0), fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
  · have hc : 0 < c := by omega
    obtain ⟨-, w2, -, w4, -⟩ := Loc.ap hP h.2.2.1 hc
    have hfr := (h.2.2.2.1 hc).free
    refine ⟨fun _ => ⟨apart_shrinkL w2 hk, fun _ => apart_shrinkL hfr hk⟩, fun _ => ⟨?_, apart_shrinkL w4 hk⟩⟩
    simp only [frP, frN]; exact apart_shrinkL hfr hk

/-- an entry object (`OE`) read at a callee entry `S'` (`SP = sp`) -/
theorem inRd (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p n : Nat} (hoe : OE R L sp K st s.mem p (8 * n))
    (hacc : s.mem.accessible p (8 * n) false = true) (h48 : p + 8 * n ≤ 2 ^ 48) (hn : n < 2 ^ 40)
    {S : State} (hsp : S.sp.toNat = sp) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 120) :
    RdIn R L1 S stk above p n := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨hH, hw, -, -⟩ := hoe
  unfold Apart at hw
  subst hm
  refine ⟨hn, by rw [h.fr.accessible]; exact hacc, h48, h.le.held hH, ?_⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- an entry object's `StkApart` and free-part apartness at `M` -/
theorem inOp (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p k : Nat} (hoe : OE R L sp K st s.mem p k) :
    StkApart M st p k ∧ Apart p k (frP M st) (frN M st) := by
  have hfr := free_apart h hoe.1 hoe.2.2.2
  exact ⟨fun _ => ⟨hoe.2.2.1, fun _ => hfr⟩, hfr⟩


/-- an entry object's bytes (any sub-range) at `M` -/
theorem inSub (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p k : Nat} (hoe : OE R L sp K st s.mem p k)
    (hza : 0 < zc → Apart zp (8 * zc) p k) :
    ∀ a n, p ≤ a → a + n ≤ p + k → M.readLE a n = s.mem.readLE a n := by
  intro a n h1 h2
  have hb := oe_bytes hP hoe hza
  refine h.readB (hoe.1.imp (fun h => h.sub h1 h2) (fun h => h.of_sub h1 h2)) fun i hi => ?_
  have := hb (a - p + i) (by omega)
  rwa [show p + (a - p + i) = a + i by omega] at this

/-- an entry object's value and normalisation at `M` -/
theorem inVal (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p n : Nat} (hoe : OE R L sp K st s.mem p (8 * n))
    (hza : 0 < zc → Apart zp (8 * zc) p (8 * n)) (hn : NatNorm s.mem p n) :
    natVal M p n = natVal s.mem p n ∧ NatNorm M p n := by
  have hs := inSub hP h hoe hza
  refine ⟨hs p (8 * n) (Nat.le_refl _) (Nat.le_refl _), ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exact Or.inl h0
  · rcases hn with h1 | hne
    · exact Or.inl h1
    · right; rw [hs _ _ (by omega) (by omega)]; exact hne

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.sqr`'s precondition** (`SqrHypG` form) at the callee entry `S'` (`SP = sp`): `zz.sqr(stk, z)` -/
theorem sqrPreG (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 120)
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {pd ld cd px lx cx vx : Nat} (hd : DL R L st zp zc M L1 pd cd) (hld : ld ≤ cd)
    (hx : LN R L st zp zc M L1 px lx cx vx) (hdx : Pw px cx pd cd)
    (hlx : lx ≤ 2 ^ 12) (hs16 : ℓ + 4 * (2 * lx) + 64 ≤ 2 ^ 16) {c : Nat} (hb : c ≤ b1) :
    SqrPreG R b1 c L1 stk above pd ld cd st px lx S' ∧ CapIn0 R L1 px lx cx ∧
      SqrXG R L1 S' stk above st pd cd px lx cx := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := stk) (above := above) hstk habove
  have hgl := hw.globals hP (w := win S' stk above) (fun a n ho => by
    simp only [win, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hwr := DL.wr hP hd hsN hgN fm hstk habove
  have hrx := LN.rd0 hP hx hsN fm hstk habove
  have hsi := hw.stkIn hP hsN hgN fm hstk habove
  have hsx := stkXS hP hw hsN hgN fm hstk habove
  obtain ⟨od1, od2⟩ := DL.op hP hd (Nat.le_refl (8 * cd))
  obtain ⟨ox1, ox2⟩ := DL.op hP hx.1 (Nat.mul_le_mul_left 8 hx.2.1)
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hdw := DL.out hP hd hsN hstk habove
  have hax : pd = px ∨ (0 < cd → 0 < lx → Apart pd (8 * cd) px (8 * lx)) :=
    Or.inr fun hc hl => apart_shrinkR (hdx (by have := hx.2.1; omega) hc).symm (Nat.mul_le_mul_left 8 hx.2.1)
  have hex : pd = px → 0 < cd → 0 < lx → cd = cx := fun e hc hl => by
    have := hdx (by have := hx.2.1; omega) hc; rw [e] at this; unfold Apart at this; omega
  subst fm
  exact ⟨⟨hce, hsv, hgl, hld, hwr, hrx, hlx, hax, hsi, by rw [hlen]; exact hs16, od1, ox1, hb,
    by rw [hgN]; exact hw.inv⟩, hx.capIn0, ⟨hsx, hdw, hex, od2, ox2⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.mul`'s precondition** (`MulHypG` form) at the callee entry `S'`: `zz.mul(stk, z, x)` with the INPUT `x`
(capacity and `gA` facts: `SlowX`) -/
theorem mulPreS (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hX : SlowX R L xp xl xc) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 120)
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {pd ld cd pz lz cz vz : Nat} (hd : DL R L st zp zc M L1 pd cd) (hld : ld ≤ cd)
    (hz : LN R L st zp zc M L1 pz lz cz vz) (hdz : Pw pz cz pd cd)
    (hlz : lz ≤ 2 ^ 12) (hs16 : ℓ + 4 * (lz + xl) + 64 ≤ 2 ^ 16) {c : Nat} (hb : c ≤ b1) :
    MulPreG R b1 c L1 stk above pd ld cd st pz lz xp xl S' ∧ CapIn0 R L1 pz lz cz ∧ CapIn0 R L1 xp xl xc ∧
      MulXG R L1 S' stk above st pd cd pz lz cz xp xl xc := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hox := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxa := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx48 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := stk) (above := above) hstk habove
  have hgl := hw.globals hP (w := win S' stk above) (fun a n ho => by
    simp only [win, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hwr := DL.wr hP hd hsN hgN fm hstk habove
  have hrz := LN.rd0 hP hz hsN fm hstk habove
  have hrx := inRd hP hw hox hxa hx48 (by omega) hsN fm hstk habove
  have hsi := hw.stkIn hP hsN hgN fm hstk habove
  have hsx := stkXS hP hw hsN hgN fm hstk habove
  obtain ⟨od1, od2⟩ := DL.op hP hd (Nat.le_refl (8 * cd))
  obtain ⟨oz1, oz2⟩ := DL.op hP hz.1 (Nat.mul_le_mul_left 8 hz.2.1)
  obtain ⟨ox1, ox2⟩ := inOp hw hox
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hdw := DL.out hP hd hsN hstk habove
  have hdxa : 0 < cd → Apart pd (8 * cd) xp (8 * xl) := fun hc => (Loc.ap hP hd.2.2.1 hc).2.2.2.2.1
  have haz : pd = pz ∨ (0 < cd → 0 < lz → Apart pd (8 * cd) pz (8 * lz)) :=
    Or.inr fun hc hl => apart_shrinkR (hdz (by have := hz.2.1; omega) hc).symm (Nat.mul_le_mul_left 8 hz.2.1)
  have hax : pd = xp ∨ (0 < cd → 0 < xl → Apart pd (8 * cd) xp (8 * xl)) := Or.inr fun hc _ => hdxa hc
  have hez : pd = pz → 0 < cd → 0 < lz → cd = cz := fun e hc hl => by
    have := hdz (by have := hz.2.1; omega) hc; rw [e] at this; unfold Apart at this; omega
  have hex : pd = xp → 0 < cd → 0 < xl → cd = xc := fun e hc hl => by
    have := hdxa hc; rw [e] at this; unfold Apart at this; omega
  obtain ⟨⟨c1, c2, c3⟩, hxg⟩ := hX
  have hcx : CapIn0 R L1 xp xl xc := ⟨c1, c2, fun h0 => ⟨hw.le.held (c3 h0).1, (c3 h0).2⟩⟩
  subst fm
  exact ⟨⟨hce, hsv, hgl, hld, hwr, hrz, hrx.toRdIn0, hlz, by omega, haz, hax, hsi, by rw [hlen]; exact hs16, od1, oz1,
    ox1, hb, by rw [hgN]; exact hw.inv⟩, hz.capIn0, hcx,
    ⟨hsx, hdw, hez, hex, od2, oz2, fun h0 => ⟨ox2, hxg (by omega)⟩⟩⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.div`'s precondition** (`DivHypLG` form) at the callee entry `S'`: `zz.div(stk, r, z, m)` (quotient into the
`zz` buffer `(pq, cq)`, remainder into the `r` buffer `(pr, cr)`, dividend the live local `z`, divisor the input `m`) -/
theorem divPreG (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 120)
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {pq lq cq pr lr cr pu lu cu vu : Nat} (hq : DL R L st zp zc M L1 pq cq) (hlq : lq ≤ cq)
    (hr : DL R L st zp zc M L1 pr cr) (hlr : lr ≤ cr) (hqr : Pw pq cq pr cr)
    (hu : LN R L st zp zc M L1 pu lu cu vu) (hqu : Pw pu cu pq cq) (hru : Pw pu cu pr cr)
    (hlu : lu ≤ 2 ^ 9) (hs16 : ℓ + 16 * lu + 64 ≤ 2 ^ 16) {dvC : Nat → Nat → Nat → Nat} (hb : dvC ℓ lu ml ≤ b1) :
    DivPreG R b1 dvC L1 stk above pq lq cq st pr lr cr pu lu mp ml S' := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hml0 := hP.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  obtain ⟨hom, hma, hm48, hmn, hzm, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := stk) (above := above) hstk habove
  have hgl := hw.globals hP (w := win S' stk above) (fun a n ho => by
    simp only [win, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hwq := DL.wr hP hq hsN hgN fm hstk habove
  have hwr := DL.wr hP hr hsN hgN fm hstk habove
  have hru0 := LN.rd0 hP hu hsN fm hstk habove
  have hrm := inRd hP hw hom hma hm48 (by omega) hsN fm hstk habove
  have hsi := hw.stkIn hP hsN hgN fm hstk habove
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, -⟩ := stkF hP hw
  obtain ⟨-, om2⟩ := inOp hw hom
  have hmN := (inVal hP hw hom hzm hmn).2
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hua : 0 < lu → Apart pu (8 * lu) st 24 ∧ Apart pu (8 * lu) (frP M st) (frN M st) := fun hl => by
    have hc : 0 < cu := by have := hu.2.1; omega
    refine ⟨apart_shrinkL (Loc.ap hP hu.1.2.2.1 hc).2.1 (Nat.mul_le_mul_left 8 hu.2.1), ?_⟩
    exact apart_shrinkL (hu.1.2.2.2.1 hc).free (Nat.mul_le_mul_left 8 hu.2.1)
  have hdst : ∀ p c, (p, c) ∈ [(pq, cq), (pr, cr)] → 0 < c →
      (0 < lu → Apart p (8 * c) pu (8 * lu)) ∧ Apart p (8 * c) mp (8 * ml) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (frP M st) (frN M st) := by
    intro p c hm hc
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    have key : ∀ (hd : DL R L st zp zc M L1 p c) (hpw : Pw pu cu p c),
        (0 < lu → Apart p (8 * c) pu (8 * lu)) ∧ Apart p (8 * c) mp (8 * ml) ∧ Apart p (8 * c) st 24 ∧
          Apart p (8 * c) (frP M st) (frN M st) := fun hd hpw => by
      obtain ⟨-, a2, -, -, -, -, a7⟩ := Loc.ap hP hd.2.2.1 hc
      refine ⟨fun hl => apart_shrinkR (hpw (by have := hu.2.1; omega) hc).symm (Nat.mul_le_mul_left 8 hu.2.1), a7, a2,
        (hd.2.2.2.1 hc).free⟩
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key hq hqu
    · exact key hr hru
  subst fm
  refine ⟨hce, hsv, hgl, hlq, hlr, hwq, hwr, hru0, hrm, hlu, hml0, by omega, hu.2.2.2, hmN, hw.sok, hsi.2.1,
    hsi.2.2.2, by rw [hlen]; exact hs16, x6, hua, hom.2.2.1, om2, x1, ⟨by rw [hgN]; exact x7, x2, x4⟩,
    fun hc => (Loc.ap hP hq.2.2.1 hc).2.2.2.1, fun hc => (Loc.ap hP hr.2.2.1 hc).2.2.2.1, x3, x5, hqr, hdst,
    by rw [hlen]; exact hb, by rw [hgN]; exact hw.inv⟩

end

end FvModexp.Arm64.ExpSlow
