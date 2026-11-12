import FvModexp.Proofs.Arm64.Exp.EvSetT

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `z.set(z2)` before `setJ` — the facts after `z2`'s spills and the two ways to `JS`
(agent infra)

`JP` = `J8`'s locals + `z2` in the slots `256/136/144` (after `runS`'s stores; `j8_own`). `JP.reuseJS`: `len z2 ≤
cap z` → `z`'s entry array. `JP.mkJS`: a fresh `makeslice` array (`AllocR`) of capacity `c ≥ len z2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- `J8`'s locals after `z2`'s spills -/
structure JP (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s264 : S.mem.readLE (sp + 264) 8 = pz
  s152 : S.mem.readLE (sp + 152) 8 = lz
  s160 : S.mem.readLE (sp + 160) 8 = cz
  s256 : S.mem.readLE (sp + 256) 8 = pw
  s136 : S.mem.readLE (sp + 136) 8 = lw
  s144 : S.mem.readLE (sp + 144) 8 = cw
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  a2p : 0 < a2 ml (nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  pz64 : pz < 2 ^ 64
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  z2 : LN R L s.mem st S.mem L1 pw lw cw
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pw64 : pw < 2 ^ 64
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)
  lwm : lw ≤ ml

/-- the budget after an allocation (outside any large context) -/
theorem bud_alloc {rk b1 a rk' r : Nat} (h1 : rk ≤ b1) (h2 : a + rk' ≤ rk) (h3 : r ≤ a) : rk' ≤ b1 - r := by omega

/-- the return state of a one-result call -/
theorem rs1_regs {T : State} {junk : Nat → W64} {ptr : W64} {f : Flags} {v : Nat → BitVec 128} {m : Memory}
    {ex : Option (Nat × Nat)} {ep : Nat → Bool} :
    (retStateX T junk [ptr] f v m ex ep).sp = T.sp ∧ (retStateX T junk [ptr] f v m ex ep).regs 28 = T.regs 28 ∧
      (retStateX T junk [ptr] f v m ex ep).regs 29 = T.regs 29 ∧
      (retStateX T junk [ptr] f v m ex ep).regs 18 = T.regs 18 ∧
      (retStateX T junk [ptr] f v m ex ep).pc = T.regs 30 ∧ (retStateX T junk [ptr] f v m ex ep).mem = m ∧
      (retStateX T junk [ptr] f v m ex ep).regs 0 = BitVec.ofNat 64 ptr.toNat := by
  simp [retStateX, callRegs_apply]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- `J8` through `runS`'s spills of `z2` (`256/136/144`, and `128` on the `makeslice(l, l + 4)` path) -/
theorem j8_own (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : J8 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw)
    {S2 : State} {M2 : Memory} (hF : MemFrame S.mem M2 [(sp + 128, sp + 152), (sp + 256, sp + 264)])
    (hrg : M2.regions = S.mem.regions) (fm : S2.mem = M2) (fsp : S2.sp = S.sp) (f18 : S2.regs 18 = S.regs 18)
    (f28 : S2.regs 28 = S.regs 28) (f29 : S2.regs 29 = S.regs 29) (r256 : M2.readLE (sp + 256) 8 = pw)
    (r136 : M2.readLE (sp + 136) 8 = lw) (r144 : M2.readLE (sp + 144) 8 = cw) :
    JP R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S2 L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  have hlwm : lw ≤ ml := by
    have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
    have hlt : natVal s.mem mp ml < 2 ^ (64 * ml) := by
      have := Memory.readLE_lt s.mem mp (8 * ml)
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * ml) = 64 * ml by omega] at this
      exact this
    have hpos : 0 < natVal s.mem mp ml / 2 ^ nE s mp ml :=
      Nat.pos_of_ne_zero fun e => by rw [e] at hodd; exact absurd hodd (by decide)
    refine nlen_bd' h.z2.2.2.2 ?_
    rw [h.z2.2.2.1]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.le_trans (Nat.div_le_self _ _) (Nat.le_of_lt hlt))
  obtain ⟨hw2, hown⟩ := WC.own hP h.jx.wc hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a, (a + 8 ≤ sp + 128 ∨ sp + 152 ≤ a) → (a + 8 ≤ sp + 256 ∨ sp + 264 ≤ a) →
      M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 =>
    hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  subst fm
  exact ⟨⟨fsp.trans h.jx.esp, f28.trans h.jx.e28, f29.trans h.jx.e29, f18.trans h.jx.e18, hw2,
      h.jx.esl.keep (fun a k ha => hF.readLE a k (by
        simp only [SlotR] at ha; simp only [outside_cons, outside_nil, and_true]; omega)) (by omega), h.jx.bud⟩,
    (kF _ (by omega) (by omega)).trans h.s288, (kF _ (by omega) (by omega)).trans h.s208,
    (kF _ (by omega) (by omega)).trans h.s216, (kF _ (by omega) (by omega)).trans h.s280,
    (kF _ (by omega) (by omega)).trans h.s192, (kF _ (by omega) (by omega)).trans h.s200,
    (kF _ (by omega) (by omega)).trans h.s264, (kF _ (by omega) (by omega)).trans h.s152,
    (kF _ (by omega) (by omega)).trans h.s160, r256, r136, r144,
    hown _ _ _ _ h.m1, h.c1p, hown _ _ _ _ h.m2, ha2, h.ap, hown _ _ _ _ h.z1, h.pz64, h.za1, h.za2,
    hown _ _ _ _ h.z2, h.pw64, h.wa1, h.wa2, h.wz, hlwm⟩

/-- **reuse**: `len z2 ≤ cap z` → `JS` with `z`'s entry array -/
theorem JP.reuseJS (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {rk rk' : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : JP R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw)
    (hrk : rk' ≤ rk) (hpc : S.pc = BitVec.ofNat 64 setJ) (h0 : S.regs 0 = BitVec.ofNat 64 pw)
    (h1 : S.regs 1 = BitVec.ofNat 64 lw) (h2 : S.regs 2 = BitVec.ofNat 64 cw)
    (h3 : S.regs 3 = BitVec.ofNat 64 zc) (h4 : S.regs 4 = BitVec.ofNat 64 lw) (h5 : S.regs 5 = BitVec.ofNat 64 zp)
    (hlz : lw ≤ zc) :
    JS R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw zp zc := by
  have hw := h.jx.wc
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzp : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbud := h.jx.bud
  refine ⟨⟨h.jx.esp, h.jx.e28, h.jx.e29, h.jx.e18, hw, h.jx.esl, Nat.le_trans hrk hbud⟩, hpc, h0, h1, h2, h3, h4, h5,
    h.s288, h.s208, h.s216, h.s280, h.s192, h.s200, h.s264, h.s152, h.s160, h.s256, h.s136, h.s144, h.m1, h.c1p,
    h.m2, h.ap, h.z1, h.pz64, h.za1, h.za2, h.z2, h.pw64, h.wa1, h.wa2, h.wz,
    ⟨hzc, fun c0 => ?_, fun _ => Or.inl ⟨rfl, rfl⟩, hlz⟩, hzp,
    fun c0 => ((Loc.ap hP (h.m1.1.2.2 h.c1p).1).2.2.2 c0).symm,
    fun c0 => ((Loc.ap hP (h.m2.1.2.2 h.a2p).1).2.2.2 c0).symm,
    fun c0 cz0 => ((Loc.ap hP (h.z1.1.2.2 cz0).1).2.2.2 c0).symm,
    fun c0 cw0 => ((Loc.ap hP (h.z2.1.2.2 cw0).1).2.2.2 c0).symm, h.lwm⟩
  obtain ⟨oe, acc, b48, al, -⟩ := hz c0
  exact ⟨al, hw.le.held oe.1, by rw [hw.fr.accessible]; exact acc, b48⟩

set_option maxRecDepth 20000 in
/-- **fresh**: a `makeslice` array `[ptr, ptr + r)` of capacity `c ≥ len z2` → `JS` -/
theorem JP.mkJS (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {rk rk' : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : JP R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw)
    {m : Memory} {ptr r c : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem S.mem L1 b1 (ℓ4 s st mp ml l1 l2) m ptr r (8 * c))
    (hc : lw ≤ c) (hc40 : c < 2 ^ 40) (hc0 : 0 < c) (hptr : ptr < 2 ^ 64) (hbud : rk' ≤ b1 - r)
    (S' : State) (esp : S'.sp = S.sp) (e28 : S'.regs 28 = S.regs 28) (e29 : S'.regs 29 = S.regs 29)
    (e18 : S'.regs 18 = S.regs 18) (hm : S'.mem = m) (hpc : S'.pc = BitVec.ofNat 64 setJ)
    (h0 : S'.regs 0 = BitVec.ofNat 64 pw) (h1 : S'.regs 1 = BitVec.ofNat 64 lw) (h2 : S'.regs 2 = BitVec.ofNat 64 cw)
    (h3 : S'.regs 3 = BitVec.ofNat 64 c) (h4 : S'.regs 4 = BitVec.ofNat 64 lw)
    (h5 : S'.regs 5 = BitVec.ofNat 64 ptr) :
    JS R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S' (L1 ++ [(ptr, ptr + r)]) (b1 - r) p1 l1 c1 q l2 pz
      lz cz pw lw cw ptr c := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 448) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := h.jx.wc
  have h8c : 8 * c ≤ r := hA.sz
  have hx : LiveExt R L1 (L1 ++ [(ptr, ptr + r)]) :=
    LiveExt.single (by rw [show ptr + r - ptr = r by omega]; exact hA.rin)
      (by rw [show ptr + r - ptr = r by omega]; exact hA.rap)
  have hhd : HdrEq st S.mem m := by
    have hh : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = S.mem.readLE (st + j) 8 := fun j hj =>
      hA.rdH _ _ (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart at hstw ⊢; omega)
    refine ⟨?_, hh 8 (by omega), hh 16 (by omega)⟩
    have := hh 0 (by omega); simpa using this
  have kN : ∀ {q' l c' v : Nat}, LN R L s.mem st S.mem L1 q' l c' v →
      LN R L s.mem st m (L1 ++ [(ptr, ptr + r)]) q' l c' v := fun hq =>
    LN.frm hP hx hA.macc hhd (d := 0) (n := 0) (fun a k hh hw' _ => hA.rdH a k hh hw') hq
      (fun _ => by unfold Apart; omega)
  have hin : InRanges ptr (8 * c) R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  have hap1 : ApartAll ptr (8 * c) L1 := fun x hx' => by
    have := hA.rap x hx'; unfold Apart at this ⊢; omega
  have hheld : Held R (L1 ++ [(ptr, ptr + r)]) ptr (8 * c) :=
    Or.inl ⟨(ptr, ptr + r), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by
      simp only; omega⟩
  have hob : Ob R (L1 ++ [(ptr, ptr + r)]) st m ptr c :=
    ob_fresh hw.sok (WC.cap0 hP hw) hin hap1 hheld (fun _ hne => absurd ⟨hhd.1, hhd.2.2⟩ hne) hc0
  have hb48 := hA.b48
  subst hm
  refine ⟨⟨esp.trans h.jx.esp, e28.trans h.jx.e28, e29.trans h.jx.e29, e18.trans h.jx.e18, hA.wc,
      h.jx.esl.keep (fun a k ha => hA.keep a k (by simp only [SlotR] at ha; omega)) (by omega), hbud⟩,
    hpc, h0, h1, h2, h3, h4, h5,
    (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s288, (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s208,
    (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s216, (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s280,
    (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s192, (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s200,
    (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s264, (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s152,
    (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s160, (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s256,
    (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s136, (hA.keep _ _ (Or.inr ⟨by omega, by omega⟩)).trans h.s144,
    kN h.m1, h.c1p, kN h.m2, h.ap, kN h.z1, h.pz64, h.za1, h.za2, kN h.z2, h.pw64, h.wa1, h.wa2, h.wz,
    ⟨hc40, fun _ => ⟨hA.al, hheld, Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega), by omega⟩,
      fun _ => Or.inr ⟨hin, fun x hx' => hap1 x (hw.le.mem_old hx'), hob⟩, hc⟩, hptr,
    fun _ => hfresh (h.m1.1.2.1 h.c1p).2.1 hap1 hin, fun _ => hfresh (h.m2.1.2.1 h.a2p).2.1 hap1 hin,
    fun _ cz0 => hfresh (h.z1.1.2.1 cz0).2.1 hap1 hin, fun _ cw0 => hfresh (h.z2.1.2.1 cw0).2.1 hap1 hin, h.lwm⟩

end

end FvModexp.Arm64.ExpEven
