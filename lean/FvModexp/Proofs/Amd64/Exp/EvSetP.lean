import FvModexp.Proofs.Amd64.Exp.EvSetT

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `J8` → `setJ` (asm s61; twin of infra's arm64 `EvSetP`)

`JP` = `J8`'s locals after `runS`'s spills of `z2` (`0xf8/0x80/0x88`, `0x78` on the `makeslice(l, l + 4)` path, the
`CALL`'s return-address push at `sp - 8`): `j8_own`; `JP.reuseJS` (entry `z` reused), `JP.mkJS` (a fresh `makeslice`
array).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `J8`'s locals after `z2`'s spills -/
structure JP (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
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
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  a2p : 0 < a2 ml (nE s mp ml)
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
  lwm : lw ≤ ml

/-- the budget after an allocation (outside any large context) -/
theorem bud_alloc {rk b1 a rk' r : Nat} (h1 : rk ≤ b1) (h2 : a + rk' ≤ rk) (h3 : r ≤ a) : rk' ≤ b1 - r := by omega

/-- the frame written by `runS` (every path) -/
@[reducible] def F3 (sp : Nat) : List (Nat × Nat) := [(sp - 8, sp), (sp + 0x78, sp + 0x90), (sp + 0xf8, sp + 0x100)]

theorem fr_K0 {sp : Nat} {M M' : Memory} (hsp : 8 ≤ sp) (h : MemFrame M M' [(sp + 0x80, sp + 0x90), (sp + 0xf8, sp + 0x100)]) :
    MemFrame M M' (F3 sp) :=
  h.mono fun a n hh => by simp only [F3, outside_cons, outside_nil, and_true] at hh ⊢; omega

theorem fr_K1 {sp : Nat} {M M' : Memory} (hsp : 8 ≤ sp)
    (h : MemFrame M M' [(sp - 8, sp), (sp + 0x80, sp + 0x90), (sp + 0xf8, sp + 0x100)]) : MemFrame M M' (F3 sp) :=
  h.mono fun a n hh => by simp only [F3, outside_cons, outside_nil, and_true] at hh ⊢; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `J8` through `runS`'s spills of `z2` and the `CALL`'s push (`F3`) -/
theorem j8_own (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : J8 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw)
    {S2 : State} {M2 : Memory} (hF : MemFrame S.mem M2 (F3 sp))
    (hrg : M2.regions = S.mem.regions) (fm : S2.mem = M2) (f4 : S2.regs 4 = S.regs 4) (f14 : S2.regs 14 = S.regs 14)
    (ffs : S2.fsBase = S.fsBase) (fx : S2.xmm 15 = S.xmm 15) (fdf : S2.df = S.df) (rf8 : M2.readLE (sp + 0xf8) 8 = pw)
    (r80 : M2.readLE (sp + 0x80) 8 = lw) (r88 : M2.readLE (sp + 0x88) 8 = cw) :
    JP R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S2 L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw := by
  have hk := hP.kf
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  have hlwm : lw ≤ ml := by
    have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
    have hlt : natVal s.mem mp ml < 2 ^ (64 * ml) := by
      have := Janus.Arm64.Memory.readLE_lt s.mem mp (8 * ml)
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * ml) = 64 * ml by omega] at this
      exact this
    have hpos : 0 < natVal s.mem mp ml / 2 ^ nE s mp ml :=
      Nat.pos_of_ne_zero fun e => by rw [e] at hodd; exact absurd hodd (by decide)
    refine nlen_bd' h.z2.2.2.2 ?_
    rw [h.z2.2.2.1]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.le_trans (Nat.div_le_self _ _) (Nat.le_of_lt hlt))
  obtain ⟨hw2, hown⟩ := WC.own hP h.jx.wc hF hrg (fun q hq => by
    simp only [F3, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a, sp ≤ a → (a + 8 ≤ sp + 0x78 ∨ sp + 0x90 ≤ a) → (a + 8 ≤ sp + 0xf8 ∨ sp + 0x100 ≤ a) →
      M2.readLE a 8 = S.mem.readLE a 8 := fun a h0 h1 h2 =>
    hF.readLE a 8 (by simp only [F3, outside_cons, outside_nil, and_true]; omega)
  subst fm
  exact ⟨⟨f4.trans h.jx.esp, f14.trans h.jx.e14, by rw [ffs]; exact h.jx.efs, fx.trans h.jx.ex15, fdf.trans h.jx.edf,
      hw2, h.jx.esl.keep (fun a k ha => hF.readLE a k (by
        simp only [SlotR] at ha; simp only [F3, outside_cons, outside_nil, and_true]; omega)), h.jx.bud⟩,
    (kF _ (by omega) (by omega) (by omega)).trans h.s118, (kF _ (by omega) (by omega) (by omega)).trans h.sc8,
    (kF _ (by omega) (by omega) (by omega)).trans h.sd0, (kF _ (by omega) (by omega) (by omega)).trans h.s110,
    (kF _ (by omega) (by omega) (by omega)).trans h.sb8, (kF _ (by omega) (by omega) (by omega)).trans h.sc0,
    (kF _ (by omega) (by omega) (by omega)).trans h.s100, (kF _ (by omega) (by omega) (by omega)).trans h.s90,
    (kF _ (by omega) (by omega) (by omega)).trans h.s98, rf8, r80, r88,
    hown _ _ _ _ h.m1, h.c1p, hown _ _ _ _ h.m2, ha2, h.ap, hown _ _ _ _ h.z1, h.pz64, h.z1e, h.za1, h.za2,
    hown _ _ _ _ h.z2, h.pw64, h.z2e, h.wa1, h.wa2, h.wz, hlwm⟩

/-- **reuse**: `len z2 ≤ cap z` → `JS` with `z`'s entry array -/
theorem JP.reuseJS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {rk rk' : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : JP R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw)
    (hrk : rk' ≤ rk) (hpc : S.rip = BitVec.ofNat 64 setJ) (h0 : S.regs 0 = BitVec.ofNat 64 pw)
    (h1 : S.regs 1 = BitVec.ofNat 64 cw) (h3 : S.regs 3 = BitVec.ofNat 64 lw) (h6 : S.regs 6 = BitVec.ofNat 64 lw)
    (h7 : S.regs 7 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (hlz : lw ≤ zc) :
    JS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw zp zc := by
  have hw := h.jx.wc
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzp, hzc, hz, -⟩ := hP'
  have hbud := h.jx.bud
  refine ⟨⟨h.jx.esp, h.jx.e14, h.jx.efs, h.jx.ex15, h.jx.edf, hw, h.jx.esl, Nat.le_trans hrk hbud⟩, hpc, h0, h1, h3,
    h6, h7, h2, h.s118, h.sc8, h.sd0, h.s110, h.sb8, h.sc0, h.s100, h.s90, h.s98, h.sf8, h.s80, h.s88, h.m1, h.c1p,
    h.m2, h.ap, h.z1, h.pz64, h.z1e, h.za1, h.za2, h.z2, h.pw64, h.z2e, h.wa1, h.wa2, h.wz,
    ⟨hzc, fun c0 => ?_, fun _ => Or.inl ⟨rfl, rfl⟩, hlz⟩, hzp, fun _ => ⟨rfl, rfl⟩,
    fun c0 => ((Loc.ap hP (h.m1.1.2.2 h.c1p).1).2.2.2.2 c0).symm,
    fun c0 => ((Loc.ap hP (h.m2.1.2.2 h.a2p).1).2.2.2.2 c0).symm,
    fun c0 cz0 => ((Loc.ap hP (h.z1.1.2.2 cz0).1).2.2.2.2 c0).symm,
    fun c0 cw0 => ((Loc.ap hP (h.z2.1.2.2 cw0).1).2.2.2.2 c0).symm, h.lwm⟩
  obtain ⟨oe, acc, b48, al, -⟩ := hz c0
  exact ⟨al, hw.le.held oe.1, by rw [hw.fr.accessible]; exact acc, b48⟩

set_option maxRecDepth 20000 in
/-- **fresh**: a `makeslice` array `[ptr, ptr + r)` of capacity `c ≥ len z2` → `JS` -/
theorem JP.mkJS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {rk rk' : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : JP R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw)
    {m : Memory} {ptr rr c : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem S.mem L1 b1 (lvl4 s st mp ml l1 l2) m ptr rr (8 * c))
    (hc : lw ≤ c) (hc40 : c < 2 ^ 40) (hc0 : 0 < c) (hptr : ptr < 2 ^ 64) (hbud : rk' ≤ b1 - rr)
    (S' : State) (esp : S'.regs 4 = S.regs 4) (e14 : S'.regs 14 = S.regs 14) (efs : S'.fsBase = S.fsBase)
    (ex15 : S'.xmm 15 = S.xmm 15) (edf : S'.df = S.df) (hm : S'.mem = m) (hpc : S'.rip = BitVec.ofNat 64 setJ)
    (h0 : S'.regs 0 = BitVec.ofNat 64 pw) (h1 : S'.regs 1 = BitVec.ofNat 64 cw) (h3 : S'.regs 3 = BitVec.ofNat 64 lw)
    (h6 : S'.regs 6 = BitVec.ofNat 64 lw) (h7 : S'.regs 7 = BitVec.ofNat 64 ptr)
    (h2 : S'.regs 2 = BitVec.ofNat 64 c) :
    JS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S' (L1 ++ [(ptr, ptr + rr)]) (b1 - rr) p1 l1 c1 q
      l2 pz lz cz pw lw cw ptr c := by
  have hk := hP.kf
  have hstw := hP.stkF.1
  have hw := h.jx.wc
  have h8c : 8 * c ≤ rr := hA.sz
  have hx : LiveExt R L1 (L1 ++ [(ptr, ptr + rr)]) :=
    LiveExt.single (by rw [show ptr + rr - ptr = rr by omega]; exact hA.rin)
      (by rw [show ptr + rr - ptr = rr by omega]; exact hA.rap)
  have hhd : HdrEq st S.mem m := by
    have hh : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = S.mem.readLE (st + j) 8 := fun j hj =>
      hA.rdH _ _ (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart at hstw ⊢; omega)
    refine ⟨?_, hh 8 (by omega), hh 16 (by omega)⟩
    have := hh 0 (by omega); simpa using this
  have kN : ∀ {q' l c' v : Nat}, LN R L s.mem st S.mem L1 q' l c' v →
      LN R L s.mem st m (L1 ++ [(ptr, ptr + rr)]) q' l c' v := fun hq =>
    LN.frm hP hx hA.macc hhd (d := 0) (n := 0) (fun a k hh hw' _ => hA.rdH a k hh hw') hq
      (fun _ => by unfold Apart; omega)
  have hin : InRanges ptr (8 * c) R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  have hap1 : ApartAll ptr (8 * c) L1 := fun x hx' => by
    have := hA.rap x hx'; unfold Apart at this ⊢; omega
  have hheld : Held R (L1 ++ [(ptr, ptr + rr)]) ptr (8 * c) :=
    Or.inl ⟨(ptr, ptr + rr), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by
      simp only; omega⟩
  have hob : ObZ R (L1 ++ [(ptr, ptr + rr)]) st m ptr c :=
    ob_freshZ hw.sok (WC.cap0 hP hw) hin hap1 hheld (fun _ hne => absurd ⟨hhd.1, hhd.2.2⟩ hne) hc0
  have hb48 := hA.b48
  have kS : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 0x1b8 → m.readLE a 8 = S.mem.readLE a 8 :=
    fun a h1 h2 => hA.keep a 8 (Or.inr ⟨h1, h2⟩)
  subst hm
  refine ⟨⟨esp.trans h.jx.esp, e14.trans h.jx.e14, by rw [efs]; exact h.jx.efs, ex15.trans h.jx.ex15,
      edf.trans h.jx.edf, hA.wc, h.jx.esl.keep (fun a k ha => hA.keep a k (by simp only [SlotR] at ha; omega)), hbud⟩,
    hpc, h0, h1, h3, h6, h7, h2,
    (kS _ (by omega) (by omega)).trans h.s118, (kS _ (by omega) (by omega)).trans h.sc8,
    (kS _ (by omega) (by omega)).trans h.sd0, (kS _ (by omega) (by omega)).trans h.s110,
    (kS _ (by omega) (by omega)).trans h.sb8, (kS _ (by omega) (by omega)).trans h.sc0,
    (kS _ (by omega) (by omega)).trans h.s100, (kS _ (by omega) (by omega)).trans h.s90,
    (kS _ (by omega) (by omega)).trans h.s98, (kS _ (by omega) (by omega)).trans h.sf8,
    (kS _ (by omega) (by omega)).trans h.s80, (kS _ (by omega) (by omega)).trans h.s88,
    kN h.m1, h.c1p, kN h.m2, h.ap, kN h.z1, h.pz64, h.z1e, h.za1, h.za2, kN h.z2, h.pw64, h.z2e, h.wa1, h.wa2, h.wz,
    ⟨hc40, fun _ => ⟨hA.al, hheld, Janus.Arm64.Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega), by omega⟩,
      fun _ => Or.inr ⟨hin, fun x hx' => hap1 x (hw.le.mem_old hx'), hob⟩, hc⟩, hptr, fun e => absurd e (by omega),
    fun _ => hfresh (h.m1.1.2.1 h.c1p).2.1 hap1 hin, fun _ => hfresh (h.m2.1.2.1 h.a2p).2.1 hap1 hin,
    fun _ cz0 => hfresh (h.z1.1.2.1 cz0).2.1 hap1 hin, fun _ cw0 => hfresh (h.z2.1.2.1 cw0).2.1 hap1 hin, h.lwm⟩

end

end FvModexp.Amd64.ExpEven
