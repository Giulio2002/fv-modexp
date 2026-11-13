import FvModexp.Proofs.Amd64.Nat.DivPostK
import FvModexp.Proofs.Amd64.Nat.DivGDefs

set_option autoImplicit false

/-!
# `nat.div` (amd64): the empty-tolerant / results-apart form `ExpSlow.DivHypLG` — defs (pure); twin of `Arm64/Nat/DivG.lean`

`PostLG` = `ExpSlow.DivPostLG` at `nat.div`'s window (`41512`/`112`) and budget (`cost dc`); `RQG` = `RQ` with it;
`PreG` = `ExpSlow.DivPreG` (`PFG`: its conjuncts by name); `post_keptG`: `post_kept` (stack untouched) with the two
extra clauses; only "both results fresh" needs a premise.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges held_apart_fresh)

namespace FvModexp.Amd64.NatDiv

@[reducible] def PostLG (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  ExpSlow.DivPostLG R b (cost dc) L 41512 112 zp zc st z2 z2c u ul v vl s s'

@[reducible] def RQG (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    PostLG R b dc L zp zc st z2 z2c u ul v vl s s'

/-- the precondition: `ExpSlow.DivPreG` at `nat.div`'s window and budget -/
@[reducible] def PreG (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop :=
  ExpSlow.DivPreG R b (cost dc) L 41512 112 zp zl zc st z2 z2l z2c u ul uc v vl vc s

/-- `PreG`'s conjuncts by name (as `PF`) -/
structure PFG (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop where
  ru : s.mem.readLE ((s.regs 4).toNat + 8) 8 = u
  rul : s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul
  ruc : s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc
  rv : s.mem.readLE ((s.regs 4).toNat + 32) 8 = v
  rvl : s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl
  rvc : s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc
  ce : CallEnv R L s 41512 112
  sv : RunIface.Serves R
  gl : RunIface.Globals R s.mem (win s 41512 112)
  zl : zl ≤ zc
  z2l : z2l ≤ z2c
  zo : EvenHyp.WrOut R L s 41512 112 zp zc
  z2o : EvenHyp.WrOut R L s 41512 112 z2 z2c
  ui : EvenHyp.RdIn0 R L s 41512 112 u ul
  vo : EvenHyp.RdIn R L s 41512 112 v vl
  ul9 : ul ≤ 2 ^ 9
  v0 : 0 < vl
  vl9 : vl ≤ 2 ^ 9
  un : NatNorm s.mem u ul
  vn : NatNorm s.mem v vl
  sok : ExpHyp.StackOK' s.mem R L st
  sw : Outside st 24 (win s 41512 112)
  sa : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 41512 112) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8
  sl : stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16
  w0 : stCap s.mem st = 0 → stW s.mem st = 0
  usf : 0 < ul → Apart u (8 * ul) st 24 ∧
      Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  vs : Apart v (8 * vl) st 24
  vf : Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  st0 : st ≠ 0
  hdr : Apart st 24 ((s.regs 14).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  tls : Apart st 24 (s.fsBase.toNat - 8) 8 ∧
      Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8
  zg : 0 < zc → Apart zp (8 * zc) RunIface.gA 32
  z2g : 0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32
  sg : Apart st 24 RunIface.gA 32
  fg : Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32
  zz2 : 0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)
  pw : ∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      (0 < ul → Apart p (8 * c) u (8 * ul)) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  cost : cost dc (stLen s.mem st) ul vl ≤ b
  adx : s.mem.accessible Callees.adxAddr 1 false = true
  inv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

theorem PreG.f {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (h : PreG R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) :
    PFG R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s := by
  obtain ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, hA, h31⟩ := h
  exact ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, hA, h31⟩

theorem Pre.toG {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (h : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) :
    PreG R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s := by
  obtain ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, hA, h31⟩ := h
  refine ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8.toRdIn0, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, fun _ => ⟨h20, h21⟩, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, fun p c hm hc => ?_, h30, hA, h31⟩
  obtain ⟨a1, a2, a3, a4⟩ := h29 p c hm hc
  exact ⟨fun _ => a1, a2, a3, a4⟩

/-- a non-empty dividend: `PreG` is `Pre` -/
theorem PreG.toPre {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (h : PreG R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) (hu : 0 < ul) :
    Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s := by
  obtain ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, hA, h31⟩ := h
  refine ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8.toRdIn hu, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, (h20 hu).1, (h20 hu).2, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, fun p c hm hc => ?_, h30,
    hA, h31⟩
  obtain ⟨a1, a2, a3, a4⟩ := h29 p c hm hc
  exact ⟨a1 hu, a2, a3, a4⟩

theorem RQG.toRQ {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zc st z2 z2c u ul v vl : Nat} {s s' : State} (h : RQG R b dc L zp zc st z2 z2c u ul v vl s s') :
    RQ R b dc L zp zc st z2 z2c u ul v vl s s' :=
  ⟨h.1, ExpSlow.DivPostLG.toL h.2⟩

/-- the results-apart clause (ii) from the two `NatOF`s: an old result is held (`WrOut`), a fresh one is apart from
`L` and inside `R.rt`; only "both fresh" needs `hff` -/
theorem qr_apart {R : RtInv} {L L' : List (Nat × Nat)} {m : Memory} {zp zc z2 z2c q ql qc r rl rc vq vr : Nat}
    {s : State} {stk above : Nat}
    (hzo : EvenHyp.WrOut R L s stk above zp zc) (hz2o : EvenHyp.WrOut R L s stk above z2 z2c)
    (hzz : 0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c))
    (hq : ExpHyp.NatOF R L L' m zp zc 1 q ql qc vq) (hr : ExpHyp.NatOF R L L' m z2 z2c 1 r rl rc vr)
    (hff : ¬(q = zp ∧ qc = zc) → ¬(r = z2 ∧ rc = z2c) → 0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc)) :
    0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc) := by
  intro hqc hrc
  rcases hq.2.2.2.2.2 with ⟨e1, e2⟩ | ⟨-, hqin, hqap⟩
  · rcases hr.2.2.2.2.2 with ⟨f1, f2⟩ | ⟨-, hrin, hrap⟩
    · subst e1 e2 f1 f2; exact hzz hqc hrc
    · subst e1 e2; exact (held_apart_fresh (hzo.2.1 hqc).2.1 hrap hrin).symm
  · rcases hr.2.2.2.2.2 with ⟨f1, f2⟩ | ⟨-, hrin, hrap⟩
    · subst f1 f2; exact held_apart_fresh (hz2o.2.1 hrc).2.1 hqap hqin
    · refine hff ?_ ?_ hqc hrc
      · rintro ⟨e1, e2⟩; subst e1 e2; have := held_apart_fresh (hzo.2.1 hqc).2.1 hqap hqin; unfold Apart at this; omega
      · rintro ⟨e1, e2⟩; subst e1 e2; have := held_apart_fresh (hz2o.2.1 hrc).2.1 hrap hrin; unfold Apart at this; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `post_kept` with (ii) and (iii) (`PostLG`) -/
theorem post_keptG {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : PreG R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) (s' : State) {q ql qc r rl rc : Nat}
    {L' : List (Nat × Nat)} {b' : Nat}
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 3 = BitVec.ofNat 64 ql) (h2 : s'.regs 1 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 r) (h4 : s'.regs 6 = BitVec.ofNat 64 rl) (h5 : s'.regs 8 = BitVec.ofNat 64 rc)
    (hq : ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl))
    (hr : ExpHyp.NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl))
    (hext : LiveExt R L L') (hb : b - cost dc (stLen s.mem st) ul vl ≤ b')
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem))
    (hMF : MemFrame s.mem s'.mem (R.rt ++ win s 41512 112 ++ ar zp zc ++ ar z2 z2c))
    (hLF : LiveFrame s.mem s'.mem L (ar zp zc ++ ar z2 z2c))
    (hff : ¬(q = zp ∧ qc = zc) → ¬(r = z2 ∧ rc = z2c) → 0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc)) :
    PostLG R b dc L zp zc st z2 z2c u ul v vl s s' := by
  have hp := hpre.f
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hp.sok
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hz := hp.pw zp zc (by simp)
  have hz2 := hp.pw z2 z2c (by simp)
  -- the stack header is unchanged
  have hhd : ∀ a n, st ≤ a → a + n ≤ st + 24 → s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have ho : Outside a n (ar zp zc ++ ar z2 z2c) := by
      rw [outside_append]
      refine ⟨outside_ar fun hc => ?_, outside_ar fun hc => ?_⟩
      · have := (hz hc).2.2.1; unfold Apart at this; omega
      · have := (hz2 hc).2.2.1; unfold Apart at this; omega
    rcases hsth with hin | hout
    · exact hLF.readLE a n (hin.sub h1 h2) ho
    · refine hMF.readLE a n ?_
      simp only [outside_append] at ho ⊢
      refine ⟨⟨⟨hout.of_sub h1 h2, ?_⟩, ho.1⟩, ho.2⟩
      simp only [win, outside_cons, outside_nil, and_true]; omega
  have ew : stW s'.mem st = stW s.mem st := hhd st 8 (Nat.le_refl _) (by omega)
  have el : stLen s'.mem st = stLen s.mem st := hhd (st + 8) 8 (by omega) (by omega)
  have ec : stCap s'.mem st = stCap s.mem st := hhd (st + 16) 8 (by omega) (by omega)
  refine ⟨hfs, hdf, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, ⟨hext, hb, hinv⟩,
    ⟨⟨?sok, el, Or.inl ⟨ew, ec⟩⟩, fun hn => absurd ⟨ew, ec⟩ hn⟩, ?fresh, ?mf, ?lf,
    qr_apart hp.zo hp.z2o hp.zz2 hq hr hff, ?qfresh⟩
  case sok =>
    refine ⟨hst8, hext.held hsth, by rw [hMF.accessible]; exact hstacc, hst48, ?_, by rw [el, ec]; exact hlc,
      by rw [ec]; exact hc40⟩
    rw [ew, ec]
    intro hc0
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc0
    exact ⟨a1, hext.held a2, by rw [hMF.accessible]; exact a3, a4⟩
  case fresh =>
    intro hne hrc hcap
    rcases hr.2.2.2.2.2 with ⟨e1, e2⟩ | ⟨-, hrin, hrap⟩
    · exact absurd ⟨e1, e2⟩ hne
    · rw [ec] at hcap; rw [ew, ec]
      exact held_apart_fresh (hnl hcap).2.1 hrap hrin
  case qfresh =>
    intro hne hqc hcap
    rcases hq.2.2.2.2.2 with ⟨e1, e2⟩ | ⟨-, hqin, hqap⟩
    · exact absurd ⟨e1, e2⟩ hne
    · rw [ec] at hcap; rw [ew, ec]
      exact held_apart_fresh (hnl hcap).2.1 hqap hqin
  case mf =>
    refine hMF.mono fun a n ho => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨⟨ho.1.1.1, ho.1.1.2⟩, outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2.1)⟩,
      outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2.2)⟩
  case lf =>
    refine ⟨fun a n hin ho => hLF.readLE a n hin ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.1),
      outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2)⟩

end FvModexp.Amd64.NatDiv
