import FvModexp.Proofs.Amd64.Nat.DivBasicDefs

set_option autoImplicit false

/-!
# `divBasic` (amd64): the address layout after `qhatv := stk.nat(n + 1)` (pure)

`Lay`: every disjointness/bound fact the segment proofs need, as omega-ready disjunctions (one `have := hl.x` per use).
`Env.lay` derives it once from `Env`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

theorem mfTrans {m₀ m₁ m₂ : Memory} {rs rs' : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs)
    (h₂ : MemFrame m₁ m₂ rs') : MemFrame m₀ m₂ (rs ++ rs') where
  readLE a k ho := by
    rw [outside_append] at ho
    rw [h₂.readLE a k ho.2, h₁.readLE a k ho.1]
  accessible a k w := by rw [h₂.accessible, h₁.accessible]

theorem LiveFrame.trans' {m1 m2 m3 : Memory} {L ws : List (Nat × Nat)} (h1 : LiveFrame m1 m2 L ws)
    (h2 : LiveFrame m2 m3 L ws) : LiveFrame m1 m3 L ws :=
  ⟨fun a n hin ho => (h2.readLE a n hin ho).trans (h1.readLE a n hin ho)⟩

structure Lay (R : RtInv) (L L1 : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s : State) (t : Nat) : Prop where
  sp0 : 4424 ≤ (s.regs 4).toNat
  sp1 : (s.regs 4).toNat + 88 ≤ 2 ^ 48
  spa : (s.regs 4).toNat % 8 = 0
  v2 : 2 ≤ vl
  vb : vl + 4 ≤ 2 ^ 16
  q48 : qp + 8 * ql ≤ 2 ^ 48
  u48 : up + 8 * ul ≤ 2 ^ 48
  v48 : vp + 8 * vl ≤ 2 ^ 48
  t48 : t + 8 * (vl + 1) ≤ 2 ^ 48
  qw : qp + 8 * ql ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ qp
  uw : up + 8 * ul ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ up
  vw : vp + 8 * vl ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ vp
  tw : t + 8 * (vl + 1) ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ t
  sw : st + 24 ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ st
  qu : qp + 8 * ql ≤ up ∨ up + 8 * ul ≤ qp
  qv : qp + 8 * ql ≤ vp ∨ vp + 8 * vl ≤ qp
  uv : up + 8 * ul ≤ vp ∨ vp + 8 * vl ≤ up
  tq : t + 8 * (vl + 1) ≤ qp ∨ qp + 8 * ql ≤ t
  tu : t + 8 * (vl + 1) ≤ up ∨ up + 8 * ul ≤ t
  tv : t + 8 * (vl + 1) ≤ vp ∨ vp + 8 * vl ≤ t
  ts : t + 8 * (vl + 1) ≤ st ∨ st + 24 ≤ t
  sq : st + 24 ≤ qp ∨ qp + 8 * ql ≤ st
  su : st + 24 ≤ up ∨ up + 8 * ul ≤ st
  sv : st + 24 ≤ vp ∨ vp + 8 * vl ≤ st
  tg : t + 8 * (vl + 1) ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 16 + 8 ≤ t
  qg : qp + 8 * ql ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 16 + 8 ≤ qp
  ug : up + 8 * ul ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 16 + 8 ≤ up
  gw : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ (s.regs 14).toNat + 16
  tlw : s.fsBase.toNat - 8 + 8 ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ s.fsBase.toNat - 8
  tlq : qp + 8 * ql ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat - 8 + 8 ≤ qp
  tlu : up + 8 * ul ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat - 8 + 8 ≤ up
  tlt : t + 8 * (vl + 1) ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat - 8 + 8 ≤ t
  tls : st + 24 ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat - 8 + 8 ≤ st
  theld : Held R L1 t (8 * (vl + 1))
  lsep : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ r.1

theorem Env.lay {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) :
    Lay R L L1 qp ql st up ul vp vl s t := by
  have hpre := hE.pre
  have hce := hpre.ce
  have hvb : vl + 4 ≤ 2 ^ 16 := by have := hpre.stlen; omega
  have hgw : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ (s.regs 14).toNat + 16 := by
    have := hce.2.2.2.2.2.1; unfold Apart at this; omega
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [regSP] at hb' ha hw
  have hscr := hE.scr
  have hfr : ∀ p n, Held R L p n → (0 < stCap s.mem st → Apart p n (freeP s.mem st) (freeN s.mem st)) →
      Apart t (8 * (vl + 1)) p n := fun p n h1 h2 => hscr.apart h1 h2
  have htq := hfr qp (8 * ql) hpre.qh (fun _ => hpre.free.1)
  have htu := hfr up (8 * ul) hpre.uh (fun _ => hpre.free.2.1)
  have htv := hfr vp (8 * vl) hpre.vh (fun _ => hpre.free.2.2)
  have hts := hfr st 24 hpre.stok.2.1 (fun _ => hpre.stfree)
  have htw : Outside t (8 * (vl + 1)) (win s 4424 88) := by
    refine hscr.outside ?_ ?_
    · intro r hr; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact hout.of_sub (by omega) (by omega)
    · intro r hr hc; simp only [win, List.mem_singleton] at hr; subst hr
      have := (hpre.starr hc).1
      simp only [win, outside_cons, outside_nil, and_true] at this
      have hlc := hpre.stok.2.2.2.2.2.1
      simp only [Apart]; omega
  have htg : Apart t (8 * (vl + 1)) ((s.regs 14).toNat + 16) 8 := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have := (hpre.starr h0).2; unfold Apart at this ⊢; have := hpre.stok.2.2.2.2.2.1; omega
    · have := hin.apart hgr; unfold Apart at this ⊢; omega
  have hqw := hpre.qw; have huw := hpre.uw; have hvw := hpre.vw; have hsw := hpre.stw
  simp only [win, outside_cons, outside_nil, and_true] at hqw huw hvw hsw htw
  have hqu := hpre.qu; have hqv := hpre.qv; have huv := hpre.uv; have hsq := hpre.stq; have hsu := hpre.stu
  have hsv := hpre.stv; have hqg := hpre.qg; have hug := hpre.ug
  unfold Apart at htq htu htv hts htg hqu hqv huv hsq hsu hsv hqg hug hga
  have hlen := hpre.stlen
  have hls : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; exact this
  have hq48 := hpre.q48; have hu48 := hpre.u48; have hv48 := hpre.v48; have ht48 := hscr.b48
  have hv2 := hpre.v2
  have htl := hpre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨-, htlr, htlw⟩ := htl
  unfold Apart at htlw
  have htlt : t + 8 * (vl + 1) ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat - 8 + 8 ≤ t := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have := hpre.stft; simp only [freeP, freeN] at this; unfold Apart at this
      have := hpre.stok.2.2.2.2.2.1; omega
    · have := hin.apart htlr; unfold Apart at this; omega
  have hqt := hpre.qt; have hut := hpre.ut; have hstt := hpre.stt
  unfold Apart at hqt hut hstt
  exact ⟨hb', ha, hal, hv2, hvb, hq48, hu48, hv48, ht48, hqw, huw, hvw, htw, hsw, hqu, hqv, huv, htq, htu, htv, hts,
    hsq, hsu, hsv, htg, hqg, hug, hgw, by omega, by omega, by omega, htlt, by omega, hscr.held, hls⟩

end FvModexp.Amd64.DivBasic
