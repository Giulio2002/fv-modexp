import FvModexp.Proofs.Arm64.Nat.DivLargeRel
import FvModexp.Proofs.Arm64.Nat.NatAddMid

/-!
# `divLarge` (arm64): layout facts (`Lay`) and `Mem` across a frame (`Mem.frame`) — pure

`Lay`: the numeric facts every segment's `omega` needs (window, operands, scratch `v`, stack header), from `Env`.
`scr s`: the frame slots written after `stk.nat` besides `Mem`'s, and the area below the frame. `Mem.frame`: a
`MemFrame M M' (R.rt ++ scr s ++ wsL … ++ stkWs …)` with a `LiveFrame` over the same ranges keeps `Mem`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

namespace FvModexp.Arm64.DivLarge

/-- the numeric layout facts -/
structure Lay (R : RtInv) (L1 : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State) (t : Nat) : Prop where
  sp0 : 41264 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 112 ≤ 2 ^ 48
  v2 : 2 ≤ vl
  vil : vl ≤ il
  il9 : il ≤ 2 ^ 9
  zw : 0 < zc → zp + 8 * zc ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ zp
  uw : 0 < uc → up + 8 * uc ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ up
  iw : ip + 8 * il ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ ip
  vw : vp + 8 * vl ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ vp
  tw : t + 8 * vl ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ t
  sw : st + 24 ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ st
  tz : 0 < zc → t + 8 * vl ≤ zp ∨ zp + 8 * zc ≤ t
  tu : 0 < uc → t + 8 * vl ≤ up ∨ up + 8 * uc ≤ t
  ti : t + 8 * vl ≤ ip ∨ ip + 8 * il ≤ t
  tv : t + 8 * vl ≤ vp ∨ vp + 8 * vl ≤ t
  ts : t + 8 * vl ≤ st ∨ st + 24 ≤ t
  sz : 0 < zc → st + 24 ≤ zp ∨ zp + 8 * zc ≤ st
  su : 0 < uc → st + 24 ≤ up ∨ up + 8 * uc ≤ st
  si : st + 24 ≤ ip ∨ ip + 8 * il ≤ st
  sv : st + 24 ≤ vp ∨ vp + 8 * vl ≤ st
  zv : 0 < zc → zp + 8 * zc ≤ vp ∨ vp + 8 * vl ≤ zp
  zi : 0 < zc → zp + 8 * zc ≤ ip ∨ ip + 8 * il ≤ zp
  uv : 0 < uc → up + 8 * uc ≤ vp ∨ vp + 8 * vl ≤ up
  t48 : t + 8 * vl ≤ 2 ^ 48
  v48 : vp + 8 * vl ≤ 2 ^ 48
  i48 : ip + 8 * il ≤ 2 ^ 48
  st48 : st + 24 ≤ 2 ^ 48
  lsep : ∀ r ∈ L1, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ r.1
  theld : Held R L1 t (8 * vl)

theorem Env.lay {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) :
    Lay R L1 zp zc st up uc ip il vp vl s t := by
  have hpre := hE.pre
  have hv2 := hpre.v2
  have hil0 : 0 < il := by have := hpre.vil; omega
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hpre.ce
  obtain ⟨hz40, hzl, hzw⟩ := hpre.zo
  obtain ⟨hu40, hul, huw⟩ := hpre.uo
  obtain ⟨hi40, hiacc, hi48, hih, hiw⟩ := hpre.io
  obtain ⟨hv40, hvacc, hv48, hvh, hvw⟩ := hpre.vo
  obtain ⟨⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩, hsw, hsg, hstarr⟩ := hpre.sti
  simp only [win, outside_cons, outside_nil, and_true] at hiw hvw hsw
  simp only [LiveSep, win] at hLs
  have hscr := hE.scr
  have hext := hE.ext
  have hsz := hpre.sz; have hsu := hpre.su; have hsi := hpre.si; have hsv := hpre.svv
  have hzio := hpre.zio; have huv := hpre.uv
  -- `t` is in the entry stack's free part (apart from everything the operands' `StkApart` excludes) or fresh
  have hfree : ∀ p n, Outside p n R.rt ∨ InRanges p n L →
      (0 < n → stLen s.mem st < stCap s.mem st →
        Apart p n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) →
      0 < n → Apart t (8 * vl) p n := by
    intro p n hpn hfr hn
    rcases hscr.loc with ⟨hc0, hl1, hl2⟩ | ⟨hin, hap⟩
    · have := hfr hn (by omega); unfold Apart at this ⊢; omega
    · rcases hpn with ho | hi
      · have := outside_of_inRanges ho hin; unfold Apart; omega
      · obtain ⟨r, hr, h1, h2⟩ := hi; have := hap r hr; unfold Apart at this ⊢; omega
  have hv0 : 0 < 8 * vl := by have := hpre.v2; omega
  have htw : t + 8 * vl ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ t := by
    rcases hscr.loc with ⟨hc0, hl1, hl2⟩ | ⟨hin, -⟩
    · obtain ⟨ho, -⟩ := hstarr hc0
      simp only [win, outside_cons, outside_nil, and_true] at ho; omega
    · have := outside_of_inRanges hout hin; omega
  have hheld : ∀ p n, Held R L p n → Outside p n R.rt ∨ InRanges p n L := fun p n h => h.symm
  refine {
    sp0 := hb', sp1 := ha, v2 := hpre.v2, vil := hpre.vil, il9 := hpre.il9,
    zw := fun h => by have := (hzw h).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega,
    uw := fun h => by have := (huw h).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega,
    iw := by omega, vw := by omega, tw := htw, sw := by omega,
    tz := fun h => by
      have := hfree zp (8 * zc) (hheld _ _ (hzl h).2.1) (fun _ _ => (hsz h).2) (by omega)
      unfold Apart at this; omega,
    tu := fun h => by
      have := hfree up (8 * uc) (hheld _ _ (hul h).2.1) (fun _ _ => (hsu h).2) (by omega)
      unfold Apart at this; omega,
    ti := by
      have := hfree ip (8 * il) (hheld _ _ hih) (fun _ _ => hsi.2) (by omega)
      unfold Apart at this; omega,
    tv := by
      have := hfree vp (8 * vl) (hheld _ _ hvh) (fun _ _ => hsv.2) (by omega)
      unfold Apart at this; omega,
    ts := by
      rcases hscr.loc with ⟨hc0, hl1, hl2⟩ | ⟨hin, hap⟩
      · have := hpre.hf; unfold Apart at this; omega
      · rcases hsth with hi | ho
        · obtain ⟨r, hr, h1, h2⟩ := hi; have := hap r hr; unfold Apart at this; omega
        · have := outside_of_inRanges ho hin; omega,
    sz := fun h => by have := (hsz h).1; unfold Apart at this; omega,
    su := fun h => by have := (hsu h).1; unfold Apart at this; omega,
    si := by
      by_cases h0 : il = 0
      · subst h0; omega
      · have := hsi.1; unfold Apart at this; omega,
    sv := by have := hsv.1; unfold Apart at this; omega,
    zv := fun h => by have := (hzio h).2; unfold Apart at this; omega,
    zi := fun h => by
      by_cases h0 : il = 0
      · subst h0; omega
      · have := (hzio h).1; unfold Apart at this; omega,
    uv := fun h => by have := huv h; unfold Apart at this; omega,
    t48 := hscr.b48, v48 := hv48, i48 := hi48, st48 := hst48,
    lsep := by
      intro r hr
      rcases hext with ⟨ns, rfl, hn, -⟩
      rcases List.mem_append.1 hr with hr | hr
      · have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
      · have := outside_of_inRanges hout (hn r hr).1; omega,
    theld := hscr.held }

/-- the frame slots written between `stk.nat`'s return and the division call besides `Mem`'s (and the callee area) -/
@[reducible] def slotsW (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 41264, s.sp.toNat - 312), (s.sp.toNat - 296, s.sp.toNat - 201), (s.sp.toNat - 200, s.sp.toNat - 168),
    (s.sp.toNat - 160, s.sp.toNat - 144), (s.sp.toNat - 120, s.sp.toNat - 88)]

theorem mfTrans {m₀ m₁ m₂ : Memory} {rs rs' : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs)
    (h₂ : MemFrame m₁ m₂ rs') : MemFrame m₀ m₂ (rs ++ rs') where
  readLE a k ho := by
    rw [outside_append] at ho
    rw [h₂.readLE a k ho.2, h₁.readLE a k ho.1]
  accessible a k w := by rw [h₂.accessible, h₁.accessible]

set_option maxHeartbeats 4000000 in
/-- **`Mem` after `stk.nat`** (pure): from the prologue facts (`AtNat`), `stk.nat`'s frame (`F2`, `LF2`) and a frame `hM`
of the slots written since (and of a runtime call: `R.rt` with a `LiveFrame`). -/
theorem mem_of_nat {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {ic vc stkSN abSN : Nat}
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96) {P : State} (hP : AtNat st up uc ip il ic vp vl vc zp zc s P)
    {S2 : Memory} (hF2 : MemFrame P.mem S2 (R.rt ++ [(s.sp.toNat - 304 - stkSN, s.sp.toNat - 312),
      (s.sp.toNat - 296, s.sp.toNat - 304 + abSN)] ++ stkWs s.mem st))
    (hLF2 : LiveFrame P.mem S2 L (stkWs s.mem st))
    (hw1 : S2.readLE st 8 = w1) (hl1 : S2.readLE (st + 8) 8 = stLen s.mem st + StackNat.rnd vl)
    (hc1 : S2.readLE (st + 16) 8 = c1)
    {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} (hM : MemFrame S2 M (R.rt ++ slotsW s)) (hML : LiveFrame S2 M L1 [])
    (r1 : M.readLE (s.sp.toNat - 96) 8 = t) (r2 : M.readLE (s.sp.toNat - 160) 8 = vl)
    (r3 : M.readLE (s.sp.toNat - 152) 8 = vl) (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk M)) :
    Mem R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk M := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hF := hP.fr
  -- a window slot outside the callee area and the scratch slots keeps its `P` value
  have rdW : ∀ a n, s.sp.toNat - 41264 ≤ a → a + n ≤ s.sp.toNat + 112 →
      (a + n ≤ s.sp.toNat - 304 - stkSN ∨ s.sp.toNat - 312 ≤ a) → (a + n ≤ s.sp.toNat - 296 ∨ s.sp.toNat - 304 + abSN ≤ a) →
      Outside a n (slotsW s) → M.readLE a n = P.mem.readLE a n := by
    intro a n h1 h2 h3 h4 h5
    rw [hM.readLE a n (by rw [outside_append]; exact ⟨hout.of_sub h1 (by omega), h5⟩)]
    refine hF2.readLE a n ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub h1 (by omega), h3, h4⟩, ?_, ?_⟩
    · have := hl.sw; omega
    · have := hE.pre.fw
      simp only [win, outside_cons, outside_nil, and_true] at this; omega
  -- the slots
  have k : ∀ (a : Nat) {x : Nat}, s.sp.toNat - 41264 ≤ a → a + 8 ≤ s.sp.toNat + 112 →
      (a + 8 ≤ s.sp.toNat - 304 - stkSN ∨ s.sp.toNat - 312 ≤ a) → (a + 8 ≤ s.sp.toNat - 296 ∨ s.sp.toNat - 304 + abSN ≤ a) →
      Outside a 8 (slotsW s) → P.mem.readLE a 8 = x → M.readLE a 8 = x :=
    fun a _ h1 h2 h3 h4 h5 hx => (rdW a 8 h1 h2 h3 h4 h5).trans hx
  have so : ∀ a n, (s.sp.toNat - 312 ≤ a ∧ a + n ≤ s.sp.toNat - 296) ∨ (s.sp.toNat - 201 ≤ a ∧ a + n ≤ s.sp.toNat - 200) ∨
      (s.sp.toNat - 168 ≤ a ∧ a + n ≤ s.sp.toNat - 160) ∨ (s.sp.toNat - 144 ≤ a ∧ a + n ≤ s.sp.toNat - 120) ∨
      (s.sp.toNat - 88 ≤ a ∧ a + n ≤ s.sp.toNat + 112) → Outside a n (slotsW s) := by
    intro a n h; simp only [slotsW, outside_cons, outside_nil, and_true]; omega
  have hheld : ∀ a n, Held R L a n → (a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a) → Outside a n (stkWs s.mem st) →
      M.readLE a n = s.mem.readLE a n := by
    intro a n hh hw hs
    have h1 : P.mem.readLE a n = s.mem.readLE a n := hF.readLE a n (by
      simp only [proWs, outside_cons, outside_nil, and_true]; omega)
    have h2 : S2.readLE a n = P.mem.readLE a n :=
      FvModexp.Expmc.held_readLE hh hF2 hLF2 (by simp only [outside_cons, outside_nil, and_true]; omega) hs
    rw [← h1, ← h2]
    rcases hh with hi | ho
    · exact hML.readLE a n (hE.ext.inRanges_old hi) (by simp)
    · exact hM.readLE a n (by
        rw [outside_append]; exact ⟨ho, by simp only [slotsW, outside_cons, outside_nil, and_true]; omega⟩)
  have hS2 : ∀ a n, Held R L a n → (a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a) → M.readLE a n = S2.readLE a n := by
    intro a n hh hw
    rcases hh with hi | ho
    · exact hML.readLE a n (hE.ext.inRanges_old hi) (by simp)
    · exact hM.readLE a n (by
        rw [outside_append]; exact ⟨ho, by simp only [slotsW, outside_cons, outside_nil, and_true]; omega⟩)
  have hsth : Held R L st 24 := hE.pre.sti.1.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, plr, pfp, pdbit, pvtop, pil1, pmm, -, -, -, -, -, -, pdfn, pdst, pdn, pdp,
    ps1, ps3, ps4, ps5, ps7, ps8, ps9, ps10, ps11, ps12, ps13⟩ := hP
  refine ⟨k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) plr,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pfp, ?_,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pvtop,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pil1,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pmm, r1, r2, r3,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pdfn,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pdst,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pdn,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) pdp,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps1,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps3,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps4,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps5,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps7,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps8,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps9,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps10,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps11,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps12,
    k _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega)) ps13, ?_, ?_, ?_, ?_, ?_, ?_, hinv⟩
  · rw [rdW _ _ (by omega) (by omega) (by omega) (by omega) (so _ _ (by omega))]; exact pdbit
  · rw [hS2 _ _ (hsth.sub (Nat.le_refl _) (by omega)) (by have := hl.sw; omega)]; exact hw1
  · rw [hS2 _ _ (hsth.sub (by omega) (by omega)) (by have := hl.sw; omega)]; exact hl1
  · rw [hS2 _ _ (hsth.sub (by omega) (by omega)) (by have := hl.sw; omega)]; exact hc1
  · intro a n h1 h2
    exact hheld a n (hE.pre.vo.2.2.2.1.sub h1 h2) (by have := hl.vw; omega) (by
      simp only [stkWs, outside_cons, outside_nil, and_true]
      refine ⟨by have := hl.sv; omega, ?_⟩
      have := hE.pre.svv.2; unfold Apart at this; omega)
  · refine (mfTrans (mfTrans hF hF2) hM).mono fun a n ho => ?_
    simp only [outside_append] at ho
    obtain ⟨⟨⟨hrt, hwa⟩, -⟩, hsk⟩ := ho
    simp only [winA, outside_cons, outside_nil, and_true] at hwa
    simp only [stkWs, outside_cons, outside_nil, and_true] at hsk
    simp only [proWs, slotsW, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨hrt, by omega, by omega⟩, hsk⟩, hrt, by omega, by omega, by omega, by omega, by omega⟩
  · refine ⟨fun a n hin hws => ?_⟩
    have hw0 : a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r (hE.ext.mem_old hr); omega
    have hws' : Outside a n (stkWs s.mem st) := by rw [outside_append] at hws; exact hws.2
    rw [hML.readLE a n (hE.ext.inRanges_old hin) (by simp), hLF2.readLE a n hin hws']
    exact hF.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)

/-- the free part of the stack after `stk.nat(n)` is inside the array `(w1, c1)`, and that array is the entry one or
fresh: an operand array apart from the entry free part and held in `L` is apart from the new free part -/
theorem apart_free {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {p n : Nat} (hn : 0 < n)
    (hh : Held R L p n) (hfr : Apart p n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) :
    Apart p n (w1 + 8 * (stLen s.mem st + StackNat.rnd vl)) (8 * (c1 - (stLen s.mem st + StackNat.rnd vl))) := by
  have hlc := hE.c1len
  have hle := hE.pre.sti.1.2.2.2.2.2.1
  rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · unfold Apart at hfr ⊢; omega
  · rcases hh with hi | ho
    · obtain ⟨r, hr, h1, h2⟩ := hi; have := hap r hr; unfold Apart at this ⊢; omega
    · have := outside_of_inRanges ho hin; unfold Apart; omega

set_option maxHeartbeats 4000000 in
/-- `UArr` on the reuse path (`len uIn + 1 ≤ cap u`): `(P, C) = (up, uc)` -/
theorem uarr_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (hz : il + 1 ≤ uc) {M : Memory}
    (hacc : ∀ a n w, M.accessible a n w = s.mem.accessible a n w) :
    UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 L1 up uc M := by
  have hl := hE.lay
  have hpre := hE.pre
  have hu0 : 0 < uc := by omega
  obtain ⟨hu40, hul, huw⟩ := hpre.uo
  obtain ⟨hu8, huh, huacc, hu48⟩ := hul hu0
  have hut := hl.tu hu0
  have hsu := hpre.su hu0
  exact {
    cap := hz, c40 := hu40, p8 := hu8, p48 := hu48, pacc := by rw [hacc]; exact huacc,
    pw := hl.uw hu0, pg := (huw hu0).2, pheld := hE.ext.held huh, ror := Or.inl ⟨rfl, rfl⟩,
    pi := hpre.ui.imp id (fun h => h hu0), pv := hpre.uv hu0,
    pt := by unfold Apart; omega, ps := hsu.1,
    pz := fun h => by have := hpre.zu h hu0; unfold Apart at this ⊢; omega,
    pf := apart_free hE (by omega) huh hsu.2 }

set_option maxHeartbeats 4000000 in
/-- `UArr` on the allocation path: `makeslice` returned `[ptr, ptr + round)` (fresh, apart from `L1`) -/
theorem uarr_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (hz : uc < il + 1) {M : Memory}
    {ptr round : Nat} (hAp : ApartAll ptr round L1) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : M.accessible ptr round true = true) (h8 : ptr % 8 = 0) (hsz : 8 * (il + 1 + 4) ≤ round)
    (hw1h : Held R L1 w1 (8 * c1)) :
    UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 (L1 ++ [(ptr, ptr + round)]) ptr (il + 1 + 4) M := by
  have hl := hE.lay
  have hpre := hE.pre
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hpre.ce.2.2.2.2.2.1
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hil9 := hl.il9
  -- fresh ⇒ apart from anything held in `L1`
  have fr : ∀ p n, Held R L1 p n → Apart ptr (8 * (il + 1 + 4)) p n := by
    intro p n hh
    rcases hh with hi | ho
    · obtain ⟨r, hr, h1, h2⟩ := hi; have := hAp r hr; unfold Apart at this ⊢; omega
    · have := outside_of_inRanges ho hIn; unfold Apart; omega
  exact {
    cap := by omega, c40 := by omega, p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by omega, pg := by unfold Apart; omega,
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    ror := Or.inr ⟨hz, hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono (by omega) (Nat.le_refl _)⟩,
    pi := Or.inr (fr _ _ (hE.ext.held hpre.io.2.2.2.1)),
    pv := fr _ _ (hE.ext.held hpre.vo.2.2.2.1),
    pt := fr _ _ hl.theld,
    ps := fr _ _ (hE.ext.held hpre.sti.1.2.1),
    pz := fun h => fr _ _ (hE.ext.held (hpre.zo.2.1 h).2.1),
    pf := by have h1 := fr _ _ hw1h; have h2 := hE.c1len; unfold Apart at h1 ⊢; omega }

/-- reads of `S2.mem` (after `stk.nat`) at the frame slots: the prologue's values -/
theorem rdS2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} (hpre : Pre R b L c zp zc st up uc ip il vp vl s) {stkSN abSN : Nat} (hk1 : stkSN ≤ 4224)
    (hk2 : abSN ≤ 96) {P S2 : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hA : AfterNat R b L st vl s P S2 stkSN abSN L1 b1) (a n : Nat) (h1 : s.sp.toNat - 208 ≤ a)
    (h2 : a + n ≤ s.sp.toNat + 112) (h3 : a + n ≤ s.sp.toNat - 8 ∨ s.sp.toNat + 8 ≤ a) :
    S2.mem.readLE a n = P.mem.readLE a n := by
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  obtain ⟨hal, hb', ha, hw⟩ := hpre.ce.2.1
  have hsw := hpre.sti.2.1
  have hfw := hpre.fw
  simp only [win, outside_cons, outside_nil, and_true] at hsw hfw
  refine hA.F2.readLE a n ?_
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega⟩

/-- a range apart from the stack header and (when the stack has an array) from the whole array is outside the stack's
written ranges (`cap = 0` ⇒ `w = 0`, so the empty free part is the point `0`) -/
theorem outside_stkWs {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} (hpre : Pre R b L c zp zc st up uc ip il vp vl s) {a n : Nat} (h1 : Apart a n st 24)
    (h2 : 0 < stCap s.mem st → Apart a n (stW s.mem st) (8 * stCap s.mem st)) : Outside a n (stkWs s.mem st) := by
  have hlc := hpre.sti.1.2.2.2.2.2.1
  simp only [stkWs, outside_cons, outside_nil, and_true]
  unfold Apart at h1
  refine ⟨h1, ?_⟩
  by_cases hc : 0 < stCap s.mem st
  · have := h2 hc; unfold Apart at this; omega
  · have := hpre.w0 (by omega); rw [this]; omega

end FvModexp.Arm64.DivLarge
