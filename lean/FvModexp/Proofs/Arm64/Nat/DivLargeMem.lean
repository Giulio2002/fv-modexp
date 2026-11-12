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
  simp only [EvenHyp.StkApart] at hsz hsu hsi hsv
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
      have := hfree zp (8 * zc) (hheld _ _ (hzl h).2.1) (fun _ h2 => (hsz (by omega)).2 h2) (by omega)
      unfold Apart at this; omega,
    tu := fun h => by
      have := hfree up (8 * uc) (hheld _ _ (hul h).2.1) (fun _ h2 => (hsu (by omega)).2 h2) (by omega)
      unfold Apart at this; omega,
    ti := by
      have := hfree ip (8 * il) (hheld _ _ hih) (fun _ h2 => (hsi (by omega)).2 h2) (by omega)
      unfold Apart at this; omega,
    tv := by
      have := hfree vp (8 * vl) (hheld _ _ hvh) (fun _ h2 => (hsv (by omega)).2 h2) (by omega)
      unfold Apart at this; omega,
    ts := by
      rcases hscr.loc with ⟨hc0, hl1, hl2⟩ | ⟨hin, hap⟩
      · have := hpre.hf; unfold Apart at this; omega
      · rcases hsth with hi | ho
        · obtain ⟨r, hr, h1, h2⟩ := hi; have := hap r hr; unfold Apart at this; omega
        · have := outside_of_inRanges ho hin; omega,
    sz := fun h => by have := (hsz (by omega)).1; unfold Apart at this; omega,
    su := fun h => by have := (hsu (by omega)).1; unfold Apart at this; omega,
    si := by
      by_cases h0 : il = 0
      · subst h0; omega
      · have := (hsi (by omega)).1; unfold Apart at this; omega,
    sv := by have := (hsv (by omega)).1; unfold Apart at this; omega,
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

end FvModexp.Arm64.DivLarge
