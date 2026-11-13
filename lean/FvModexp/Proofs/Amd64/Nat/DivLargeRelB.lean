import FvModexp.Proofs.Amd64.Nat.DivLargeMem

set_option autoImplicit false

/-!
# `divLarge` (amd64): relations after `u.make` — `Mem.frame`, `MemU` (pure)

Port of the first part of `Arm64/Nat/DivLargeRelB.lean` (the alias point `AtA` follows in its own module).
`scrA s`: the frame slots written after `joinU` besides `Mem`'s and `u`'s (`RSP - 200` = `il + 1`, `- 184` = `C`,
`- 104` = `P`): everything below `RSP - 209` (callee frames, the return-address slot `RSP - 312`, the ABI0 argument
area `RSP - 304 … - 216`), `- 208`, `- 192`, the `shift` slot `- 176`, `- 144`, `- 120 … - 104`, `- 88 … - 40`
(from the stores of `nb-divLarge-amd64.dis` after `+0x216`). `scrB` = `scrA` without the `shift` slot.
`Mem.frame`: a frame `MemFrame M M' (R.rt ++ scrA s ++ wsL … ++ [u's array])` with a `LiveFrame` over the written
ranges keeps `Mem`. `MemU` = `Mem` + the slots of `u` (`P, il + 1, C`), `shift` and the stack-guard word.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

namespace FvModexp.Amd64.DivLarge

theorem outside_ar {a n p c : Nat} (h : 0 < c → a + n ≤ p ∨ p + 8 * c ≤ a) : Outside a n (ar p c) := by
  unfold ar; split
  · simp only [outside_cons, outside_nil, and_true]; next hc => exact h hc
  · trivial

theorem ar_out {a n p c : Nat} (h : Outside a n (ar p c)) (hc : 0 < c) : a + n ≤ p ∨ p + 8 * c ≤ a := by
  unfold ar at h; rw [if_pos hc] at h; simpa only [outside_cons, outside_nil, and_true] using h

theorem outside_wsL {a n zp zc up uc vl t : Nat} (ht : a + n ≤ t ∨ t + 8 * vl ≤ a)
    (hz : 0 < zc → a + n ≤ zp ∨ zp + 8 * zc ≤ a) (hu : 0 < uc → a + n ≤ up ∨ up + 8 * uc ≤ a) :
    Outside a n (wsL zp zc up uc vl t) := by
  simp only [wsL, outside_cons, outside_append]
  exact ⟨ht, outside_ar hz, outside_ar hu⟩

theorem wsL_parts {a n zp zc up uc vl t : Nat} (h : Outside a n (wsL zp zc up uc vl t)) :
    (a + n ≤ t ∨ t + 8 * vl ≤ a) ∧ Outside a n (ar zp zc) ∧ Outside a n (ar up uc) := by
  simp only [wsL, outside_cons, outside_append] at h; exact h

theorem out4 {a n p q : Nat} {rt sc w : List (Nat × Nat)} (h1 : Outside a n rt) (h2 : Outside a n sc)
    (h3 : Outside a n w) (h4 : a + n ≤ p ∨ q ≤ a) : Outside a n (rt ++ sc ++ w ++ [(p, q)]) := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- the frame slots written after `joinU` besides `Mem`'s and `u`'s (incl. `shift`'s) -/
@[reducible] def scrA (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 41272, (s.regs 4).toNat - 209), ((s.regs 4).toNat - 208, (s.regs 4).toNat - 200),
    ((s.regs 4).toNat - 192, (s.regs 4).toNat - 184), ((s.regs 4).toNat - 176, (s.regs 4).toNat - 168),
    ((s.regs 4).toNat - 144, (s.regs 4).toNat - 136), ((s.regs 4).toNat - 120, (s.regs 4).toNat - 104),
    ((s.regs 4).toNat - 88, (s.regs 4).toNat - 40)]

/-- `scrA` without the `shift` slot -/
@[reducible] def scrB (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 41272, (s.regs 4).toNat - 209), ((s.regs 4).toNat - 208, (s.regs 4).toNat - 200),
    ((s.regs 4).toNat - 192, (s.regs 4).toNat - 184),
    ((s.regs 4).toNat - 144, (s.regs 4).toNat - 136), ((s.regs 4).toNat - 120, (s.regs 4).toNat - 104),
    ((s.regs 4).toNat - 88, (s.regs 4).toNat - 40)]

/-- `u`'s array is old (`up`) or fresh: outside the old ranges -/
theorem uarr_out {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1)
    {Lk : List (Nat × Nat)} {P C : Nat} {M : Memory} (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    {a n : Nat} (h1 : Outside a n R.rt) (h2 : Outside a n (ar up uc)) : a + n ≤ P ∨ P + 8 * C ≤ a := by
  rcases hU.ror with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
  · exact ar_out h2 (by have := hU.cap; omega)
  · exact outside_of_inRanges h1 hin

theorem uarr_liveOut {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1)
    {Lk : List (Nat × Nat)} {P C : Nat} {M : Memory} (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    {a n : Nat} (hin : InRanges a n L) (h2 : Outside a n (ar up uc)) : a + n ≤ P ∨ P + 8 * C ≤ a := by
  rcases hU.ror with ⟨rfl, rfl⟩ | ⟨-, -, hap⟩
  · exact ar_out h2 (by have := hU.cap; omega)
  · obtain ⟨r, hr, i1, i2⟩ := hin
    have := hap r (hE.ext.mem_old hr); unfold Apart at this; omega

/-- the stack guard word is outside the written ranges -/
theorem g_wsL {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) :
    Outside ((s.regs 14).toNat + 16) 8 (wsL zp zc up uc vl t) := by
  have hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.2.1
  refine outside_wsL ?_ (fun h => by have := (hE.pre.zo.2.2 h).2.1; unfold Apart at this; omega)
    (fun h => by have := (hE.pre.uo.2.2 h).2.1; unfold Apart at this; omega)
  rcases hE.scr.loc with ⟨hc, h1, h2⟩ | ⟨hin, -⟩
  · have := (hE.pre.sti.2.2.2 hc).2; unfold Apart at this; omega
  · have := outside_of_inRanges hgr hin; omega

/-- the TLS word (`g`) is outside the written ranges -/
theorem tls_wsL {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) :
    Outside (s.fsBase.toNat - 8) 8 (wsL zp zc up uc vl t) := by
  have htr : Outside (s.fsBase.toNat - 8) 8 R.rt := hE.pre.ce.2.2.2.2.2.2.2.2.2.2.1
  refine outside_wsL ?_ (fun h => by have := (hE.pre.zo.2.2 h).2.2; unfold Apart at this; omega)
    (fun h => by have := (hE.pre.uo.2.2 h).2.2; unfold Apart at this; omega)
  rcases hE.scr.loc with ⟨hc, h1, h2⟩ | ⟨hin, -⟩
  · have := hE.pre.stft; have hlc := hE.pre.sti.1.2.2.2.2.2.1; unfold Apart at this; omega
  · have := outside_of_inRanges htr hin; omega

/-- the live set after `u.make` is apart from the frame window -/
theorem lsep_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} (hx : LiveExt R L1 Lk) :
    ∀ r ∈ Lk, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ r.1 := by
  have hl := hE.lay
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  rcases hx with ⟨ns, rfl, hn, -⟩
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hl.lsep r hr
  · have := outside_of_inRanges hout (hn r hr).1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`Mem` across a frame** (pure) -/
theorem Mem.frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk P C : Nat}
    {M M' : Memory} {wS cS : Nat} (hM : Mem R L zp zc st up uc ip il vp vl s t wS cS Lk bk M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    (hf : MemFrame M M' (R.rt ++ scrA s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]))
    (hlf : LiveFrame M M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]))
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M')) :
    Mem R L zp zc st up uc ip il vp vl s t wS cS Lk' bk' M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have hpw := hU.pw
  -- a frame slot (outside the scratch) keeps its value
  have rdw : ∀ a n, (s.regs 4).toNat - 304 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → Outside a n (scrA s) →
      M'.readLE a n = M.readLE a n := by
    intro a n h1 h2 h3
    refine hf.readLE _ _ (out4 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by have := hl.tw; omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega))
  have so : ∀ a, ((s.regs 4).toNat - 168 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 144) ∨
      ((s.regs 4).toNat - 136 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 120) ∨
      ((s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 88) ∨
      ((s.regs 4).toNat - 40 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 112) → Outside a 8 (scrA s) := by
    intro a h; simp only [scrA, outside_cons, outside_nil, and_true]; omega
  -- a held range outside the window and the written ranges keeps its value
  have hheld : ∀ a n, Held R L a n → (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      Outside a n (wsL zp zc up uc vl t) → (a + n ≤ P ∨ P + 8 * C ≤ a) → M'.readLE a n = M.readLE a n := by
    intro a n hh hw h1 h2
    rcases hh with hi | ho
    · exact hlf.readLE a n hi (by
        rw [outside_append]; exact ⟨h1, by simp only [outside_cons, outside_nil, and_true]; omega⟩)
    · exact hf.readLE a n (out4 ho (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) h1 h2)
  have hsth : Held R L st 24 := hE.pre.sti.1.2.1
  have hsw : Outside st 24 (wsL zp zc up uc vl t) :=
    outside_wsL (by have := hl.ts; omega) (fun h => by have := hl.sz h; omega) (fun h => by have := hl.su h; omega)
  have hsP := hU.ps; unfold Apart at hsP
  have rdS : ∀ a, st ≤ a → a + 8 ≤ st + 24 → M'.readLE a 8 = M.readLE a 8 := fun a h1 h2 =>
    hheld _ _ (hsth.sub h1 h2) (by have := hl.sw; omega) (hsw.of_sub h1 h2) (by omega)
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22,
    mhw, mhl, mhc, mtls, mvs, mfr, mlf, -⟩ := hM
  have r8 : ∀ {x : Nat} (a : Nat), (s.regs 4).toNat - 304 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 → Outside a 8 (scrA s) →
      M.readLE a 8 = x → M'.readLE a 8 = x := fun a h1 h2 h3 h => (rdw a 8 h1 h2 h3).trans h
  refine ⟨r8 _ (by omega) (by omega) (so _ (by omega)) m1, r8 _ (by omega) (by omega) (so _ (by omega)) m2,
    (rdw _ 1 (by omega) (by omega) (by simp only [scrA, outside_cons, outside_nil, and_true]; omega)).trans m3,
    r8 _ (by omega) (by omega) (so _ (by omega)) m4, r8 _ (by omega) (by omega) (so _ (by omega)) m5,
    r8 _ (by omega) (by omega) (so _ (by omega)) m6, r8 _ (by omega) (by omega) (so _ (by omega)) m7,
    r8 _ (by omega) (by omega) (so _ (by omega)) m8, r8 _ (by omega) (by omega) (so _ (by omega)) m9,
    r8 _ (by omega) (by omega) (so _ (by omega)) m10, r8 _ (by omega) (by omega) (so _ (by omega)) m11,
    r8 _ (by omega) (by omega) (so _ (by omega)) m12, r8 _ (by omega) (by omega) (so _ (by omega)) m13,
    r8 _ (by omega) (by omega) (so _ (by omega)) m14, r8 _ (by omega) (by omega) (so _ (by omega)) m15,
    r8 _ (by omega) (by omega) (so _ (by omega)) m16, r8 _ (by omega) (by omega) (so _ (by omega)) m17,
    r8 _ (by omega) (by omega) (so _ (by omega)) m18, r8 _ (by omega) (by omega) (so _ (by omega)) m19,
    r8 _ (by omega) (by omega) (so _ (by omega)) m20, r8 _ (by omega) (by omega) (so _ (by omega)) m21,
    r8 _ (by omega) (by omega) (so _ (by omega)) m22,
    (rdS _ (by omega) (by omega)).trans mhw, (rdS _ (by omega) (by omega)).trans mhl,
    (rdS _ (by omega) (by omega)).trans mhc, ?_, ?_, ?_, ?_, hinv⟩
  · obtain ⟨-, htr, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
    have hpt := hU.pt
    unfold Apart at htw hpt
    rw [hf.readLE _ _ (out4 htr (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) (tls_wsL hE)
      (by omega))]
    exact mtls
  · intro a n h1 h2
    rw [hheld a n (hE.pre.vo.2.2.2.1.sub h1 h2) (by have := hl.vw; omega) ?_ ?_]
    · exact mvs a n h1 h2
    · exact outside_wsL (by have := hl.tv; omega) (fun h => by have := hl.zv h; omega)
        (fun h => by have := hl.uv h; omega)
    · have := hU.pv; unfold Apart at this; omega
  · refine (mfTrans mfr hf).mono fun a n ho => ?_
    have ho0 := ho
    simp only [outside_append] at ho
    obtain ⟨⟨⟨hrt, hwa⟩, hws⟩, -⟩ := ho
    simp only [win, outside_cons, outside_nil, and_true] at hwa
    have hP := uarr_out hE hU hrt (wsL_parts hws).2.2
    rw [outside_append]
    exact ⟨ho0, out4 hrt (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) hws hP⟩
  · refine ⟨fun a n hin hws => ?_⟩
    rw [outside_append] at hws
    have hP := uarr_liveOut hE hU hin (wsL_parts hws.1).2.2
    rw [hlf.readLE a n hin (by
      rw [outside_append]; exact ⟨hws.1, by simp only [outside_cons, outside_nil, and_true]; omega⟩)]
    exact mlf.readLE a n hin (by rw [outside_append]; exact hws)

/-- `Mem` plus the slots of `u` (`P` at `RSP - 104`, `il + 1` at `- 200`, `C` at `- 184`), `shift` (`- 176`) and the
stack-guard word -/
structure MemU (R : RtInv) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat) (M : Memory) : Prop where
  mem : Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk M
  sC : M.readLE ((s.regs 4).toNat - 184) 8 = C
  sL : M.readLE ((s.regs 4).toNat - 200) 8 = il + 1
  sP : M.readLE ((s.regs 4).toNat - 104) 8 = P
  ssh : M.readLE ((s.regs 4).toNat - 176) 8 = sh
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8

set_option maxRecDepth 20000 in
theorem MemU.frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk P C sh : Nat}
    {M M' : Memory} {wS cS : Nat} (hM : MemU R L zp zc st up uc ip il vp vl s t wS cS Lk bk P C sh M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    (hf : MemFrame M M' (R.rt ++ scrB s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]))
    (hlf : LiveFrame M M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]))
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M')) :
    MemU R L zp zc st up uc ip il vp vl s t wS cS Lk' bk' P C sh M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have hpw := hU.pw
  have rdw : ∀ a, (s.regs 4).toNat - 200 ≤ a → a + 8 ≤ (s.regs 4).toNat - 96 → Outside a 8 (scrB s) →
      M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    refine hf.readLE _ _ (out4 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by have := hl.tw; omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega))
  refine ⟨Mem.frame hE hM.mem hU (hf.mono fun a n ho => ?_) hlf hinv,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.sC,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.sL,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.sP,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.ssh, ?g⟩
  case g =>
    have hga := hE.pre.ce.2.2.2.2.2.1; have hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.2.1
    have hpg := hU.pg
    unfold Apart at hga hpg
    rw [hf.readLE _ _ (out4 hgr (by simp only [scrB, outside_cons, outside_nil, and_true]; omega) (g_wsL hE) (by omega))]
    exact hM.grd
  simp only [outside_append] at ho ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ho
  refine ⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩
  simp only [scrA, scrB, outside_cons, outside_nil, and_true] at h2 ⊢
  omega

theorem UArr.frame {R : RtInv} {zp zc st up uc ip il vp vl : Nat} {s : State} {t w1 c1 : Nat}
    {L1 Lk : List (Nat × Nat)} {P C : Nat} {M M' : Memory} (h : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) :
    UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M' :=
  { h with pacc := by rw [hacc]; exact h.pacc }

theorem UArr.live {R : RtInv} {zp zc st up uc ip il vp vl : Nat} {s : State} {t w1 c1 : Nat}
    {L1 Lk Lk' : List (Nat × Nat)} {P C : Nat} {M : Memory} (h : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    (hx : LiveExt R Lk Lk') : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk' P C M :=
  { h with pheld := hx.held h.pheld }

end FvModexp.Amd64.DivLarge
