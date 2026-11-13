import FvModexp.Proofs.Amd64.Nat.DivLargeRelB
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `divLarge` (amd64): the slot stores at `joinU` and the copy path's relations (pure)

`scrJ s`: the frame window minus `Mem`'s fixed slots (`- 209`, `- 168 … - 144`, `- 136 … - 120`, `- 96 … - 88`,
`- 40 … + 112`); it contains the `u` slots `- 200`, `- 184`, `- 104` and `shift` (`- 176`) that `joinU` stores
(`+0x216 … +0x22f`). `Mem.frameJ` = `Mem.frame` over `scrJ`; `MemU.ofJoin`: `Mem` + the four stores → `MemU`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

namespace FvModexp.Amd64.DivLarge

/-- the frame window without `Mem`'s fixed slots -/
@[reducible] def scrJ (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 41272, (s.regs 4).toNat - 209), ((s.regs 4).toNat - 208, (s.regs 4).toNat - 168),
    ((s.regs 4).toNat - 144, (s.regs 4).toNat - 136), ((s.regs 4).toNat - 120, (s.regs 4).toNat - 96),
    ((s.regs 4).toNat - 88, (s.regs 4).toNat - 40)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`Mem` across a frame inside `scrJ`** (pure; copy of `Mem.frame`) -/
theorem Mem.frameJ {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk P C : Nat}
    {M M' : Memory} {wS cS : Nat} (hM : Mem R L zp zc st up uc ip il vp vl s t wS cS Lk bk M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M)
    (hf : MemFrame M M' (R.rt ++ scrJ s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]))
    (hlf : LiveFrame M M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]))
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M')) :
    Mem R L zp zc st up uc ip il vp vl s t wS cS Lk' bk' M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have hpw := hU.pw
  -- a frame slot (outside the scratch) keeps its value
  have rdw : ∀ a n, (s.regs 4).toNat - 304 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → Outside a n (scrJ s) →
      M'.readLE a n = M.readLE a n := by
    intro a n h1 h2 h3
    refine hf.readLE _ _ (out4 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by have := hl.tw; omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega))
  have so : ∀ a, ((s.regs 4).toNat - 168 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 144) ∨
      ((s.regs 4).toNat - 136 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 120) ∨
      ((s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 88) ∨
      ((s.regs 4).toNat - 40 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 112) → Outside a 8 (scrJ s) := by
    intro a h; simp only [scrJ, outside_cons, outside_nil, and_true]; omega
  -- a held range outside the window and the written ranges keeps its value
  have hheld : ∀ a n, Held R L a n → (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      Outside a n (wsL zp zc up uc vl t) → (a + n ≤ P ∨ P + 8 * C ≤ a) → M'.readLE a n = M.readLE a n := by
    intro a n hh hw h1 h2
    rcases hh with hi | ho
    · exact hlf.readLE a n hi (by
        rw [outside_append]; exact ⟨h1, by simp only [outside_cons, outside_nil, and_true]; omega⟩)
    · exact hf.readLE a n (out4 ho (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega) h1 h2)
  have hsth : Held R L st 24 := hE.pre.sti.1.2.1
  have hsw : Outside st 24 (wsL zp zc up uc vl t) :=
    outside_wsL (by have := hl.ts; omega) (fun h => by have := hl.sz h; omega) (fun h => by have := hl.su h; omega)
  have hsP := hU.ps; unfold Apart at hsP
  have rdS : ∀ a, st ≤ a → a + 8 ≤ st + 24 → M'.readLE a 8 = M.readLE a 8 := fun a h1 h2 =>
    hheld _ _ (hsth.sub h1 h2) (by have := hl.sw; omega) (hsw.of_sub h1 h2) (by omega)
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22,
    mhw, mhl, mhc, mtls, mvs, mfr, mlf, -⟩ := hM
  have r8 : ∀ {x : Nat} (a : Nat), (s.regs 4).toNat - 304 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 → Outside a 8 (scrJ s) →
      M.readLE a 8 = x → M'.readLE a 8 = x := fun a h1 h2 h3 h => (rdw a 8 h1 h2 h3).trans h
  refine ⟨r8 _ (by omega) (by omega) (so _ (by omega)) m1, r8 _ (by omega) (by omega) (so _ (by omega)) m2,
    (rdw _ 1 (by omega) (by omega) (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega)).trans m3,
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
    rw [hf.readLE _ _ (out4 htr (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega) (tls_wsL hE)
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
    exact ⟨ho0, out4 hrt (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega) hws hP⟩
  · refine ⟨fun a n hin hws => ?_⟩
    rw [outside_append] at hws
    have hP := uarr_liveOut hE hU hin (wsL_parts hws.1).2.2
    rw [hlf.readLE a n hin (by
      rw [outside_append]; exact ⟨hws.1, by simp only [outside_cons, outside_nil, and_true]; omega⟩)]
    exact mlf.readLE a n hin (by rw [outside_append]; exact hws)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **the `joinU` stores** (pure): `Mem` + `UArr` at `M`, a frame inside `scrJ` writing `C, il + 1, P, sh` to the `u` /
`shift` slots → `MemU` + `UArr` at `M'` -/
theorem MemU.ofJoin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk P C sh : Nat}
    {M M' : Memory} {wS cS : Nat} (hM : Mem R L zp zc st up uc ip il vp vl s t wS cS Lk bk M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M) (hf : MemFrame M M' (scrJ s))
    (h1 : M'.readLE ((s.regs 4).toNat - 184) 8 = C) (h2 : M'.readLE ((s.regs 4).toNat - 200) 8 = il + 1)
    (h3 : M'.readLE ((s.regs 4).toNat - 104) 8 = P) (h4 : M'.readLE ((s.regs 4).toNat - 176) 8 = sh)
    (hg : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8) :
    MemU R L zp zc st up uc ip il vp vl s t wS cS Lk bk P C sh M' ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have hga := hE.pre.ce.2.2.2.2.2.1
  unfold Apart at hga
  have hf' : MemFrame M M' (R.rt ++ scrJ s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) :=
    hf.mono fun a n ho => by simp only [outside_append] at ho; exact ho.1.1.2
  have hlf : LiveFrame M M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) :=
    FvModexp.Expmc.liveFrame_of_frame hf fun a k hin _ => by
      obtain ⟨q, hq, hq1, hq2⟩ := hE.ext.inRanges_old hin
      have := hl.lsep q hq
      simp only [scrJ, outside_cons, outside_nil, and_true]; omega
  have hinv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk M') :=
    FvModexp.Expmc.inv_frame hf (fun r hr => by
      simp only [scrJ, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (hout.of_sub (by omega) (by omega))) hM.inv
  refine ⟨⟨Mem.frameJ hE hM hU hf' hlf hinv, h1, h2, h3, h4, ?_⟩, hU.frame fun a n w => hf.accessible a n w⟩
  rw [hf.readLE _ _ (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega)]
  exact hg

/-- `copy(v, vIn)`'s `memmove` return (`fn + 0x277`, `MOVQ 0xd0(SP), AX`) -/
abbrev cpRet1 : Nat := segAddr Extracted.program fn + 0x277

/-- the state after `copy(v, vIn)` (`shift = 0`): `v` (at `t`) = `vIn`, `u`'s slots stored (`shift` slot `0`) -/
structure AtV (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat) (S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 cpRet1
  sp : S.regs 4 = s.regs 4 - 304#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  mem : MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C 0 S.mem
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C S.mem
  ext2 : LiveExt R L1 Lk
  bud2 : b1 - makeCost (il + 1) ≤ bk
  vval : natVal S.mem t vl = natVal s.mem vp vl
  vtop : S.mem.readLE (t + 8 * (vl - 1)) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  is : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S.mem.readLE a n = s.mem.readLE a n
  reg : S.mem.regions = s.mem.regions

set_option maxRecDepth 20000 in
/-- **`MemU` across a runtime call** (pure): the callee's frame `cs` lies below `RSP - 209` (in `scrB`), its written
ranges `ext` inside the ranges `MemU` allows (`wsL`, `u`'s array) -/
theorem MemU.call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk Lk' : List (Nat × Nat)} {bk bk' P C sh : Nat}
    {M M2 : Memory} {wS cS : Nat} {cs ext : List (Nat × Nat)}
    (hM : MemU R L zp zc st up uc ip il vp vl s t wS cS Lk bk P C sh M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M) (hF : MemFrame M M2 (R.rt ++ cs ++ ext))
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 41272 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 209)
    (hext : ∀ a n, Outside a n (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) → Outside a n ext)
    (hLF : LiveFrame M M2 Lk ext) (hLL : ∀ a n, InRanges a n L → InRanges a n Lk)
    (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M2)) :
    MemU R L zp zc st up uc ip il vp vl s t wS cS Lk' bk' P C sh M2 ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M2 := by
  refine ⟨MemU.frame hE hM hU (hF.mono fun a n ho => ?_) ⟨fun a n hin hws => hLF.readLE a n (hLL a n hin) (hext a n hws)⟩
    hinv, hU.frame fun a n w => hF.accessible a n w⟩
  simp only [outside_append] at ho ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ho
  refine ⟨⟨h1, outside_of_forall fun r hr => ?_⟩, hext a n (by rw [outside_append]; exact ⟨h3, h4⟩)⟩
  have := hcs r hr
  simp only [scrB, outside_cons, outside_nil, and_true] at h2
  omega

end FvModexp.Amd64.DivLarge
