import FvModexp.Proofs.Arm64.Nat.RemDvPre
import FvModexp.Proofs.Arm64.Nat.RemFin
import FvModexp.Proofs.Common.ByteFrame

set_option autoImplicit false

/-!
# `nat.rem` (arm64): the postcondition `CPostR` from `div`'s `DivPostL` and the epilogue (pure)

States: entry `s`, `div`'s call state `X` (memory `M` after `stk.nat`, `SN`), `div`'s return `U` (live set `L2`, budget
`b2`), the final state `s'` (`fin`: `finW` written, `len(stk.w)` restored). Pieces: `post_stk` (the stack: `StackBackL`
and the `kept-or-fresh` fact), `post_fr` (memory / live frames), `post_val` (the result nat), `post` (assembly).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NatRem

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

/-- a held range outside the old free part is outside `q` and the new free part -/
theorem SN.outF {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st k : Nat} {s : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hN : SN R b L st k s M L1 b1) (hlc0 : stLen s.mem st ≤ stCap s.mem st)
    {a n : Nat} (hH : Held R L a n)
    (ho : Outside a n [(stW s.mem st + 8 * stLen s.mem st, stW s.mem st + 8 * stCap s.mem st)]) :
    Outside a n [(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * k),
      (stW M st + 8 * stLen M st, stW M st + 8 * stCap M st)] := by
  have hA : Apart a n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := by
    simp only [outside_cons, outside_nil, and_true] at ho; unfold Apart; omega
  have hlc := hN.sok.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := sub_F hN.len hlc (hN.regH hH hA)
  simp only [outside_cons, outside_nil, and_true]
  unfold Apart at h1 h2; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the stack at the end -/
theorem post_stk {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st k : Nat} {s : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hN : SN R b L st k s M L1 b1) {L2 : List (Nat × Nat)} {MU m' : Memory}
    (hx2 : LiveExt R L1 L2) (hsb : StackBackL R L1 L2 st M MU)
    (ew : stW m' st = stW MU st) (ec : stCap m' st = stCap MU st) (el : stLen m' st = stLen s.mem st)
    (hacc : ∀ a n w, m'.accessible a n w = MU.accessible a n w) :
    StackBackL R L L2 st s.mem m' ∧
      ((stW m' st = stW s.mem st ∧ stCap m' st = stCap s.mem st) ∨
        (InRanges (stW m' st) (8 * stCap m' st) R.rt ∧ ApartAll (stW m' st) (8 * stCap m' st) L)) := by
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, hlenU, hkfU⟩, harrU⟩ := hsb
  have hl := hN.len
  have hlcM := hN.sok.2.2.2.2.2.1
  have hkf : (stW m' st = stW s.mem st ∧ stCap m' st = stCap s.mem st) ∨
      (InRanges (stW m' st) (8 * stCap m' st) R.rt ∧ ApartAll (stW m' st) (8 * stCap m' st) L) := by
    rw [ew, ec]
    rcases hkfU with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]
      by_cases hg : stLen s.mem st + StackNat.rnd k ≤ stCap s.mem st
      · exact Or.inl (hN.kept hg)
      · exact Or.inr (hN.fresh (by omega))
    · exact Or.inr ⟨hin, fun q hq => hap q (hN.ext.mem_old hq)⟩
  have hA1 : ArrIn L1 st s.mem M := ArrIn.of_nat hlcM hl hN.kept hN.arrL
  have hA2 : ArrIn L2 st s.mem MU := ArrIn.trans hA1 harrU hx2
  refine ⟨⟨⟨⟨a1, a2, by rw [hacc]; exact a3, a4, ?_, ?_, by rw [ec]; exact a7⟩, el, hkf⟩,
    ArrIn.congr hA2 ew ec (fun _ h => h)⟩, hkf⟩
  · rw [ew, ec]; intro hc; obtain ⟨b1', b2', b3', b4'⟩ := a5 hc; exact ⟨b1', b2', by rw [hacc]; exact b3', b4'⟩
  · rw [el, ec]; rw [hlenU] at a6; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the memory and live frames from the entry to the end -/
theorem post_fr {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl : Nat} {s X : State} {M MU m' : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b cd L zp zl zc st up ul uc vp vl s) (hN : SN R b L st (kq ul vl) s M L1 b1)
    (hXsp : X.sp.toNat = s.sp.toNat - 208)
    (hMF2 : MemFrame M MU (R.rt ++ winA X 41504 112 ++
      [(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * kq ul vl), (zp, zp + 8 * zc)] ++ stWs M st))
    (hLF2 : LiveFrame M MU L1
      ([(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * kq ul vl), (zp, zp + 8 * zc)] ++ stWs M st))
    (hF3 : MemFrame MU m' (finW s st)) :
    MemFrame s.mem m' (R.rt ++ winA s 41712 112 ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem m' L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) := by
  obtain ⟨⟨⟨hce, -, -, -, -, -, -, -, hsok0, hsw, -, -, -, -, -, -, -, -, -, -, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, -, -, -, hLs, -⟩ := hce
  obtain ⟨-, -, -, -, -, hlc0, -⟩ := hsok0
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hfin : ∀ a n, Outside a n (winA s 41712 112) → a + n ≤ st ∨ st + 24 ≤ a → Outside a n (finW s st) := by
    intro a n h1 h2
    simp only [winA, finW, outside_cons, outside_nil, and_true] at h1 ⊢; omega
  refine ⟨MemFrame.trans (MemFrame.trans (rs'' := R.rt ++ winA s 41712 112 ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st)
    hN.mf hMF2 fun a n ho => ?_) hF3 fun a n ho => ?_, ⟨fun a n hin ho => ?_⟩⟩
  · rw [outside_append, outside_append, outside_append] at ho
    obtain ⟨⟨⟨hR, hW⟩, hZ⟩, hS⟩ := ho
    refine ⟨by rw [outside_append, outside_append]; exact ⟨⟨hR, hW⟩, hS⟩, ?_⟩
    have hq := hN.outF hlc0 (Or.inr hR) (by
      simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at hS ⊢; exact hS.2)
    rw [outside_append, outside_append, outside_append]
    refine ⟨⟨⟨hR, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨e1, e2, e3, e4⟩ := spW hXsp hb'
      simp only [winA, outside_cons, outside_nil, and_true] at hW ⊢; rw [e1, e2, e3, e4]; omega
    · simp only [outside_cons, outside_nil, and_true] at hq hZ ⊢; exact ⟨hq.1, hZ⟩
    · simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at hS hq ⊢; exact ⟨hS.1, hq.2⟩
  · refine ⟨ho, ?_⟩
    rw [outside_append, outside_append, outside_append] at ho
    obtain ⟨⟨⟨-, hW⟩, -⟩, hS⟩ := ho
    simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at hS
    exact hfin a n hW hS.1
  · rw [outside_append] at ho
    obtain ⟨hZ, hS⟩ := ho
    have hq := hN.outF hlc0 (Or.inl hin) (by
      simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at hS ⊢; exact hS.2)
    have h3 : Outside a n (finW s st) := by
      refine hfin a n ?_ ?_
      · obtain ⟨r, hr, h1, h2⟩ := hin
        have := hLs r hr
        simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega
      · simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at hS; exact hS.1
    rw [hF3.readLE a n h3, hLF2.readLE a n (hN.ext.inRanges_old hin) ?_, hN.lf.readLE a n hin hS]
    rw [outside_append]
    refine ⟨?_, ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at hq hZ ⊢; exact ⟨hq.1, hZ⟩
    · simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at hS hq ⊢; exact ⟨hS.1, hq.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the result nat -/
theorem post_val {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl : Nat} {s : State} {M MU m' : Memory} {L1 L2 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b cd L zp zl zc st up ul uc vp vl s) (hN : SN R b L st (kq ul vl) s M L1 b1)
    (hx2 : LiveExt R L1 L2) {r rl rc : Nat}
    (hr : NatOF R L1 L2 MU zp zc 1 r rl rc (natVal M up ul % natVal M vp vl))
    (hF3 : MemFrame MU m' (finW s st)) :
    NatOF R L L2 m' zp zc 1 r rl rc (natVal s.mem up ul % natVal s.mem vp vl) := by
  obtain ⟨eu, ev⟩ := uv_val hpre hN
  obtain ⟨⟨⟨hce, -, -, -, -, -, hzo, -, hsok0, hsw, -, -, -, -, -, -, -, hzst, -, -, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨-, hsth, -, -, -, -, -⟩ := hsok0
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  obtain ⟨hv, hnm, hlc, hc40, hlive, hloc⟩ := hr
  have hrO : 0 < rc → Outside r (8 * rc) (finW s st) := by
    intro hc
    rcases hloc with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
    · have h1 := (hzo.2.2 hc).1
      have h2 := (hzst hc).1
      simp only [win, finW, outside_cons, outside_nil, and_true] at h1 ⊢; unfold Apart at h2; omega
    · have h1 := InRanges.apart hin hout
      have h2 : Apart st 24 r (8 * rc) := by
        rcases hN.ext.held hsth with h | h
        · obtain ⟨q, hq, e1, e2⟩ := h
          have := hap q hq; unfold Apart at this ⊢; omega
        · exact InRanges.apart hin h
      simp only [finW, outside_cons, outside_nil, and_true]; unfold Apart at h1 h2; omega
  have hrd : ∀ a n, r ≤ a → a + n ≤ r + 8 * rl → 0 < n → m'.readLE a n = MU.readLE a n := fun a n h1 h2 h3 =>
    hF3.readLE a n ((hrO (by omega)).of_sub h1 (by omega))
  refine ⟨?_, ?_, hlc, hc40, fun hc => ?_, hloc.imp id fun ⟨a, b, c⟩ => ⟨a, b, fun q hq => c q (hN.ext.mem_old hq)⟩⟩
  · rw [← eu, ← ev, ← hv]
    rcases Nat.eq_zero_or_pos rl with h0 | h0
    · subst h0; simp only [natVal, Nat.mul_zero, Memory.readLE_zero]
    · exact hrd _ _ (Nat.le_refl _) (Nat.le_refl _) (by omega)
  · rcases hnm with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos rl with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h)
  · obtain ⟨a1, a2, a3, a4⟩ := hlive hc; exact ⟨a1, a2, by rw [hF3.accessible]; exact a3, a4⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`CPostR`** at the end -/
theorem post {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl : Nat} {s X : State} {M MU : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b cd L zp zl zc st up ul uc vp vl s) (hN : SN R b L st (kq ul vl) s M L1 b1)
    (hXm : X.mem = M) (hXsp : X.sp.toNat = s.sp.toNat - 208) (hX28 : X.regs 28 = s.regs 28)
    {r rl rc : Nat} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hr : NatOF R L1 L2 MU zp zc 1 r rl rc (natVal M up ul % natVal M vp vl))
    (hx2 : LiveExt R L1 L2) (hbud2 : b1 - cd (stLen M st) ul vl ≤ b2)
    (hinv2 : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 MU))
    (hsb : StackBackL R L1 L2 st M MU)
    (hfr : ¬ (r = zp ∧ rc = zc) → 0 < rc → 0 < stCap MU st → Apart r (8 * rc) (stW MU st) (8 * stCap MU st))
    (hMF2 : MemFrame M MU (R.rt ++ winA X 41504 112 ++
      [(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * kq ul vl), (zp, zp + 8 * zc)] ++ stWs M st))
    (hLF2 : LiveFrame M MU L1
      ([(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * kq ul vl), (zp, zp + 8 * zc)] ++ stWs M st))
    (s' : State) (hF3 : MemFrame MU s'.mem (finW s st)) (hlen3 : s'.mem.readLE (st + 8) 8 = stLen s.mem st)
    (h0 : s'.regs 0 = BitVec.ofNat 64 r) (h1 : s'.regs 1 = BitVec.ofNat 64 rl) (h2 : s'.regs 2 = BitVec.ofNat 64 rc) :
    CPostR R b L 41712 112 zp zc st (natVal s.mem up ul % natVal s.mem vp vl) (cost cd (stLen s.mem st) ul vl)
      s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hce, -, -, -, -, -, hzo, -, hsok0, hsw, -, -, -, -, -, -, -, -, -, -, -, -⟩, -⟩, -⟩ := hpre'
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨-, hsth, -, -, -, -, -⟩ := hsok0
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrdS : ∀ o, o + 8 ≤ 8 ∨ 16 ≤ o → o + 8 ≤ 24 → s'.mem.readLE (st + o) 8 = MU.readLE (st + o) 8 :=
    fun o h1 h2 => hF3.readLE _ _ (by simp only [finW, outside_cons, outside_nil, and_true]; omega)
  have ew : stW s'.mem st = stW MU st := by have := hrdS 0 (by omega) (by omega); simpa using this
  have ec : stCap s'.mem st = stCap MU st := hrdS 16 (by omega) (by omega)
  obtain ⟨hstk, hkf⟩ := post_stk hN hx2 hsb ew ec hlen3 hF3.accessible
  obtain ⟨hMF, hLF⟩ := post_fr hpre hN hXsp hMF2 hLF2 hF3
  have hl := hN.len
  refine ⟨r, rl, rc, h0, h1, h2, L2, b2, post_val hpre hN hx2 hr hF3, ⟨hN.ext.trans hx2, ?_, ?_⟩, hstk, hMF, hLF, ?_⟩
  · have := hN.bud; rw [hl] at hbud2; simp only [cost]; omega
  · refine RtInv.inv_frame' hF3 (fun q hq => ?_) hinv2
    simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · rcases (hN.ext.trans hx2).held hsth with h | h
      · right; exact h.sub (by simp only; omega) (by simp only; omega)
      · left; exact h.of_sub (by simp only; omega) (by simp only; omega)
  · intro hc hn
    by_cases hz : r = zp ∧ rc = zc
    · obtain ⟨rfl, rfl⟩ := hz
      exact ResSep.of_held hkf (hzo.2.1 hc).2.1 hc hn
    · have hcap := (hstk.2 hn).2
      rw [ec] at hcap; rw [ew, ec]
      exact hfr hz hc hcap

/-- an empty `z` range (`zc = 0`, `zp` arbitrary) in a frame can be moved to `0` (frames are byte-wise) -/
theorem dropZ {m m' : Memory} {A S : List (Nat × Nat)} {ql qh zp zc : Nat}
    (h : MemFrame m m' (A ++ [(ql, qh), (zp, zp + 8 * zc)] ++ S)) :
    MemFrame m m' (A ++ [(ql, qh), (if zc = 0 then 0 else zp, (if zc = 0 then 0 else zp) + 8 * zc)] ++ S) := by
  refine FvModexp.ByteFrame.MemFrame.mono1 h fun a ho => ?_
  rw [outside_append, outside_append] at ho ⊢
  obtain ⟨⟨hA, hB⟩, hS⟩ := ho
  refine ⟨⟨hA, ?_⟩, hS⟩
  simp only [outside_cons, outside_nil, and_true] at hB ⊢
  refine ⟨hB.1, ?_⟩
  by_cases hc : zc = 0
  · subst hc; omega
  · rw [if_neg hc] at hB; exact hB.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the frame slots and the guard word at `div`'s return -/
theorem atU {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl vc : Nat} {s X : State} {M MU : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : Pre R b cd L zp zl zc st up ul uc vp vl s) (hN : SN R b L st (kq ul vl) s M L1 b1)
    (hXsp : X.sp.toNat = s.sp.toNat - 208)
    (hMF2 : MemFrame M MU (R.rt ++ winA X 41504 112 ++
      [(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * kq ul vl), (zp, zp + 8 * zc)] ++ stWs M st))
    (hsl : Sl s zp zl zc st up ul uc vp vl vc M) :
    Sl s zp zl zc st up ul uc vp vl vc MU ∧
      MU.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
  have hO := hN.regO hpre
  obtain ⟨⟨⟨hce, -, -, -, -, -, hzo, -, hsok0, hsw, hsg, harr, hc0, -, -, -, -, -, -, -, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, hga, hgr, -, -⟩ := hce
  obtain ⟨-, -, -, -, -, hlc0, -⟩ := hsok0
  have hlc := hN.sok.2.2.2.2.2.1
  have hl := hN.len
  have hr := rnd_ge (kq ul vl)
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  obtain ⟨hO1, hO2, -⟩ := hO
  simp only [win, outside_cons, outside_nil, and_true] at hO1
  have hMF2z := dropZ hMF2
  -- every range inside the entry window is outside `div`'s writes
  have key : ∀ a n, (s.sp.toNat - 216 ≤ a ∧ a + n ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 96 ≤ a ∧
      a + n ≤ s.sp.toNat - 8) ∨ (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 88) →
      Outside a n (R.rt ++ winA X 41504 112 ++
        [(stW M st + 8 * stLen s.mem st, stW M st + 8 * stLen s.mem st + 8 * kq ul vl),
          (if zc = 0 then 0 else zp, (if zc = 0 then 0 else zp) + 8 * zc)] ++ stWs M st) := by
    intro a n h3
    have h1 : s.sp.toNat - 41712 ≤ a := by omega
    have h2 : a + n ≤ s.sp.toNat - 41712 + (41712 + 112) := by omega
    rw [outside_append, outside_append, outside_append]
    refine ⟨⟨⟨hout.of_sub h1 h2, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨e1, e2, e3, e4⟩ := spW hXsp hb'
      simp only [winA, outside_cons, outside_nil, and_true]; rw [e1, e2, e3, e4]; omega
    · simp only [outside_cons, outside_nil, and_true]
      refine ⟨by omega, ?_⟩
      by_cases hc : zc = 0
      · rw [if_pos hc]; omega
      · rw [if_neg hc]
        have := (hzo.2.2 (by omega)).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · simp only [stWs, stkWs, outside_cons, outside_nil, and_true]; omega
  refine ⟨hsl.frame hMF2z key (by omega), ?_⟩
  -- the guard word
  have hgM : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hN.mf.readLE _ _ ?_
    rw [outside_append, outside_append]
    refine ⟨⟨hgr, by simp only [winA, outside_cons, outside_nil, and_true]; unfold Apart at hga; omega⟩,
      out_stkWs hlc0 hsg.symm ?_⟩
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with hc | hc
    · rw [hc0 hc, hc]; unfold Apart; omega
    · have := (harr hc).2; unfold Apart at this ⊢; omega
  rw [← hgM]
  refine hMF2z.readLE _ _ ?_
  rw [outside_append, outside_append, outside_append]
  refine ⟨⟨⟨hgr, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := spW hXsp hb'
    simp only [winA, outside_cons, outside_nil, and_true]; rw [e1, e2, e3, e4]; unfold Apart at hga; omega
  · simp only [outside_cons, outside_nil, and_true]
    unfold Apart at hO2
    refine ⟨by omega, ?_⟩
    by_cases hc : zc = 0
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; have := (hzo.2.2 (by omega)).2; unfold Apart at this; omega
  · simp only [stWs, stkWs, outside_cons, outside_nil, and_true]; unfold Apart at hsg hO2; omega

end FvModexp.Arm64.NatRem
