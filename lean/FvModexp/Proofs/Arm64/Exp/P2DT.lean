import FvModexp.Proofs.Arm64.Exp.P2DDefs
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): transport of the entry facts to a callee one frame down, and back (agent infra)

Frame facts `FrS s M`: `M` is the entry memory changed only in the runtime ranges and the part `winA s stk A` of the
entry window (own frame: saved FP/LR at `SP - 120`/`SP - 112`, spills above `SP`), live objects untouched.
* `cpre_sub`: `NHyp.CPre` at a callee entry `S` (`SP_S = SP - 112`, window `[SP_S - stk', SP_S + A')` inside ours)
  from the entry `NHyp.CPre` (the inputs supplied separately: `in_sub` for an entry input);
* `cpost_pre`: a callee's `NHyp.CPostR` (relative to `S`) is ours (relative to the entry `s`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

/-- the ranges the function itself may write (inside the entry window, without the caller's FP/LR words) -/
@[reducible] def ownW (s : State) (stk A : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - stk, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + A)]

theorem hdr_eq {R : RtInv} {L : List (Nat × Nat)} {st : Nat} {m M : Memory} {ws : List (Nat × Nat)}
    (hH : Held R L st 24) (hF : MemFrame m M (R.rt ++ ws)) (hLF : LiveFrame m M L []) (ho : Outside st 24 ws) :
    stW M st = stW m st ∧ stLen M st = stLen m st ∧ stCap M st = stCap m st := by
  have rd : ∀ o, o + 8 ≤ 24 → M.readLE (st + o) 8 = m.readLE (st + o) 8 := fun o hlt =>
    (hH.sub (by omega) (by omega)).readLE hF (LiveFrame.of_nil' hLF ws) (ho.of_sub (by omega) (by omega))
  exact ⟨by have := rd 0 (by omega); simpa using this, rd 8 (by omega), rd 16 (by omega)⟩

/-- a read through a frame whose ranges are each empty or apart from the read -/
theorem rd_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a k : Nat}
    (ho : ∀ r ∈ rs, r.2 ≤ r.1 ∨ a + k ≤ r.1 ∨ r.2 ≤ a) : m'.readLE a k = m.readLE a k := by
  refine Memory.readLE_congr fun j hj => ?_
  have h1 := h.readLE (a + j) 1 (outside_of_forall fun r hr => by
    rcases ho r hr with q | q | q <;> omega)
  simp only [Memory.readLE_one] at h1
  exact BitVec.eq_of_toNat_eq h1

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s S : State}

theorem win_out {a k stk' A' : Nat} (h : Outside a k (win s stk A)) (hSsp : S.sp.toNat + 112 = s.sp.toNat)
    (hk : stk' + 112 ≤ stk) (hA : A' ≤ 104) : Outside a k (win S stk' A') := by
  simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- an entry input's facts at the callee entry -/
theorem in_sub (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {p n : Nat} (hpn : (p, n) ∈ ins)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1)
    (hSsp : S.sp.toNat + 112 = s.sp.toNat) {stk' A' : Nat} (hk : stk' + 112 ≤ stk) (hA : A' ≤ 104) :
    RdIn R L1 S stk' A' p n ∧ n ≤ 2 ^ 9 ∧ NatNorm S.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (NHyp.freeOf S.mem st).1 (NHyp.freeOf S.mem st).2 ∧ (0 < zc → Apart zp (8 * zc) p (8 * n)) := by
  obtain ⟨-, -, -, -, -, -, -, hins, hsok, hstw, -⟩ := hP
  obtain ⟨⟨h40, hacc, h48, hH, hw⟩, hn, hN, hst, hfr, hz⟩ := hins p n hpn
  have ho : ∀ {a k : Nat}, Outside a k (win s stk A) → Outside a k (ownW s stk A) := fun h => by
    simp only [win, ownW, outside_cons, outside_nil, and_true] at h ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF (ho hstw)
  refine ⟨⟨h40, by rw [hF.accessible]; exact hacc, h48, hx.held hH, win_out hw hSsp hk hA⟩, hn, ?_, hst, ?_, hz⟩
  · rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · exact Or.inl hn0
    rcases hN with h0 | h1
    · exact Or.inl h0
    · right
      rw [(hH.sub (a := p + 8 * (n - 1)) (n := 8) (by omega) (by omega)).readLE hF (LiveFrame.of_nil' hLF _)
        (ho (hw.of_sub (by omega) (by omega)))]; exact h1
  · show Apart p (8 * n) (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`NHyp.CPre` at a callee entry one frame down** (inputs supplied) -/
theorem cpre_sub (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    (hrg : S.mem.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} {b1 : Nat} (hx : LiveExt R L L1)
    (hinv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S.mem))
    (hSsp : S.sp.toNat + 112 = s.sp.toNat) (h28 : S.regs 28 = s.regs 28) {stk' A' : Nat}
    (hk : stk' + 112 ≤ stk) (hA : A' ≤ 104) {ins' : List (Nat × Nat)} {need' cst' : Nat}
    (hins : ∀ p n, (p, n) ∈ ins' → RdIn R L1 S stk' A' p n ∧ n ≤ 2 ^ 9 ∧ NatNorm S.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (NHyp.freeOf S.mem st).1 (NHyp.freeOf S.mem st).2 ∧ (0 < zc → Apart zp (8 * zc) p (8 * n)))
    (hneed : stLen s.mem st + need' ≤ 2 ^ 16) (hcst : cst' ≤ b1) :
    NHyp.CPre R b1 L1 stk' A' zp zl zc st ins' need' cst' S := by
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, hd, hwrt, hgw, hgrt, hLs, hro'⟩, hsv, hgl, hro, hwT, hzl, hwo, -,
    hsok, hstw, hstg, harr, hcap0, -, hwba, hstwb, hstf, hzs, hstgA, hfgA, -, -⟩ := hP
  have hSg : (S.regs 28).toNat = (s.regs 28).toNat := by rw [h28]
  generalize hSP : s.sp.toNat = SP at *
  have ho : ∀ {a k : Nat}, Outside a k (win s stk A) → Outside a k (ownW s stk A) := fun h => by
    simp only [win, ownW, outside_cons, outside_nil, and_true, hSP] at h ⊢; omega
  have hwin : ∀ {a k : Nat}, Outside a k (win s stk A) → Outside a k (win S stk' A') := fun h =>
    win_out h (by rw [hSP]; exact hSsp) hk hA
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF (ho hstw)
  have hgow : Outside ((s.regs 28).toNat + 16) 8 (ownW s stk A) := by
    simp only [ownW, outside_cons, outside_nil, and_true, hSP]; unfold Apart at hgw; omega
  have hgM : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hgow⟩)
  have hgl' : RunIface.Globals R S.mem (win S stk' A') := by
    obtain ⟨q40, q12, q80, q40', e8, e16, e24, hgacc, hgrt', hgw', hwbacc, hwbrt, hwbw⟩ := hgl
    have hgA : Outside RunIface.gA 32 (R.rt ++ ownW s stk A) := by rw [outside_append]; exact ⟨hgrt', ho hgw'⟩
    have hrd : ∀ k, k + 8 ≤ 32 → S.mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 := fun k hk =>
      hF.readLE _ _ (hgA.of_sub (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, (hF.accessible _ _ _).trans hgacc, hgrt', hwin hgw',
      (hF.accessible _ _ _).trans hwbacc, hwbrt, hwin hwbw⟩
    · rw [e8, hrd 8 (by omega), ← e8]; exact q40
    · rw [e16, hrd 16 (by omega), ← e16]; exact q12
    · rw [e24, hrd 24 (by omega), ← e24]; exact q80
    · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
      show S.mem.readLE RunIface.gA 8 = 40; rw [this]; exact q40'
  have hout : Outside (SP - stk) (stk + A) R.rt := hwrt
  obtain ⟨hz40, hzL, hzW⟩ := hwo
  refine ⟨⟨⟨by rw [hSg]; exact g1, by rw [hSg, hF.accessible]; exact g2, by rw [hSg, hgM]; omega⟩,
      ⟨by omega, by omega, by omega, by
        rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)⟩,
      dataLoaded_frame hd hrg hro hF (fun r hr _ => by
        simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)),
      hout.of_sub (by omega) (by omega), by rw [hSg]; unfold Apart at hgw ⊢; omega, by rw [hSg]; exact hgrt, ?_, hro'⟩,
    hsv, hgl', hro, hwT, hzl, ⟨hz40, fun hc => ?_, fun hc => ?_⟩, hins, stkOK_hdr hsok hF ew el ec hx, hwin hstw,
    by rw [hSg]; exact hstg, ?_, by rw [ec, ew]; exact hcap0, by rw [el]; exact hneed,
    by rw [hF.accessible]; exact hwba, hstwb, ?_, fun hc => ?_, hstgA, ?_, hcst, by rw [hSg]; exact hinv⟩
  · refine hx.liveSep (LiveSep.sub_win hLs (by omega) (by omega)) fun r hr => ?_
    simp only [win, List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)
  · obtain ⟨a1, a2, a3, a4⟩ := hzL hc
    exact ⟨a1, hx.held a2, by rw [hF.accessible]; exact a3, a4⟩
  · obtain ⟨a1, a2⟩ := hzW hc
    exact ⟨hwin a1, by rw [hSg]; exact a2⟩
  · rw [ec, ew, hSg]; intro hc
    obtain ⟨a1, a2⟩ := harr hc
    exact ⟨hwin a1, a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hstf
  · obtain ⟨a1, a2, a3⟩ := hzs hc
    refine ⟨a1, ?_, a3⟩
    show Apart zp (8 * zc) (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact a2
  · show Apart (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st)) RunIface.gA 32
    rw [ew, el, ec]; exact hfgA

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **a callee's exit facts one frame down are ours** -/
theorem cpost_pre (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} {b1 : Nat} (hx : LiveExt R L L1)
    (hSsp : S.sp.toNat + 112 = s.sp.toNat) (h28 : S.regs 28 = s.regs 28) {stk' A' : Nat}
    (hk : stk' + 112 ≤ stk) (hA : A' ≤ 104) {v cst' : Nat} (hb : b - cst ≤ b1 - cst')
    {S' s' : State} (hq : NHyp.CPostR R b1 L1 stk' A' zp zc st v cst' S S')
    (hm : s'.mem = S'.mem) (e0 : s'.regs 0 = S'.regs 0) (e1 : s'.regs 1 = S'.regs 1) (e2 : s'.regs 2 = S'.regs 2) :
    NHyp.CPostR R b L stk A zp zc st v cst s s' := by
  have hsok := hP.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.1
  have ho : ∀ {a k : Nat}, Outside a k (win s stk A) → Outside a k (ownW s stk A) := fun h => by
    simp only [win, ownW, outside_cons, outside_nil, and_true] at h ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF (ho hstw)
  obtain ⟨p, l, c, q0, q1, q2, L', b', ⟨hv, hn, hlc, hc40, hlive, hor⟩, ⟨hx', hb', hinv⟩, ⟨⟨hsk, hsl, hkf⟩, hai⟩,
    hF', hLF', hrs⟩ := hq
  have hsub : ∀ {a k : Nat}, ApartAll a k L1 → ApartAll a k L := fun h r hr => h r (hx.mem_old hr)
  refine ⟨p, l, c, e0.trans q0, e1.trans q1, e2.trans q2, L', b', ?_, ⟨hx.trans hx', by omega, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    refine ⟨hv, hn, hlc, hc40, hlive, hor.imp id fun h => ⟨h.1, h.2.1, hsub h.2.2⟩⟩
  · rw [hm, ← h28]; exact hinv
  · rw [hm]
    refine ⟨⟨hsk, by rw [hsl, el], ?_⟩, ?_⟩
    · rw [ew, ec] at hkf; exact hkf.imp id fun h => ⟨h.1, hsub h.2⟩
    · intro hn'; apply hai; rw [ew, ec]; exact hn'
  · rw [hm]
    have es : stWs S.mem st = stWs s.mem st := by unfold stWs stkWs; rw [ew, el, ec]
    rw [es] at hF'
    refine hF.trans hF' fun a k hok => ?_
    simp only [winA, ownW, outside_append, outside_cons, outside_nil, and_true] at hok ⊢
    refine ⟨⟨hok.1.1.1, by omega, by omega⟩, ⟨⟨hok.1.1.1, by omega, by omega⟩, hok.1.2⟩, hok.2⟩
  · rw [hm]
    refine (LiveFrame.of_nil' hLF _).trans ?_ fun a k h => hx.inRanges_old h
    simp only [stWs, stkWs, ew, el, ec] at hLF'
    exact hLF'
  · rw [hm]; exact hrs.pre ew ec

end

end FvModexp.Arm64.P2D
