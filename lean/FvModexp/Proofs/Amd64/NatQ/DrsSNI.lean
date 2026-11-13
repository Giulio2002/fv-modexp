import FvModexp.Proofs.Amd64.NatQ.DrsSNP

set_option autoImplicit false

/-! (amd64 twin of Arm64/NatQ/DrsSNI.lean, asm s45)
# `divRecursiveStep` (amd64), big path: the facts after `qhat0 := stk.nat(B + 1)` (pure)

`hd_mem`: from the entry pre, the frame of the prologue (`fw s`) and `(*stack).nat`'s `PostQ` (callee entry state `X`,
`RSP = r - 400`, window `4192 / 24`; return memory `T`): `Cr`, `Ev`, `Fp` at the stack length `l1`, and `z`, `u`, `v`
unchanged since the entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 32000000 in
theorem hd_mem {R : RtInv} {c : Cx} {s X : State} {T : Memory} {bk : Nat}
    (hpre : DrsPreW R c.b c.L c.Hq (drsCQ c.ul c.vl) c.W c.qp c.ql c.qc c.st c.up c.ul c.uc c.vp c.vl
      c.vc s)
    (ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (x15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hW : drsW64 c.vl ≤ c.W) (h40 : 40 ≤ c.vl) (hvu : c.vl ≤ c.u1) (hu1 : c.u1 ≤ c.ul)
    (hU : natVal s.mem c.up c.u1 = natVal s.mem c.up c.ul) (hN : NatNorm s.mem c.up c.u1)
    (hMF : MemFrame X.mem T (R.rt ++ win X 4192 24 ++ stkWs X.mem c.st))
    (hLF : LiveFrame X.mem T c.L (stkWs X.mem c.st))
    (hF0 : MemFrame s.mem X.mem (fw s)) (hspX : (X.regs 4).toNat = (s.regs 4).toNat - 400)
    (ht0 : c.t0 = stW T c.st + 8 * stLen s.mem c.st)
    (hext : LiveExt R c.L c.L1) (hinv : R.inv bk c.L1 (s.regs 14).toNat (view R.rt c.L1 T))
    (hok : StkOK T R c.L1 c.st) (hlen : stLen T c.st = stLen X.mem c.st + StackNat.rnd (c.vl / 2 + 1))
    (hsame : stLen X.mem c.st + StackNat.rnd (c.vl / 2 + 1) ≤ stCap X.mem c.st →
      stW T c.st = stW X.mem c.st ∧ stCap T c.st = stCap X.mem c.st)
    (hgrow : stCap X.mem c.st < stLen X.mem c.st + StackNat.rnd (c.vl / 2 + 1) →
      InRanges (stW T c.st) (8 * stCap T c.st) R.rt ∧ ApartAll (stW T c.st) (8 * stCap T c.st) c.L)
    (hmem : stCap X.mem c.st < stLen X.mem c.st + StackNat.rnd (c.vl / 2 + 1) →
      (stW T c.st, stW T c.st + 8 * stCap T c.st) ∈ c.L1)
    (hreg : T.regions = s.mem.regions) :
    Cr R c s ∧ Ev R c s c.L1 bk T ∧ Fp R c s c.L1 T (c.l1 s) ∧
      (∀ x k, Held R c.L x k → Outside x k (win s c.W 96) → Apart x k c.st 24 →
        Apart x k (stW s.mem c.st + 8 * stLen s.mem c.st) (8 * (stCap s.mem c.st - stLen s.mem c.st)) →
        T.readLE x k = s.mem.readLE x k) := by
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, hLs, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, hqh, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvw, -, -, -⟩ := hpre.va
  obtain ⟨hsok, hsto, -, -⟩ := hpre.sti
  have hWg := drsW64_ge c.vl
  -- the header is untouched by the prologue
  have hst : Outside c.st 24 (fw s) := by
    simp only [win, fw, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have eW : stW X.mem c.st = stW s.mem c.st := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eL : stLen X.mem c.st = stLen s.mem c.st := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap X.mem c.st = stCap s.mem c.st := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eWs : stkWs X.mem c.st = stkWs s.mem c.st := by simp only [stkWs]; rw [eW, eL, eC]
  rw [eWs] at hMF hLF
  rw [eL] at hlen; rw [eL, eC] at hsame hgrow hmem
  rw [eW] at hsame
  -- qhat0 = the scratch nat
  have hscr : Scr R c.L c.L1 s.mem T c.st c.t0 (c.vl / 2 + 1) := by
    rw [ht0]; exact Scr.of_post hok hlen (by omega) hsame hgrow rfl
  have hloc : Loc R c s c.t0 (8 * (c.vl / 2 + 1)) := by
    rcases hscr.loc with ⟨-, h1, h2⟩ | h
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h
  have hsep := Loc.sep hpre hloc
  -- the frame of the callee is inside the window
  have hwX : ∀ x k, Outside x k (R.rt ++ win s c.W 96 ++ c.ws s) →
      Outside x k (R.rt ++ win X 4192 24 ++ stkWs s.mem c.st) := by
    intro x k ho
    simp only [Cx.ws, outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    rw [hspX]; refine ⟨⟨ho.1.1, by omega⟩, ho.2.2⟩
  have hown : ∀ x k, Outside x k (R.rt ++ win s c.W 96 ++ c.ws s) → Outside x k (fw s) := by
    intro x k ho
    simp only [outside_append, win, fw, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hfr : MemFrame s.mem T (R.rt ++ win s c.W 96 ++ c.ws s) :=
    mf_trans (hF0.mono hown) (hMF.mono hwX)
  have hlf : LiveFrame s.mem T c.L (c.ws s) := by
    refine ⟨fun x k hin ho => ?_⟩
    have h1 : T.readLE x k = X.mem.readLE x k := hLF.readLE x k hin (by
      simp only [Cx.ws, outside_append] at ho; exact ho.2)
    rw [h1]
    refine hF0.readLE x k ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, outside_cons, outside_nil, and_true] at this ⊢; omega
  -- the old/fresh array
  have hsarr : (stW T c.st = stW s.mem c.st ∧ stCap T c.st = stCap s.mem c.st) ∨
      (InRanges (stW T c.st) (8 * stCap T c.st) R.rt ∧ ApartAll (stW T c.st) (8 * stCap T c.st) c.L) := by
    by_cases hc : stLen s.mem c.st + StackNat.rnd (c.vl / 2 + 1) ≤ stCap s.mem c.st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  have hacc : ∀ x k w, T.accessible x k w = s.mem.accessible x k w := fun x k w => by
    rw [hMF.accessible, hF0.accessible]
  -- the free part at l1
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, -⟩ := hok'
  have hcapT : 0 < stCap T c.st := by simp only [StackNat.rnd] at hlen; omega
  obtain ⟨-, harrh, -, -⟩ := hnl hcapT
  have hfloc : Loc R c s (stW T c.st + 8 * c.l1 s) (8 * (stCap T c.st - c.l1 s)) := by
    simp only [Cx.l1]
    rcases hsarr with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · left; rw [e1, e2]; rw [e2] at hlc; omega
    · right; exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
  have hfsep := Loc.sep hpre hfloc
  have ht0e : c.t0 + 8 * (c.vl / 2 + 1) ≤ stW T c.st + 8 * c.l1 s := by
    rw [ht0]; simp only [Cx.l1, StackNat.rnd]; omega
  -- reads kept
  have hkeep : ∀ x k, Held R c.L x k → Outside x k (win s c.W 96) → Apart x k c.st 24 →
      Apart x k (stW s.mem c.st + 8 * stLen s.mem c.st) (8 * (stCap s.mem c.st - stLen s.mem c.st)) →
      T.readLE x k = s.mem.readLE x k := by
    intro x k hh hw hs hf
    have h1 : T.readLE x k = X.mem.readLE x k := by
      refine Held.readLE2 hh hMF hLF ?_ ?_
      · simp only [win, outside_cons, outside_nil, and_true] at hw ⊢; rw [hspX]; omega
      · unfold Apart at hs hf; simp only [stkWs, outside_cons, outside_nil, and_true]; omega
    rw [h1]; exact hF0.readLE x k (by simp only [win, fw, outside_cons, outside_nil, and_true] at hw ⊢; omega)
  refine ⟨⟨hpre, ra47, x15, hdf, hW, h40, hvu, hu1, hU, hN, hext, hscr.al, hscr.b48, hscr.held, ?_, hloc, hsep.w,
    hsep.g, hsep.fs, hsep.gA, (hsep.st).symm, hsep.q, hsep.u, hsep.v⟩,
    ⟨LiveExt.refl R c.L1, hreg, hinv, hfr, hlf, hok, hsarr,
      ArrIn.of_nat (L1 := c.L1) (m0 := s.mem) (m := T) hlc hlen hsame hmem⟩,
    ⟨by rw [hlen], harrh.sub (by simp only [Cx.l1]; omega) (by simp only [Cx.l1]; omega), hfsep.w, hfsep.g, hfsep.fs,
      hfsep.st, hfsep.gA, hfsep.q, hfsep.u, hfsep.v, by unfold Apart; omega⟩,
    hkeep⟩
  · rw [← hacc]; exact hscr.acc

end FvModexp.Amd64.Q.DivRec
