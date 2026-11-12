import FvModexp.Proofs.Arm64.Nat.DrsSNP

/-!
# `divRecursiveStep` (arm64), big path: the facts after `qhat0 := stk.nat(B + 1)` (pure)

`hd_mem`: from the entry pre, the frame of the prologue (`fw s`) and `(*stack).nat`'s `PostL` (call state `X`, return
state memory `T`): `Cr`, `Ev`, `Fp` at the stack length `l1`, and `z`, `u`, `v` unchanged since the entry.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 32000000 in
theorem hd_mem {R : RtInv} {c : Cx} {s X : State} {T : Memory} {bk : Nat}
    (hpre : DrsPreW R c.b c.L (drsC (stLen s.mem c.st) c.ul c.vl) c.W c.qp c.ql c.qc c.st c.up c.ul c.uc c.vp c.vl
      c.vc s)
    (ra4 : (s.regs 30).toNat % 4 = 0) (ra48 : (s.regs 30).toNat < 2 ^ 48)
    (hW : drsW c.vl ≤ c.W) (h40 : 40 ≤ c.vl) (hvu : c.vl ≤ c.u1) (hu1 : c.u1 ≤ c.ul)
    (hU : natVal s.mem c.up c.u1 = natVal s.mem c.up c.ul) (hN : NatNorm s.mem c.up c.u1)
    (hMF : MemFrame X.mem T (R.rt ++ winA X 4208 24 ++ stkWs X.mem c.st))
    (hLF : LiveFrame X.mem T c.L (stkWs X.mem c.st))
    (hF0 : MemFrame s.mem X.mem (fw s)) (hXsp : X.sp = s.sp - 400#64)
    (ht0 : c.t0 = stW T c.st + 8 * stLen s.mem c.st)
    (hext : LiveExt R c.L c.L1) (hinv : R.inv bk c.L1 (s.regs 28).toNat (view R.rt c.L1 T))
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
  have hpre' := hpre
  obtain ⟨hce, -, hgl, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hqh, hqw, -⟩, ⟨-, -, huh, huw, -⟩,
    ⟨-, -, hvh, hvw, -, -, -⟩, -, -, -, hsti, ⟨-, hc0⟩, ⟨hqs, hqf⟩, ⟨hus, huf⟩, ⟨hvs, hvf⟩, -, hstf, hfw, -, -, -⟩ := hpre'
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', -, -⟩, -, hout, -, hgr, hLs, -⟩ := hce'
  have hsti' := hsti
  obtain ⟨hsok, hsto, -, -⟩ := hsti'
  have hWg := drsW_ge c.vl
  -- the header is untouched by the prologue
  have hst : Outside c.st 24 (fw s) := by
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have eW : stW X.mem c.st = stW s.mem c.st := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eL : stLen X.mem c.st = stLen s.mem c.st := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap X.mem c.st = stCap s.mem c.st := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eWs : stkWs X.mem c.st = stkWs s.mem c.st := by simp only [stkWs]; rw [eW, eL, eC]
  rw [eWs] at hMF hLF
  rw [eL] at hlen; rw [eL, eC] at hsame hgrow hmem
  rw [eW] at hsame
  have hspX : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hXsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  -- qhat0 = the scratch nat
  have hscr : Scr R c.L c.L1 s.mem T c.st c.t0 (c.vl / 2 + 1) := by
    rw [ht0]; exact Scr.of_post hok hlen (by omega) hsame hgrow rfl
  have hloc : Loc R c s c.t0 (8 * (c.vl / 2 + 1)) := by
    rcases hscr.loc with ⟨-, h1, h2⟩ | h
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h
  have hsep := Loc.sep hpre hloc
  -- the frame of the callee is inside the window
  have hwX : ∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k (R.rt ++ winA X 4208 24 ++ stkWs s.mem c.st) := by
    intro x k ho
    simp only [Cx.ws, outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    rw [hspX]; refine ⟨⟨ho.1.1, by omega, by omega⟩, ho.2.2⟩
  have hown : ∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k (fw s) := by
    intro x k ho
    simp only [outside_append, winA, fw, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hfr : MemFrame s.mem T (R.rt ++ winA s c.W 96 ++ c.ws s) :=
    mf_trans (hF0.mono hown) (hMF.mono hwX)
  have hlf : LiveFrame s.mem T c.L (c.ws s) := by
    refine ⟨fun x k hin ho => ?_⟩
    have h1 : T.readLE x k = X.mem.readLE x k := hLF.readLE x k hin (by
      simp only [Cx.ws, outside_append] at ho; exact ho.2)
    rw [h1]
    refine hF0.readLE x k ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at this ⊢; omega
  -- the old/fresh array
  have hsarr : (stW T c.st = stW s.mem c.st ∧ stCap T c.st = stCap s.mem c.st) ∨
      (InRanges (stW T c.st) (8 * stCap T c.st) R.rt ∧ ApartAll (stW T c.st) (8 * stCap T c.st) c.L) := by
    by_cases hc : stLen s.mem c.st + StackNat.rnd (c.vl / 2 + 1) ≤ stCap s.mem c.st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  have hsin : ArrIn c.L1 c.st s.mem T := by
    intro hn
    by_cases hc : stLen s.mem c.st + StackNat.rnd (c.vl / 2 + 1) ≤ stCap s.mem c.st
    · exact absurd (hsame hc) hn
    · exact hmem (by omega)
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
      · simp only [win, winA, outside_cons, outside_nil, and_true] at hw ⊢; rw [hspX]; omega
      · unfold Apart at hs hf; simp only [stkWs, outside_cons, outside_nil, and_true]; omega
    rw [h1]; exact hF0.readLE x k (fw_out (by omega) hw)
  refine ⟨⟨hpre, ra4, ra48, hW, h40, hvu, hu1, hU, hN, hext, hscr.al, hscr.b48, hscr.held, ?_, hloc, hsep.w, hsep.g,
    hsep.gA, (hsep.st).symm, hsep.q, hsep.u, hsep.v⟩,
    ⟨LiveExt.refl R c.L1, hreg, hinv, hfr, hlf, hok, hsarr, hsin⟩,
    ⟨by rw [hlen], harrh.sub (by simp only [Cx.l1]; omega) (by simp only [Cx.l1]; omega), hfsep.w, hfsep.g, hfsep.st,
      hfsep.gA, hfsep.q, hfsep.u, hfsep.v, by unfold Apart; omega⟩,
    hkeep⟩
  · rw [← hacc]; exact hscr.acc

end FvModexp.Arm64.DivRec
