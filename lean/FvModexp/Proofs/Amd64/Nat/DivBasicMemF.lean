import FvModexp.Proofs.Amd64.Nat.DivBasicLay
import FvModexp.Proofs.Amd64.Nat.DivBasicRel

set_option autoImplicit false

/-!
# `divBasic` (amd64): `Mem` survives writes to scratch slots and to `q`, `u`, `qhatv` (pure)

`scr s`: the frame slots the loop body writes besides `Mem`'s (ABI0 argument/result area `[RSP-224, RSP-144)`, `qhl`,
`qhat`, `j`, `j+n`, `cap(u)-j`, `&u[j]`) and the area below the frame (callee frames, return-address pushes). `Mem.frame`: a frame `MemFrame M M' (scr s ++ wsL …)` keeps
`Mem`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

@[reducible] def scr (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 4424, (s.regs 4).toNat - 137), ((s.regs 4).toNat - 128, (s.regs 4).toNat - 120),
    ((s.regs 4).toNat - 112, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 72),
    ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]

theorem Mem.frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {M M' : Memory} (hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M)
    (hf : MemFrame M M' (scr s ++ wsL qp ql up ul vl t)) :
    Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hqn : qn ql ul vl ≤ ql := by unfold qn; split <;> omega
  have rdw : ∀ a n, ((s.regs 4).toNat - 137 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 128 ∨
      (s.regs 4).toNat - 120 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 112 ∨ (s.regs 4).toNat - 104 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 96 ∨
      (s.regs 4).toNat - 72 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 48 ∨
      (s.regs 4).toNat - 40 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 88) → M'.readLE a n = M.readLE a n := by
    intro a n h
    have hw : (s.regs 4).toNat - 4424 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 88 := by omega
    refine hf.readLE _ _ ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals omega
    · have := hl.qw; clear h; omega
    · have := hl.uw; clear h; omega
    · have := hl.tw; clear h; omega
  have rdo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ a) → (a + n ≤ qp ∨ qp + 8 * ql ≤ a) →
      (a + n ≤ up ∨ up + 8 * ul ≤ a) → (a + n ≤ t ∨ t + 8 * (vl + 1) ≤ a) → M'.readLE a n = M.readLE a n := by
    intro a n h1 h2 h3 h4
    refine hf.readLE _ _ ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | (clear h2 h3 h4; omega) | (clear h1 h3 h4; omega) | (clear h1 h2 h4; omega) | (clear h1 h2 h3; omega)
  have rdS : ∀ (o : Nat) {x : Nat}, o + 8 ≤ 24 → M.readLE (st + o) 8 = x → M'.readLE (st + o) 8 = x := by
    intro o x ho hx
    rw [rdo _ _ (by have := hl.sw; omega) (by have := hl.sq; omega) (by have := hl.su; omega)
      (by have := hl.ts; omega)]; exact hx
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23,
    m24, mtl, mvs, mfr, mlf, minv⟩ := hM
  refine ⟨(rdw _ _ (by omega)).trans m1, (rdw _ _ (by omega)).trans m2, (rdw _ _ (by omega)).trans m3,
    (rdw _ _ (by omega)).trans m4, (rdw _ _ (by omega)).trans m5, (rdw _ _ (by omega)).trans m6,
    (rdw _ _ (by omega)).trans m7, (rdw _ _ (by omega)).trans m8, (rdw _ _ (by omega)).trans m9,
    (rdw _ _ (by omega)).trans m10, (rdw _ _ (by omega)).trans m11, (rdw _ _ (by omega)).trans m12,
    (rdw _ _ (by omega)).trans m13, (rdw _ _ (by omega)).trans m14, (rdw _ _ (by omega)).trans m15,
    (rdw _ _ (by omega)).trans m16, (rdw _ _ (by omega)).trans m17, (rdw _ _ (by omega)).trans m18,
    (rdw _ _ (by omega)).trans m19, (rdw _ _ (by omega)).trans m20, (rdw _ _ (by omega)).trans m21,
    rdS 0 (by omega) m22, rdS 8 (by omega) m23, rdS 16 (by omega) m24, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdo _ _ (by have := hl.tlw; omega) (by have := hl.tlq; omega) (by have := hl.tlu; omega)
      (by have := hl.tlt; omega)]; exact mtl
  · intro a n h1 h2
    rw [rdo a n (by have := hl.vw; omega) (by have := hl.qv; omega) (by have := hl.uv; omega)
      (by have := hl.tv; omega)]; exact mvs a n h1 h2
  · clear m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 mtl rdS rdo rdw mvs mlf minv
    refine (mfTrans mfr hf).mono fun a n ho => ?_
    simp only [scr, win, stkWs, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨hrt, hw1, h3, h4, h5, h6, h7⟩ := ho
    refine ⟨hrt, hw1, h3, h4, h5, h6, h7, ?_, ?_, ?_, ?_, ?_, h3, h4, h5⟩
    all_goals clear h3 h4 h5 h6 h7 hrt; omega
  · clear m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 mtl rdS rdo rdw mvs mfr minv
    refine ⟨fun a n hin hws => ?_⟩
    have hw0 : a + n ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; omega
    have hws' := hws
    simp only [wsL, stkWs, outside_append, outside_cons, outside_nil, and_true] at hws'
    rw [hf.readLE _ _ (by
      simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, hws'.1⟩)]
    exact mlf.readLE a n hin hws
  · clear m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 mtl rdS rdo rdw mvs mlf mfr
    have hout : Outside ((s.regs 4).toNat - 4424) (4424 + 88) R.rt := hE.pre.ce.2.2.2.2.1
    refine RtInv.inv_frame' hf (fun r hr => ?_) minv
    simp only [scr, wsL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hq1 := hE.ext.held hE.pre.qh
    have hu1 := hE.ext.held hE.pre.uh
    have ht1 := hl.theld
    rcases hr with hr | hr
    · left
      have hsp0 := hl.sp0; have hsp1 := hl.sp1
      clear hq1 hu1 ht1 hf minv
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hout.of_sub (by dsimp only; omega) (by dsimp only; omega)
    rcases hr with rfl | rfl | rfl
    · have e : qp + 8 * qn ql ul vl - qp = 8 * qn ql ul vl := by omega
      dsimp only; rw [e]
      rcases (hq1.sub (a := qp) (n := 8 * qn ql ul vl) (Nat.le_refl _) (by omega)) with h | h
      · exact Or.inr h
      · exact Or.inl h
    · have e : up + 8 * ul - up = 8 * ul := by omega
      dsimp only; rw [e]
      exact hu1.symm
    · have e : t + 8 * (vl + 1) - t = 8 * (vl + 1) := by omega
      dsimp only; rw [e]
      exact ht1.symm

end FvModexp.Amd64.DivBasic
