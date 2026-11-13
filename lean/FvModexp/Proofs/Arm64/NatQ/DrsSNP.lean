import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsRel

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsSNP.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), big path: pure lemmas about the relations (frames, separation, the loop entry)

* `limbs_congr` (limbs from a read), `Loc` (a range inside the entry stack's free part or a fresh runtime block) and
  `Loc.sep` (its separation from everything the big path uses);
* `Ev.own` / `Fp.own`: the environment survives the function's own frame stores;
* `li_init`, `bud_init`: the loop invariant's value and budget parts at `j = m`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

theorem apart_of_held {R : RtInv} {L : List (Nat × Nat)} {w n p k : Nat} (hh : Held R L w n)
    (hin : InRanges p k R.rt) (hap : ApartAll p k L) : Apart p k w n := by
  rcases hh with h | h
  · obtain ⟨r, hr, h1, h2⟩ := h
    have := hap r hr; unfold Apart at this ⊢; omega
  · have := NatAdd.outside_of_inRanges h hin; unfold Apart; omega

theorem limbs_congr {m m' : Memory} {p n : Nat} (h : m'.readLE p (8 * n) = m.readLE p (8 * n)) :
    Asm.limbs m' p n = Asm.limbs m p n :=
  Asm.eq_of_val (Asm.Wd_limbs _ _ _) (Asm.Wd_limbs _ _ _) (by simp)
    (by rw [Asm.val_limbs, Asm.val_limbs]; exact h)

/-- a range inside the entry stack's free part, or a fresh runtime block apart from the entry live set -/
@[reducible] def Loc (R : RtInv) (c : Cx) (s : State) (a n : Nat) : Prop :=
  (stW s.mem c.st + 8 * stLen s.mem c.st ≤ a ∧ a + n ≤ stW s.mem c.st + 8 * stCap s.mem c.st) ∨
    (InRanges a n R.rt ∧ ApartAll a n c.L)

/-- the separation facts of a `Loc` range -/
structure Sep (c : Cx) (s : State) (a n : Nat) : Prop where
  w : Outside a n (win s c.W 96)
  g : Apart a n (grd s) 8
  gA : Apart a n RunIface.gA 32
  st : Apart c.st 24 a n
  q : Apart a n c.qp (8 * c.ql)
  u : Apart a n c.up (8 * c.ul)
  v : Apart a n c.vp (8 * c.vl)

set_option maxHeartbeats 8000000 in
theorem Loc.sep {R : RtInv} {c : Cx} {s : State} {a n : Nat}
    (hpre : DrsPreW R c.b c.L c.Hq (drsCQ c.ul c.vl) c.W c.qp c.ql c.qc c.st c.up c.ul c.uc c.vp c.vl c.vc s)
    (h : Loc R c s a n) : Sep c s a n := by
  obtain ⟨hce, -, hgl, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hqh, -, -⟩, ⟨-, -, huh, -, -⟩, ⟨-, -, hvh, -, -, -, -⟩,
    -, -, -, hsti, ⟨-, hc0, -⟩, ⟨-, hqf⟩, ⟨-, huf⟩, ⟨-, hvf⟩, -, hstf, hfw, ⟨-, -, -, hfgA⟩, -, -⟩ := hpre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, hgr, -, -⟩ := hce
  obtain ⟨⟨-, hsth, -, -, -, hlc, -⟩, -, -, harr⟩ := hsti
  obtain ⟨-, harg⟩ := harr hc0
  have hgrt : Outside RunIface.gA 32 R.rt := hgl.2.2.2.2.2.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hfw ⊢
  unfold Apart at hqf huf hvf hstf hfgA harg
  rcases h with ⟨h1, h2⟩ | ⟨hin, hap⟩
  · refine ⟨by simp only [win, outside_cons, outside_nil, and_true]; omega, by unfold Apart grd; omega, by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega,
      by unfold Apart; omega, by unfold Apart; omega⟩
  · have ho := NatAdd.outside_of_inRanges hout hin
    have hgo := NatAdd.outside_of_inRanges hgr hin
    have hgo' := NatAdd.outside_of_inRanges hgrt hin
    refine ⟨by simp only [win, outside_cons, outside_nil, and_true]; omega, by unfold Apart grd; omega,
      by unfold Apart; omega, (apart_of_held hsth hin hap).symm,
      apart_of_held hqh hin hap, apart_of_held huh hin hap, apart_of_held hvh hin hap⟩

/-! ## own frame stores -/

/-- the function's own frame ranges are outside `R.rt`, the live objects and the entry's caller-visible ranges -/
theorem own_ok {R : RtInv} {c : Cx} {s : State} (hcr : Cr R c s) {Lk : List (Nat × Nat)} (hext : LiveExt R c.L1 Lk) :
    (∀ r ∈ fw s, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) Lk) ∧
    (∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k (fw s)) := by
  have hW := hcr.hW; have := drsW_ge c.vl
  obtain ⟨hce, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, -, -, -⟩ := hce
  refine ⟨fun r hr => Or.inl ?_, fun x k ho => ?_⟩
  · simp only [fw, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  · simp only [outside_append, winA, fw, outside_cons, outside_nil, and_true] at ho ⊢; omega

theorem Ev.own {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    (hcr : Cr R c s) (h : Ev R c s Lk bk M) (hF : MemFrame M M' (fw s)) (hreg : M'.regions = M.regions) :
    Ev R c s Lk bk M' := by
  obtain ⟨hrt, hsub⟩ := own_ok hcr h.ext
  have hW := hcr.hW; have := drsW_ge c.vl
  obtain ⟨hce, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, -, hLs, -⟩ := hce
  obtain ⟨-, hsto, -, -⟩ := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : Outside c.st 24 (fw s) := by
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have eW : stW M' c.st = stW M c.st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eL : stLen M' c.st = stLen M c.st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap M' c.st = stCap M c.st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  refine ⟨h.ext, by rw [hreg]; exact h.reg, RtInv.inv_frame' hF hrt h.inv,
    mf_trans' h.fr (hF.mono fun x k ho => hsub x k ho), ?_, stkOK_moveS h.sok eW eL eC hF.accessible,
    by rw [eW, eC]; exact h.sarr, h.sarrL.congr eW eC fun _ h => h⟩
  refine ⟨fun x k hin ho => ?_⟩
  rw [hF.readLE x k ?_]
  · exact h.lf.readLE x k hin ho
  · obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at this ⊢; omega
where
  mf_trans' {m₀ m₁ m₂ : Memory} {rs : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs) (h₂ : MemFrame m₁ m₂ rs) :
      MemFrame m₀ m₂ rs := mf_trans h₁ h₂

/-- the stack capacity across own-frame writes (Q-form budgets) -/
theorem Cr.capOwn {R : RtInv} {c : Cx} {s : State} {M M' : Memory} (hcr : Cr R c s) (hF : MemFrame M M' (fw s)) :
    stCap M' c.st = stCap M c.st := by
  have hW := hcr.hW; have := drsW_ge c.vl
  obtain ⟨-, hsto, -, -⟩ := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : Outside c.st 24 (fw s) := by
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  exact hF.readLE _ _ (hst.of_sub (by omega) (by omega))

theorem Fp.own {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {M M' : Memory} {lM : Nat}
    (hcr : Cr R c s) (h : Fp R c s Lk M lM) (hF : MemFrame M M' (DivRec.fw s)) : Fp R c s Lk M' lM := by
  have hW := hcr.hW; have := drsW_ge c.vl
  obtain ⟨-, hsto, -, -⟩ := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : Outside c.st 24 (DivRec.fw s) := by
    simp only [win, DivRec.fw, winA, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have eW : stW M' c.st = stW M c.st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eL : stLen M' c.st = stLen M c.st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap M' c.st = stCap M c.st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  rw [← eW, ← eC] at h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨by rw [eL]; exact h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## the loop entry -/

set_option maxHeartbeats 4000000 in
/-- the loop invariant at `j = m` (the quotient all zero, nothing written yet) -/
theorem li_init {M M0 : Memory} {qp ql up u1 vp vl : Nat} (hv1 : 1 ≤ vl) (hvu : vl ≤ u1)
    (htop : 2 ^ 63 ≤ M0.readLE (vp + 8 * (vl - 1)) 8) (hq0 : natVal M qp ql = 0)
    (hU : natVal M up u1 = natVal M0 up u1) (B : Nat) :
    Mdl.LI (Asm.limbs M0 vp vl) vl B (u1 - vl) ql (natVal M0 up u1) (u1 - vl) (Asm.limbs M qp ql)
      (Asm.limbs M up u1) := by
  have hV := v_ge hv1 htop
  have hUlt := natVal_lt M up u1
  have e : 2 ^ (64 * u1) ≤ 2 ^ (64 * (vl - 1)) * 2 ^ 63 * 2 ^ (64 * (u1 - vl + 1)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have e2 : 2 ^ (64 * (vl - 1)) * 2 ^ 63 * 2 ^ (64 * (u1 - vl + 1)) ≤ natVal M0 vp vl * 2 ^ (64 * (u1 - vl + 1)) :=
    Nat.mul_le_mul_right _ hV
  refine ⟨Asm.Wd_limbs _ _ _, Asm.Wd_limbs _ _ _, by simp, by simp; omega, ?_, ?_, ?_, Or.inl rfl⟩
  · rw [Asm.val_limbs, Asm.val_limbs, Asm.val_limbs]
    show natVal M up u1 + natVal M0 vp vl * natVal M qp ql = natVal M0 up u1
    rw [hq0, hU]; simp
  · rw [Asm.val_limbs, Asm.val_limbs]
    show natVal M up u1 < natVal M0 vp vl * 2 ^ (64 * (u1 - vl + 1))
    omega
  · intro d hd
    rw [List.drop_of_length_le (by simp; omega)] at hd
    simp at hd

/-- the budget at the loop entry (Q-form: the reserve at the head memory `M`) -/
theorem bud_init {R : RtInv} {c : Cx} {s : State} {b1 : Nat} {M : Memory}
    (hc : drsCQ c.ul c.vl + stkR c.Hq s.mem c.st ≤ c.b) (h40 : 40 ≤ c.vl) (hvu : c.vl ≤ c.u1) (hu : c.u1 ≤ c.ul)
    (hb1 : c.b - stkR c.Hq s.mem c.st + stkR c.Hq M c.st ≤ b1) :
    c.lo s + ((c.u1 - c.vl) / (c.vl / 2) + 1) * c.K s + stkR c.Hq M c.st ≤ b1 := by
  unfold Cx.lo
  rw [drsCQ_big (by omega)] at hc ⊢
  have hq : (c.u1 - c.vl) / (c.vl / 2) ≤ (c.ul - c.vl) / (c.vl / 2) := Nat.div_le_div_right (by omega)
  have := Nat.mul_le_mul_right (c.K s) (Nat.add_le_add_right hq 1)
  simp only [Cx.K] at this ⊢
  omega

end FvModexp.Arm64.Q.DivRec
