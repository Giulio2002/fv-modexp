import FvModexp.Proofs.Arm64.Conv
import FvModexp.Proofs.Arm64.Exp.W2P01Defs
import FvModexp.Proofs.Arm64.Exp.W2ZcDefs

/-!
# window-2 prologue (arm64): `z = z.make(2 * numWords)` (nat.go:1425, nat.go:58-69), `j4 → zj`

Reuse when `2n ≤ cap z`, else `makeslice(Word, 2n, 2n+4)`. Result in X0 (pointer), X14 (capacity), X13 = n at `zj`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

/-- `type:big.Word` -/
@[reducible] def wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- the facts about `z` after `z.make(2n)` -/
@[reducible] def ZPost (R : RtInv) (L L' : List (Nat × Nat)) (b b' g sp n : Nat) (M M' : Memory)
    (zp zc zp' zc' : Nat) : Prop :=
  Env R L' g sp M' ∧ Buf R L' g sp n M' zp' zc' ∧ zp' % 8 = 0 ∧ LiveExt R L L' ∧
  b - blockSize (8 * (2 * n + 4)) true ≤ b' ∧
  MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 152)]) ∧ LiveFrame M M' L [] ∧
  R.inv b' L' g (view R.rt L' M') ∧ M'.regions = M.regions ∧
  ((zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L))

theorem out_inR {a n p k : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hin : InRanges p k rs) :
    a + n ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem h hr
  omega

/-- the post of the `makeslice` path, from the contract's post (small context) -/
theorem fresh_post {R : RtInv} {L : List (Nat × Nat)} {b g sp n zp zc p r : Nat} {M m : Memory}
    (he : Env R L g sp M) (hn16 : n ≤ 2 ^ 16)
    (hLF : LiveFrame (M.writeLE (sp + 144) 8 (2 * n + 4)) m L []) (hrg : m.regions = M.regions)
    (hMF : MemFrame (M.writeLE (sp + 144) 8 (2 * n + 4)) m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24)]))
    (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) (hle : p + r ≤ 2 ^ 48)
    (hacc : M.accessible p r true = true) (h8 : p % 8 = 0) (hsz : 8 * (2 * n + 4) ≤ r) (hr : r = blockSize (8 * (2 * n + 4)) true)
    (hinv : R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)) :
    ZPost R L (L ++ [(p, p + r)]) b (b - r) g sp n M m zp zc p (2 * n + 4) := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hw1 : MemFrame M (M.writeLE (sp + 144) 8 (2 * n + 4)) [(sp + 144, sp + 152)] :=
    (MemFrame.refl M [(sp + 144, sp + 152)]).writeLE_inRanges _ ⟨(sp + 144, sp + 152), by simp, by simp only; omega, by simp only; omega⟩
  have hF : MemFrame M m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 152)]) := by
    refine hw1.trans hMF (fun a k ho => ⟨?_, ?_⟩)
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
  have hLw : LiveFrame M (M.writeLE (sp + 144) 8 (2 * n + 4)) L [] :=
    (LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
  have hgo : Outside (g + 16) 8 [(sp - 4096, sp - 8), (sp + 8, sp + 152)] := by
    unfold Apart at hgw; simp only [outside_cons, outside_nil, and_true]; omega
  obtain ⟨hal', hsp1', hsp2', hwacc', hg1', hg2', hg3', hwrt', hgw', hgrt', hLs'⟩ := env_frame he hF hgo
  have hpw := out_inR hwrt hIn
  have hpg := out_inR hgrt hIn
  have hacc' : m.accessible p (8 * (2 * n + 4)) true = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  refine ⟨⟨hal', hsp1', hsp2', hwacc', hg1', hg2', hg3', hwrt', hgw', hgrt', ?_⟩,
    ⟨by omega, by omega, hacc', by omega, Or.inl ⟨(p, p + r), by simp, by omega, by simp only; omega⟩,
      by unfold Apart; omega, by unfold Apart; omega⟩, h8,
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, hF, hLw.trans hLF (fun _ _ h => h), hinv, hrg,
    Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), fun q hq => ?_⟩⟩
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hLs' q hq
    · simp only [List.mem_singleton] at hq; subst hq
      simp only [outside_cons, outside_nil, and_true]; omega
  · have := hAp q hq; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zmake (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n zp zc : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hzc : zc < 2 ^ 40)
    (hz : 2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0)
    (hd : Extracted.program.DataLoaded M) (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r664 : M.readLE (sp + 664) 8 = zc) (r648 : M.readLE (sp + 648) 8 = zp) (r736 : M.readLE (sp + 736) 8 = n)
    (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (hok : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 j4) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KZ : ∀ (S' : State) (M' : Memory) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.pc = BitVec.ofNat 64 zj → S'.sp = BitVec.ofNat 64 sp → S'.regs 0 = BitVec.ofNat 64 zp' →
      S'.regs 13 = BitVec.ofNat 64 n → S'.regs 14 = BitVec.ofNat 64 zc' →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      ZPost R L L' b b' g sp n M M' zp zc zp' zc' →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  by_cases hr : 2 * n ≤ zc
  · obtain ⟨hB, hz8⟩ := hz hr
    janus_run [r664, r648, r736, r128] until [zj]
    refine KZ _ M zp zc L b ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ⟨he, ?_, hz8, LiveExt.refl R L, by omega, MemFrame.refl _ _,
      LiveFrame.refl _ _ _, hinv, rfl, Or.inl ⟨rfl, rfl⟩⟩
    all_goals first | (janus_simp; done) | skip
    exact hB
  · have hr' : zc < 2 * n := by omega
    obtain ⟨hok1, hbs⟩ := hok hr'
    have hwt : Apart wT 16 (sp - 4288) (4288 + 752) := apart_of_data hd 1 (by decide) (by decide) hwacc
    janus_data hd
    janus_eval_nat h_t : wT
    rw [h_t] at hty hok1 hwt
    unfold Apart at hwt
    have hts : (M.writeLE (sp + 144) 8 (2 * n + 4)).readLE 2641088 8 = M.readLE 2641088 8 :=
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
        (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
      intro r hr
      have := hLs r hr
      simp only [Outside, and_true] at this
      omega
    janus_run [r664, r648, r736, r128, hts] until [zj] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv' _ _
    refine KZ _ m ptr.toNat (2 * n + 4) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      (fresh_post he hn16 hLF (by janus_assumption) hMF hAp hIn hle hacc (h8 (Or.inr (by omega))) hsz rfl hinv')
    all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.W2Pro
