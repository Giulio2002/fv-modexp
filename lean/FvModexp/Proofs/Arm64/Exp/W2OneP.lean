import FvModexp.Proofs.Arm64.Exp.W2One

/-!
# W2One's segment proofs (split out of `W2One` in s67 so that modules needing only `W2One`'s definitions do not wait
for these proofs; unchanged text, same namespace)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `var powers [4]nat` (6 `STP`s) and the call setup of `stk.nat(17n)` -/
theorem zeroLoop (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (R : RtInv) (L : List (Nat × Nat)) (g sp n st : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn16 : n ≤ 2 ^ 16)
    (r672 : M.readLE (sp + 672) 8 = st)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 zl0) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KZ : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp → S'.regs 0 = BitVec.ofNat 64 st →
      S'.regs 1 = BitVec.ofNat 64 (5 * n) → S'.regs 30 = BitVec.ofNat 64 p01 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' [(sp + 432, sp + 528)] → LiveFrame M M' L [] → M'.regions = M.regions →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  janus_run [r672, e17 hn16] until [snE]
  refine KZ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?lf ?rg
  case mf =>
    repeat (refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  case lf =>
    repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  all_goals first | (janus_simp; done) | skip

theorem rd8 (m : Memory) (a k : Nat) : m.readLE a (8 * (k + 1)) = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) (8 * k) := by
  rw [show 8 * (k + 1) = 8 + 8 * k by omega, Memory.readLE_add]

theorem rd_zero (m : Memory) : ∀ (k a : Nat), (∀ j, j < k → m.readLE (a + 8 * j) 8 = 0) → m.readLE a (8 * k) = 0
  | 0, a, _ => by simp
  | k + 1, a, h => by
    rw [rd8, rd_zero m k (a + 8) (fun j hj => by rw [show a + 8 + 8 * j = a + 8 * (j + 1) by omega]; exact h _ (by omega)),
      show m.readLE a 8 = m.readLE (a + 8 * 0) 8 from rfl, h 0 (by omega)]

/-- the frame buffer `one` (`n ≤ 4`) after `one[0] = 1` -/
@[reducible] def oneMem (M : Memory) (sp : Nat) : Memory :=
  (((((M.writeLE (sp + 336) 8 0).writeLE (sp + 344) 8 0).writeLE (sp + 352) 8 0).writeLE (sp + 360) 8 0).writeLE
    (sp + 528) 8 (sp + 336)).writeLE (sp + 336) 8 1

theorem oneMem_facts {R : RtInv} {L : List (Nat × Nat)} {g sp n : Nat} {M : Memory} (he : Env R L g sp M)
    (hn : 0 < n) (hn4 : n ≤ 4) :
    Env R L g sp (oneMem M sp) ∧ MemFrame M (oneMem M sp) [(sp + 336, sp + 368), (sp + 528, sp + 536)] ∧
    LiveFrame M (oneMem M sp) L [] ∧ (oneMem M sp).regions = M.regions ∧
    (oneMem M sp).readLE (sp + 528) 8 = sp + 336 ∧ (oneMem M sp).readLE (sp + 336) (8 * n) = 1 := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hF : MemFrame M (oneMem M sp) [(sp + 336, sp + 368), (sp + 528, sp + 536)] := by
    simp only [oneMem]
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 336, sp + 368)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 528, sp + 536)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  have hgo : Outside (g + 16) 8 [(sp + 336, sp + 368), (sp + 528, sp + 536)] := by
    unfold Apart at hgw; simp only [outside_cons, outside_nil, and_true]; omega
  refine ⟨env_frame he (hF.mono (fun a k h => by simp only [outside_append] at h; exact h.2)) hgo, hF, ?_, by simp only [oneMem, Memory.regions_writeLE], ?_, ?_⟩
  · simp only [oneMem]
    repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  · simp (disch := omega) only [oneMem, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.reducePow]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [rd8]
    have h1 : (oneMem M sp).readLE (sp + 336) 8 = 1 := by
      simp only [oneMem, Memory.readLE_writeLE_self, Nat.reducePow, Nat.one_mod]
    have h2 : (oneMem M sp).readLE (sp + 336 + 8) (8 * k) = 0 := by
      refine rd_zero _ k _ (fun j hj => ?_)
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      all_goals simp (disch := omega) only [oneMem, Memory.readLE_writeLE_of_disjoint,
        Memory.readLE_writeLE_self, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.zero_mod]
    rw [h1, h2]

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem oneSmall (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n st : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn4 : n ≤ 4)
    (r736 : M.readLE (sp + 736) 8 = n) (r672 : M.readLE (sp + 672) 8 = st)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneJ) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Memory) (onep : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp → S'.regs 0 = BitVec.ofNat 64 st →
      S'.regs 1 = BitVec.ofNat 64 (5 * n) → S'.regs 30 = BitVec.ofNat 64 p01 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      OnePost R L L' b b' g sp n M M' onep →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  janus_run [r736, r672, fnBase'] until [zl0]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := oneMem_facts (L := L) (g := g) (n := n) he hn hn4
  have r672' : (oneMem M sp).readLE (sp + 672) 8 = st := by
    simp (disch := omega) only [oneMem, Memory.readLE_writeLE_of_disjoint]; exact r672
  refine zeroLoop impl ret hret Q R L g sp n st (oneMem M sp) r18 r29 o1 (by omega) r672' _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?K
  case K =>
    intro S' M' c1 c2 c3 c4 c5 c6 c7 c8 c9 hF hLF hrg
    have u := hgw; unfold Apart at u
    have hF2 : MemFrame (oneMem M sp) M' (R.rt ++ [(sp + 432, sp + 528)]) :=
      hF.mono (fun a k h => by simp only [outside_append] at h; exact h.2)
    have hgo : Outside (g + 16) 8 [(sp + 432, sp + 528)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    have r528 : M'.readLE (sp + 528) 8 = sp + 336 := by
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact o5
    have r1 : M'.readLE (sp + 336) (8 * n) = 1 := by
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact o6
    refine KA S' M' (sp + 336) L b c1 c2 c3 c4 c5 c6 c7 c8 c9 ⟨env_frame o1 hF2 hgo, LiveExt.refl R L,
      by simp only [show ¬ 4 < n by omega, ite_false]; omega, ?_, o3.trans hLF (fun _ _ h => h), ?_, hrg.trans o4,
      r528, r1, Or.inl ⟨rfl, hn4⟩⟩
    · refine o2.trans hF (fun a k h => ⟨?_, ?_⟩)
      · simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        omega
      · simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        omega
    · have hro : Outside (sp - 4288) (4288 + 752) R.rt := hwrt
      refine FvModexp.Expmc.inv_frame hF (fun r hr => Or.inr ?_) (FvModexp.Expmc.inv_frame o2 (fun r hr => Or.inr ?_) hinv)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact hro.of_sub (by omega) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact hro.of_sub (by omega) (by omega)
  all_goals first | (janus_simp; done) | skip

theorem apartAll_out {a k : Nat} {L : List (Nat × Nat)} (h : ApartAll a k L) (j : Nat) (hj : j ≤ k) :
    Outside a j L :=
  Janus.Contracts.outside_of_forall (fun r hr => by have := h r hr; unfold Apart at this; omega)

/-- the facts at `zl0` on the `makeslice` path (`one` fresh, `one[0] = 1`), from the contract's post -/
theorem large_facts {R : RtInv} {L : List (Nat × Nat)} {b g sp n p : Nat} {M m : Memory}
    (he : Env R L g sp M) (hn4 : 4 < n) (hn16 : n ≤ 2 ^ 16) (hinv : R.inv (b - blockSize (8 * n) true)
      (L ++ [(p, p + blockSize (8 * n) true)]) g (view R.rt (L ++ [(p, p + blockSize (8 * n) true)]) m))
    (hLF : LiveFrame M m L []) (hrg : m.regions = M.regions)
    (hMF : MemFrame M m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24)]))
    (hAp : ApartAll p (blockSize (8 * n) true) L) (hIn : InRanges p (blockSize (8 * n) true) R.rt)
    (hle : p + blockSize (8 * n) true ≤ 281474976710656) (hacc : M.accessible p (blockSize (8 * n) true) true = true)
    (h8 : 16 ≤ 8 * n ∨ 8 * n % 8 = 0 → p % 8 = 0) (hz : ZeroBytes m p (8 * n))
    (hsz : 8 * n ≤ blockSize (8 * n) true) :
    let L' := L ++ [(p, p + blockSize (8 * n) true)]
    let M1 := (m.writeLE (sp + 528) 8 p).writeLE p 8 1
    Env R L' g sp M1 ∧ LiveExt R L L' ∧
    MemFrame M M1 (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 528, sp + 536)]) ∧ LiveFrame M M1 L [] ∧
    R.inv (b - blockSize (8 * n) true) L' g (view R.rt L' M1) ∧ M1.regions = M.regions ∧
    M1.readLE (sp + 528) 8 = p ∧ M1.readLE p (8 * n) = 1 ∧
    InRanges p (8 * n) L' ∧ InRanges p (8 * n) R.rt ∧ ApartAll p (8 * n) L ∧
    M1.accessible p (8 * n) true = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ p % 8 = 0 := by
  intro L' M1
  simp only [L', M1]
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hpw := out_inR hwrt hIn
  have hpg := out_inR hgrt hIn
  have hp8 : p % 8 = 0 := h8 (Or.inr (by omega))
  have hF : MemFrame M M1 (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 528, sp + 536)]) := by
    refine (hMF.mono (fun a k h => ?_)).writeLE _ (r := (sp + 528, sp + 536)) (by simp) (by simp only; omega)
      (by simp only; omega) |>.writeLE_inRanges _ (InRanges.of_subset (hIn.sub (Nat.le_refl _) (by omega)) (fun r hr => List.mem_append_left _ hr))
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1, by omega, by omega⟩
  have hgo : Outside (g + 16) 8 [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 528, sp + 536)] := by
    unfold Apart at hgw; simp only [outside_cons, outside_nil, and_true]; omega
  have hX : LiveExt R L L' := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := env_frame he hF hgo
  have hinL : InRanges p 8 L' := ⟨(p, p + blockSize (8 * n) true), by simp [L'], Nat.le_refl _, by simp only; omega⟩
  refine ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hX.liveSep e11 (fun r hr => ?_)⟩, hX, hF, ?_, ?_,
    by simp only [Memory.regions_writeLE]; exact hrg, ?_, ?_,
    ⟨(p, p + blockSize (8 * n) true), by simp, Nat.le_refl _, by simp only; omega⟩,
    hIn.sub (Nat.le_refl _) (by omega), fun r hr => by have := hAp r hr; unfold Apart at this ⊢; omega,
    by rw [hF.accessible]; exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), by omega, hp8⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 752 - (sp - 4288) = 4288 + 752 by omega]; exact hwrt
  · exact (hLF.writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))).writeLE _
      (apartAll_out hAp 8 (by omega))
  · refine inv_store_held (inv_store_out hinv (hwrt.of_sub (by omega) (by omega))) (Or.inl hinL)
  · simp (disch := omega) only [M1, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.reducePow]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [rd8, Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), hz.readLE (k := 8) (j := 8 * k) (by omega)]

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem oneLarge (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (b : Nat) (L : List (Nat × Nat)) (g sp n st : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn4 : 4 < n) (hn16 : n ≤ 2 ^ 16)
    (hd : Extracted.program.DataLoaded M) (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r736 : M.readLE (sp + 736) 8 = n) (r672 : M.readLE (sp + 672) 8 = st)
    (hok : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, n, n] ∧ blockSize (8 * n) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneJ) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Memory) (onep : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp → S'.regs 0 = BitVec.ofNat 64 st →
      S'.regs 1 = BitVec.ofNat 64 (5 * n) → S'.regs 30 = BitVec.ofNat 64 p01 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      OnePost R L L' b b' g sp n M M' onep →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  obtain ⟨hok1, hbs⟩ := hok
  have hwt : Apart wT 16 (sp - 4288) (4288 + 752) := apart_of_data hd 1 (by decide) (by decide) hwacc
  janus_data hd
  janus_eval_nat h_t : wT
  rw [h_t] at hty hok1 hwt
  unfold Apart at hwt
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  janus_run [r736, r672, fnBase'] until [zl0] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ hz hsz _ hinv' _ _
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ :=
    large_facts he hn4 hn16 hinv' hLF (by janus_assumption) hMF hAp hIn hle hacc h8 hz hsz
  have r672' : ((m.writeLE (sp + 528) 8 ptr.toNat).writeLE ptr.toNat 8 1).readLE (sp + 672) 8 = st := by
    have hpw := out_inR hwrt hIn
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hMF.readLE _ _ ?_]
    · exact r672
    · simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩
  refine zeroLoop impl ret hret Q R _ g sp n st _ r18 r29 o1 hn16 r672' _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?K
  case K =>
    intro S' M' c1 c2 c3 c4 c5 c6 c7 c8 c9 hF hLF2 hrg
    have u := hgw; unfold Apart at u
    have hpw := out_inR hwrt hIn
    have hF2 : MemFrame ((m.writeLE (sp + 528) 8 ptr.toNat).writeLE ptr.toNat 8 1) M' (R.rt ++ [(sp + 432, sp + 528)]) :=
      hF.mono (fun a k h => by simp only [outside_append] at h; exact h.2)
    have hgo : Outside (g + 16) 8 [(sp + 432, sp + 528)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    have r528 : M'.readLE (sp + 528) 8 = ptr.toNat := by
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact o7
    have r1 : M'.readLE ptr.toNat (8 * n) = 1 := by
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact o8
    refine KA S' M' ptr.toNat _ (b - blockSize (8 * n) true) c1 c2 c3 c4 c5 c6 c7 c8 c9 ⟨env_frame o1 hF2 hgo, o2,
      by simp only [show 4 < n from hn4, ite_true]; omega, ?_, o4.trans hLF2 (fun a k h => o2.inRanges_old h), ?_,
      hrg.trans o6, r528, r1, Or.inr ⟨o9, o10, o11, by rw [hF.accessible]; exact o12, o13, o14⟩⟩
    · refine o3.trans hF (fun a k h => ⟨?_, ?_⟩)
      · simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        exact ⟨h.1, by omega, by omega, by omega⟩
      · simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        omega
    · refine FvModexp.Expmc.inv_frame hF (fun r hr => Or.inr ?_) o5
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hwrt.of_sub (by omega) (by omega)
  all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.W2Pro
