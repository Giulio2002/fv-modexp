import FvModexp.Proofs.Arm64.Exp.ExpHyp
import FvModexp.Proofs.Common.Link
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# Calling a project callee (an `Ensures` premise, `ExpHyp`) from an exp-layer function proved on `LibExp` (arm64)

* `hypSum`: an `Ensures` on `(Extracted.program.onlySegments ns).link impl` (`ns ⊆ LibExp.names`) as a `Summary` of
  `LibExp.program.link impl`.
* `retAddr_restrict`: a return address inside the caller's own segment (not in `ns`) is a `RetAddr` of the callee's
  program (the `RetAddr` premise of `Ensures.toSummaryIn`).
* `CEnv`: the caller's stack/guard/data environment on its current memory; `callEnv_of` gives the callee's `CallEnv`.

Callee calls are made by hand (`janus_run until [callee entry]`, then `Reaches.call`): the call-precondition closer of
`janus_run` does not prove `DataLoaded`/`MemFrame` goals.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.CallW

theorem hypSum {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {f : String} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) [ArgsFit args] :
    Summary (LibExp.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibExp.eq_only] at hS
  exact hS

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hR _ _ (hp.1 a ha')
      · exact pairwise_ne hR hp.2 ha' hb' hne

theorem find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact find_none_of h x hx'

/-- A return address inside the code of a segment `cs` of `P` whose name is not in `ns` is a `RetAddr` of the
restricted program of `ns`. -/
theorem retAddr_restrict {P : Program} {impl : List Segment} (hap : ImplApart P impl) {ns : List String}
    {cs : Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat) (hi : i < cs.words.length)
    (hu : cs.base + 4 * i < 2 ^ 48) (ha : cs.base % 4 = 0) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + 4 * i) := by
  refine ⟨by omega, hu, fun seg hseg => ?_, fun st hst => ?_⟩
  · have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have hne : seg ≠ cs := by
      rintro rfl
      rcases List.mem_append.1 hseg with h | h
      · have := (List.mem_filter.1 h).2
        rw [hn] at this; exact absurd this (by decide)
      · have := hap.1
        rw [List.pairwise_append] at this
        have := this.2.2 seg hcs seg h
        unfold Segment.Apart at this
        have hl : 0 < seg.words.length := by omega
        omega
    have := pairwise_ne (fun a b h => by unfold Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Program.stubAt at h1
    have := find_none_of h1 st hst
    simp at this
    exact this

/-- The caller's environment on its current memory `M`: stack window `[sp - K, sp + A)`, guard, read-only data. -/
@[reducible] def CEnv (R : RtInv) (L : List (Nat × Nat)) (g sp K A : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ K ≤ sp ∧ sp + A ≤ 2 ^ 48 ∧ M.accessible (sp - K) (K + A) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + K < sp ∧
  Outside (sp - K) (K + A) R.rt ∧ Apart (g + 16) 8 (sp - K) (K + A) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - K, sp + A)] ∧ Extracted.program.DataLoaded M ∧ RoOut R

theorem callEnv_of {R : RtInv} {L : List (Nat × Nat)} {g sp K A : Nat} {M : Memory} (h : CEnv R L g sp K A M)
    {s : State} (hsp : s.sp = BitVec.ofNat 64 sp) (hg : s.regs 28 = BitVec.ofNat 64 g) (hm : s.mem = M)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ A) : CallEnv R L s stk above := by
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := h
  have esp : s.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (s.regs 28).toNat = g := by rw [hg, BitVec.toNat_ofNat]; omega
  unfold CallEnv GuardOK StackOK
  rw [esp, eg, hm]
  refine ⟨⟨hg1, hg2, by omega⟩, ⟨hal, by omega, by omega, M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)⟩,
    hd, hrt.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgrt, ?_, hro⟩
  intro r hr
  have := hLs r hr
  simp only [win, outside_cons, outside_nil, and_true] at this ⊢
  rw [esp]; omega

/-- `CEnv` survives a frame (`R.rt ++ ws`, `ws` writable at the old memory, the guard word outside `ws`) when the
regions are unchanged. -/
theorem CEnv.frame {R : RtInv} {L : List (Nat × Nat)} {g sp K A : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : CEnv R L g sp K A M) (hf : MemFrame M M' (R.rt ++ ws)) (hreg : M'.regions = M.regions)
    (hws : ∀ r ∈ ws, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true) (hg : Outside (g + 16) 8 ws) :
    CEnv R L g sp K A M' := by
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := h
  have hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨hgrt, hg⟩)
  refine ⟨hal, hK, hA, by rw [hf.accessible]; exact hacc, hg1, by rw [hf.accessible]; exact hg2, by rw [hgr]; exact hg3,
    hrt, hga, hgrt, hLs, FvModexp.dataLoaded_frame hd hreg hro hf hws, hro⟩

theorem CEnv.mono {R : RtInv} {L : List (Nat × Nat)} {g sp K A K' A' : Nat} {M : Memory}
    (h : CEnv R L g sp K A M) (hK : K' ≤ K) (hA : A' ≤ A) : CEnv R L g sp K' A' M := by
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := h
  refine ⟨hal, by omega, by omega, M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega), hg1, hg2, by omega,
    hrt.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgrt, ?_, hd, hro⟩
  intro r hr
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

end FvModexp.Arm64.CallW
