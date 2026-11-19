import FvModexp.Proofs.Amd64.Exp.LibExp
import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Common.Link
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# Calling a project callee (an `Ensures` premise) from an exp-layer function proved on `LibExp` (amd64; agent infra)

The amd64 twin of `FvModexp.Arm64.CallW`:
* `hypSum`: an `Ensures` on `(Extracted.program.onlySegments ns).link impl` (`ns ⊆ LibExp.names`) as a `Summary` of
  `LibExp.program.link impl`.
* `retAddr_restrict`: a return address inside the caller's own segment (not in `ns`) is a `RetAddr` of the callee's
  program.
* `CEnv`: the caller's stack/guard/TLS/data environment on its current memory; `callEnv_of` gives the callee's `CallEnv`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.CallW

theorem hypSum {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibExp.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 args ∧ s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  have hS := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hlen (A64.codeIn_restrict_mono64 hap hns)
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
restricted program of `ns` (amd64). -/
theorem retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
    {ns : List String} {cs : Amd64.Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat)
    (hi : i < cs.bytes.length) (hu : cs.base + i < 2 ^ 47) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + i) := by
  refine ⟨hu, fun seg hseg => ?_, fun st hst => ?_⟩
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
        unfold Amd64.Segment.Apart at this
        omega
    have := pairwise_ne (fun a b h => by unfold Amd64.Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Amd64.Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Amd64.Program.stubAt at h1
    have := find_none_of h1 st hst
    simp at this
    exact this

/-- The caller's environment on its current memory `M` (amd64): stack window `[sp - K, sp + A)` (`sp` = the caller's
`RSP`), guard word, TLS slot, read-only data. -/
@[reducible] def CEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K A : Nat) (M : Memory) : Prop :=
  sp % 8 = 0 ∧ K ≤ sp ∧ sp + A ≤ 2 ^ 48 ∧ M.accessible (sp - K) (K + A) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + K < sp ∧
  Outside (sp - K) (K + A) R.rt ∧ Apart (g + 16) 8 (sp - K) (K + A) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - K, sp + A)] ∧ Extracted.program.DataLoaded M ∧ RoOut R ∧
  8 ≤ fs ∧ fs ≤ 2 ^ 48 ∧ M.accessible (fs - 8) 8 false = true ∧ M.readLE (fs - 8) 8 = g ∧
  Outside (fs - 8) 8 R.rt ∧ Apart (fs - 8) 8 (sp - K) (K + A)

theorem callEnv_of {R : RtInv} {L : List (Nat × Nat)} {g fs sp K A : Nat} {M : Memory}
    (h : CEnv R L g fs sp K A M) {s : State} (hsp : (s.regs 4).toNat = sp) (hg : (s.regs 14).toNat = g)
    (hfs : s.fsBase.toNat = fs) (hm : s.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ A)
    (hK : stk ≤ sp) (hA8 : 8 ≤ A := by omega) :
    CallEnv R L s stk above := by
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  unfold CallEnv TlsOK
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, by rw [hm]; exact hd, ?_, ?_, ?_, ?_, hro, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  all_goals try simp only [regG, regSP, stackguard0Offset, stackguard0, hsp, hg, hfs, hm, win]
  all_goals first
    | omega | exact hg2 | exact f3 | exact f4 | exact f5 | exact hgrt
    | (exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega))
    | (exact hrt.of_sub (by omega) (by omega))
    | (unfold Apart at hga ⊢; omega) | (unfold Apart at f6 ⊢; omega) | (unfold Apart at hga; omega)
    | (intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)

/-- `CEnv` survives a frame (`R.rt ++ ws`, `ws` writable at the old memory, guard and TLS words outside `ws`) when the
regions are unchanged. -/
theorem CEnv.frame {R : RtInv} {L : List (Nat × Nat)} {g fs sp K A : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : CEnv R L g fs sp K A M) (hf : MemFrame M M' (R.rt ++ ws)) (hreg : M'.regions = M.regions)
    (hws : ∀ r ∈ ws, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true) (hg : Outside (g + 16) 8 ws)
    (hfw : Outside (fs - 8) 8 ws) :
    CEnv R L g fs sp K A M' := by
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  have hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨hgrt, hg⟩)
  have hfr : M'.readLE (fs - 8) 8 = M.readLE (fs - 8) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨f5, hfw⟩)
  refine ⟨hal, hK, hA, by rw [hf.accessible]; exact hacc, hg1, by rw [hf.accessible]; exact hg2, by rw [hgr]; exact hg3,
    hrt, hga, hgrt, hLs, FvModexp.dataLoaded_frame64 hd hreg hro hf hws, hro, f1, f2, by rw [hf.accessible]; exact f3,
    by rw [hfr]; exact f4, f5, f6⟩

theorem CEnv.mono {R : RtInv} {L : List (Nat × Nat)} {g fs sp K A K' A' : Nat} {M : Memory}
    (h : CEnv R L g fs sp K A M) (hK : K' ≤ K) (hA : A' ≤ A) : CEnv R L g fs sp K' A' M := by
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨hal, by omega, by omega, M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega), hg1, hg2, by omega,
    hrt.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgrt, ?_, hd, hro, f1, f2, f3, f4, f5,
    by unfold Apart at f6 ⊢; omega⟩
  intro r hr
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

end FvModexp.Amd64.CallW
