import FvModexp.Proofs.Arm64.Nat.DivMLessA
import FvModexp.Proofs.Arm64.Nat.DivMDefs

set_option autoImplicit false

/-! `nat.div`, `z = nil`, `z2 = u`: `lessFinM`, `lessSM` (the `IMod.DivPostM` part of the former DivMLess). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the postcondition of the `u < v` path with `z2 = u` (`r = u[:len u]`, nothing copied) -/
theorem lessFinM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s) {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L 0 0 u uc u ul s u uc L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (s' : State) {q ql qc : Nat}
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 1 = BitVec.ofNat 64 ql) (h2 : s'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 3 = BitVec.ofNat 64 u) (h4 : s'.regs 4 = BitVec.ofNat 64 ul) (h5 : s'.regs 5 = BitVec.ofNat 64 uc)
    (hM : MemFrame S.mem s'.mem [(s.sp.toNat - 80, s.sp.toNat - 56)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)) :
    PostM R b dc L u ul uc v vl s s' := by
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hp.ce
  have hLs1 : ∀ r ∈ L', r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ r.1 := by
    obtain ⟨ns, e, hn, -⟩ := hS.ext
    intro r hr; rw [e] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := outside_of_inRanges hout (hn r hr).1; omega
  -- `u`'s words at `s'.mem` are the entry's
  have hku : ∀ a n, u ≤ a → a + n ≤ u + 8 * ul → 0 < n → s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2 hn
    obtain ⟨-, -, -, huh, huw⟩ := hp.ui.2 (by omega)
    simp only [win, outside_cons, outside_nil, and_true] at huw
    rw [hM.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rcases huh.sub h1 h2 with hin | ho
    · exact hS.lf.readLE a n hin trivial
    · exact hS.mf.readLE a n (by
        simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨ho, by omega, by omega⟩)
  have hval : natVal s'.mem u ul = natVal s.mem u ul := by
    by_cases h0 : ul = 0
    · simp [natVal, h0]
    · exact hku _ _ (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hbud := hS.bud
  have hc := hp.cost
  have hacc : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hM.accessible, hS.mf.accessible]
  refine ⟨q, ql, qc, u, ul, uc, h0, h1, h2, h3, h4, h5, L', b', ⟨?_, ?_, hp.ulc, hp.uo.1, ?_, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨hS.ext, ?_, hinv⟩, hS.mf.trans hM fun a n h => ⟨?_, ?_⟩, ⟨fun a n hin ho => ?_⟩⟩
  · rw [hval, Nat.mod_eq_of_lt hU]
  · by_cases h0 : ul = 0
    · exact Or.inl h0
    · rcases hp.un with h | h
      · exact absurd h h0
      · exact Or.inr (by rw [hku _ _ (by omega) (by omega) (by omega)]; exact h)
  · intro hcu
    obtain ⟨a1, a2, a3, a4⟩ := hp.uo.2.1 hcu
    exact ⟨a1, hS.ext.held a2, by rw [hacc]; exact a3, a4⟩
  · simp only [costM, cost] at hc ⊢; omega
  · simp only [outside_append] at h ⊢; exact h.1
  · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  · obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs1 r (hS.ext.mem_old hr)
    rw [hM.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hS.lf.readLE a n ⟨r, hr, i1, i2⟩ trivial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u < v`, `z2 = u`: `copy(u[:len u], u)` is skipped (same pointer), `r = u[:len u]` stored, return -/
theorem lessSM (impl : List Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s) {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L 0 0 u uc u ul s u uc L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hp.ce
  unfold Apart at hga
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr6 := hS.r6
  have hacc := hS.mf.accessible
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hacc]; exact hw
  have hinvS := hS.inv
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.q0; have m4 := hS.q1; have m5 := hS.q2; have m6 := hS.s8
  have hB : Box (PFM R b dc L u ul uc v vl s ∧ AtS R b L 0 0 u uc u ul s u uc L' b' S) := ⟨⟨hp, hS⟩⟩
  have hpu' : (BitVec.ofNat 64 u = BitVec.ofNat 64 u) = True := eq_self _
  clear hp hS
  janus_run [m1, m2, m3, m4, m5, m6, hpu']
  obtain ⟨hp, hS⟩ := hB.h
  have hW2 : MemFrame S.mem (((S.mem.writeLE (s.sp.toNat - 80) 8 u).writeLE (s.sp.toNat - 72) 8 ul).writeLE
      (s.sp.toNat - 64) 8 uc) [(s.sp.toNat - 80, s.sp.toNat - 56)] := by janus_frame
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lessFinM (q := 0) (ql := 0) (qc := 0) hp hS hU _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hI⟩
  case hM => first | exact hW2 | janus_frame
  case hI =>
    refine RtInv.inv_frame' hW2 (fun r hr => ?_) hinvS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  all_goals janus_simp
  all_goals exact ofNat_modL _

end FvModexp.Arm64.NatDiv
