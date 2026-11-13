import FvModexp.Proofs.Amd64.NatQ.DrsEnv

set_option autoImplicit false

/-! (amd64 twin (asm s47) of Arm64/NatQ/DrsCallS.lean)
# `divRecursiveStep` (amd64), loop body: the environment after a stack-using callee (pure)

A callee that takes the stack (`divRecursiveStep`, `nat.mul`) writes `ws` (its arguments) and `stkWs X st`, may grow the
stack's array (fresh, in `R.rt`, apart from the live set) and allocate (`LiveExt Lk L'`), and returns the stack at the
same length (`StackBackL`). `Ev.callS` / `Fp.callS`: `Ev` and `Fp` survive it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 8000000 in
/-- **the environment after a stack-using callee** (frame `R.rt ++ wsS ++ ws ++ stkWs M st`) -/
theorem Ev.callS {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {bk b' : Nat} {M M' : Memory}
    {wsS ws : List (Nat × Nat)} (hcr : Cr R c s) (h : Ev R c s Lk bk M) (hl : stLen s.mem c.st ≤ stLen M c.st)
    (hF : MemFrame M M' (R.rt ++ wsS ++ ws ++ stkWs M c.st)) (hL : LiveFrame M M' Lk (ws ++ stkWs M c.st))
    (hS : ∀ x k, Outside x k (win s c.W 96) → Outside x k wsS)
    (hW1 : ∀ x k, Outside x k (R.rt ++ win s c.W 96 ++ c.ws s) → Outside x k ws)
    (hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k ws)
    (hx : LiveExt R Lk L') (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M')) (hsb : StackBackL R Lk L' c.st M M')
    (hreg : M'.regions = M.regions) :
    Ev R c s L' b' M' := by
  obtain ⟨⟨hok, -, hsar⟩, harr⟩ := hsb
  have hloc := (free_loc h hl).out
  have hlc : stLen M c.st ≤ stCap M c.st := h.sok.2.2.2.2.2.1
  have hfr : MemFrame M M' (R.rt ++ win s c.W 96 ++ c.ws s) := hF.mono fun x k ho => by
    have h1 := hW1 x k ho
    have h2 := hloc.1 x k ho
    rw [outside_append] at ho
    obtain ⟨ho1, ho2⟩ := ho
    rw [outside_append] at ho1
    obtain ⟨hr, hw⟩ := ho1
    rw [outside_append, outside_append, outside_append]
    refine ⟨⟨⟨hr, hS x k hw⟩, h1⟩, ?_⟩
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho2 h2 ⊢
    exact ⟨by omega, by omega⟩
  refine ⟨h.ext.trans hx, by rw [hreg]; exact h.reg, hinv, mf_trans h.fr hfr, ?_, hok, ?_, h.sarrL.trans harr hx⟩
  · refine ⟨fun x k hin ho => ?_⟩
    rw [hL.readLE x k ((hcr.ext1.trans h.ext).inRanges_old hin) ?_]
    · exact h.lf.readLE x k hin ho
    · have h1 := hW2 x k hin ho
      have h2 := hloc.2 x k hin ho
      rw [outside_append]
      refine ⟨h1, ?_⟩
      simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho h2 ⊢
      exact ⟨by omega, by omega⟩
  · rcases hsar with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact h.sarr
    · exact Or.inr ⟨hin, fun r hr => hap r ((hcr.ext1.trans h.ext).mem_old hr)⟩

set_option maxHeartbeats 8000000 in
/-- **the free part after a stack-using callee** (same length) -/
theorem Fp.callS {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {lM : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk M) (h : Fp R c s Lk M lM) (hl0 : 0 < lM) (hx : LiveExt R Lk L')
    (hsb : StackBackL R Lk L' c.st M M') : Fp R c s L' M' lM := by
  obtain ⟨⟨hok, hlen, hsar⟩, -⟩ := hsb
  rcases hsar with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    rw [← e1, ← e2] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨by rw [hlen]; exact h1, hx.held h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · have hW := hcr.hW; have := drsW64_ge c.vl
    have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
    have hpre := hcr.pre
    obtain ⟨-, -, hqh, -, -⟩ := hpre.qa
    obtain ⟨-, -, huh, -, -⟩ := hpre.ua
    obtain ⟨-, -, hvh, -, -, -, -⟩ := hpre.va
    obtain ⟨-, -, -, -, hout, -, hgr, -, -, -, htrt, -⟩ := hpre.ce
    have hgrt : Outside RunIface.gA 32 R.rt := hpre.gl.2.2.2.2.2.2.2.2.1
    have hlc := hok.2.2.2.2.2.1
    have hl' : stLen M' c.st = lM := by rw [hlen]; exact h.len
    have fh : Held R L' (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) := by
      obtain ⟨-, hh, -, -⟩ := hok.2.2.2.2.1 (by omega)
      exact hh.sub (by omega) (by omega)
    have sub : ∀ {x k}, Apart x k (stW M' c.st) (8 * stCap M' c.st) →
        Apart x k (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) := fun hh => by unfold Apart at hh ⊢; omega
    have sub' : ∀ {x k}, Apart x k (stW M' c.st) (8 * stCap M' c.st) →
        Apart (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) x k := fun hh => by unfold Apart at hh ⊢; omega
    have hw1 := outside_of_inRangesR hout hin
    have hg1 := outside_of_inRangesR hgr hin
    have ht1 := outside_of_inRangesR htrt hin
    have hgA1 := outside_of_inRangesR hgrt hin
    refine ⟨by rw [hlen]; exact h.len, fh, ?_, sub' (by unfold Apart grd; omega), sub' (by unfold Apart tls; omega),
      sub (fresh_apart hev.sok.2.1 hin hap), sub' (by unfold Apart; omega), sub' ((fresh_apart (hext.held hqh) hin hap)),
      sub' ((fresh_apart (hext.held huh) hin hap)), sub' ((fresh_apart (hext.held hvh) hin hap)),
      sub' ((fresh_apart (hev.ext.held hcr.t0h) hin hap))⟩
    simp only [win, outside_cons, outside_nil, and_true]; omega

end FvModexp.Amd64.Q.DivRec
