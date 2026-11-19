import FvModexp.Proofs.Amd64.NatQ.DrsBd

set_option autoImplicit false

/-! (amd64 twin (asm s46) of Arm64/NatQ/DrsEnv.lean + the helpers of Arm64/NatQ/DrsCallS.lean)
# `divRecursiveStep` (amd64), big path: the call environment of the loop's callees (no janus runs)

* `drsCQ_ul64`: the budget is monotone in the dividend length (copy of arm64 `Q.drsCQ_ul`).
* `fresh_apart`, `free_loc`: a held range vs a fresh block; the stack's free part is a `Loc` range.
* `Ev.tls`: the TLS slot `FS:-8` keeps its bytes at every memory of the environment.
* `Ev.callEnv`: `CallEnv R Lk X k a` at a callee entry `X` (`RSP = r - 400`, `k + 400 ≤ W`, `a + 8 ≤ 400`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- `drsCQ` is monotone in the dividend length -/
theorem drsCQ_ul64 : ∀ (n ul ul' : Nat), ul ≤ ul' → drsCQ ul n ≤ drsCQ ul' n
  | n, ul, ul', h => by
    by_cases hn : n < 40
    · rw [drsCQ_small hn, drsCQ_small hn]; exact Nat.le_refl _
    · rw [drsCQ_big hn, drsCQ_big hn]
      have ih := drsCQ_ul64 (n - n / 2 + 1) ul ul' h
      have hq : (ul - n) / (n / 2) ≤ (ul' - n) / (n / 2) := Nat.div_le_div_right (by omega)
      exact Nat.mul_le_mul (Nat.add_le_add_right hq 1) (Nat.add_le_add_right ih _)
termination_by n => n
decreasing_by omega

/-- a held range is apart from a fresh runtime block apart from the live set -/
theorem fresh_apart {R : RtInv} {Lk : List (Nat × Nat)} {x k a n : Nat} (hh : Held R Lk x k)
    (hin : InRanges a n R.rt) (hap : ApartAll a n Lk) : Apart x k a n := by
  rcases hh with ⟨r, hr, h1, h2⟩ | ho
  · have := hap r hr; unfold Apart at this ⊢; omega
  · have := outside_of_inRangesR ho hin; unfold Apart; omega

/-- the stack's free part at a length `l ≥` the entry length is a `Loc` range -/
theorem free_loc {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory} (h : Ev R c s Lk bk M)
    (hl : stLen s.mem c.st ≤ stLen M c.st) :
    Loc R c s (stW M c.st + 8 * stLen M c.st) (8 * (stCap M c.st - stLen M c.st)) := by
  have hlc : stLen M c.st ≤ stCap M c.st := h.sok.2.2.2.2.2.1
  rcases h.sarr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · left; rw [e1, e2]; rw [e2] at hlc; omega
  · right
    exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩

/-- the TLS slot is the entry one at every memory of the environment -/
theorem Ev.tls {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hcr : Cr R c s) (h : Ev R c s Lk bk M) : M.readLE (tls s) 8 = s.mem.readLE (tls s) 8 := by
  have hpre := hcr.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, htr, htw⟩⟩ := hpre.ce
  obtain ⟨hq, hu, hs, hf⟩ := hpre.tl
  obtain ⟨-, hc0, -⟩ := hpre.stl
  obtain ⟨-, -, -, harr⟩ := hpre.sti
  obtain ⟨hwa, -⟩ := harr hc0
  refine h.fr.readLE _ _ ?_
  unfold Apart at htw hq hu hs hf
  unfold FvModexp.Amd64.Q.DivRec.tls
  simp only [win, outside_cons, outside_nil, and_true] at hwa
  simp only [Cx.ws, stkWs, win, outside_append, outside_cons, outside_nil, and_true]
  and_intros <;> first | exact htr | omega

set_option maxHeartbeats 8000000 in
/-- **the call environment at a callee entry `X`** (`RSP = r - 400`; live set `Lk`) -/
theorem Ev.callEnv {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk k a : Nat}
    (hcr : Cr R c s) (h : Ev R c s Lk bk X.mem) (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400)
    (hg : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase) (hk : k + 400 ≤ c.W) (ha : a + 8 ≤ 400) :
    CallEnv R Lk X k a := by
  have hpre := hcr.pre
  have hqa := hpre.qa.1
  have hua := hpre.ua.1
  obtain ⟨hsok, -, -, harr0⟩ := hpre.sti
  obtain ⟨-, hc0, -⟩ := hpre.stl
  have hext := hcr.ext1.trans h.ext
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htg, htr, htw⟩⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgr' : X.mem.readLE ((X.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact h.grd hcr
  obtain ⟨-, -, hsacc, -, hnl, -⟩ := hsok
  obtain ⟨-, -, harr, -⟩ := hnl hc0
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · simp only [stackguard0Offset, regG, hg]; omega
  · simp only [stackguard0Offset, regG, hg]; rw [h.fr.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hgr', hsp]; omega
  · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
  · simp only [regSP]; rw [hsp]; omega
  · simp only [regSP]; rw [hsp]; omega
  · simp only [regSP]; rw [h.fr.accessible, hsp]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [hsp]; omega
  · refine dataLoaded_frame64 (rt := R.rt) (ws := win s c.W 96 ++ c.ws s) hdl h.reg hro
      (by simpa only [List.append_assoc] using h.fr) ?_
    intro r hr hlt
    simp only [Cx.ws, stkWs, win, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · simpa using hqa
    · simpa using hua
    · simpa using hsacc
    · simp only at hlt ⊢
      exact Janus.Arm64.Memory.accessible_mono _ harr (by omega) (by omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · rw [hg]; exact hgr
  · refine hext.liveSep (fun r hr => ?_) (fun r hr => ?_)
    · have := hLs r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega
    · simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [hsp]; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  · rw [hfs]; exact htg.base
  · rw [hfs, h.fr.accessible]; exact htg.readable
  · rw [hfs, hg]
    have := h.tls hcr
    unfold FvModexp.Amd64.Q.DivRec.tls at this
    rw [this]; exact htg.g
  · rw [hfs]; exact htr
  · rw [hfs, hsp]; unfold Apart; omega

end FvModexp.Amd64.Q.DivRec
