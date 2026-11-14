import Janus.Contracts.InternalCallAmd64

set_option autoImplicit false

/-!
# one-segment programs (amd64; agent divmc s80) — kernel speed for long straight-line runs

`janus64_run` proves one auxiliary `stepOK` lemma per distinct pc; the kernel evaluates `p.fetch pc` there, which walks
`bytes.length` of every segment of `p` before the right one (~0.9 s per pc on `LibW.program`, JANUS-ISSUES
"[divmc s79] PERF"). `one P seg` keeps `P`'s stubs/exit/data/contracts but only the segment `seg`, so a run inside
`seg` costs one segment walk per pc. `codeIn_one` (proved ONCE per (P, seg) from three decidable facts) makes it code
of `P.link impl`; `lift` moves a run on `one P seg` that stops at any pc `r` with a continuation on `P.link impl`
back to `P.link impl`.
-/

open Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts.EqHashModel
open Janus (Stub)

namespace FvModexp.Amd64.SegProg

/-- `P` with the single code segment `seg` -/
def one (P : Program) (seg : Segment) : Program := { P with segments := [seg] }

theorem fetchIn_none_pre {pre : List Segment} {seg : Segment} (h : ∀ x ∈ pre, Segment.Apart x seg) {pc : Nat}
    (hc : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length) : Program.fetchIn pre pc = none := by
  induction pre with
  | nil => rfl
  | cons x rest ih =>
    have hx := h x (List.mem_cons_self ..)
    unfold Segment.Apart at hx
    simp only [Program.fetchIn]
    rw [if_neg (by omega)]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **`one P seg` is code of `P.link impl`** when `seg` is a segment of `P` whose earlier segments are apart from it and
whose range holds no stub and not the exit address -/
theorem codeIn_one {P : Program} {impl pre post : List Segment} {seg : Segment}
    (hP : P.segments = pre ++ seg :: post) (hpre : ∀ x ∈ pre, Segment.Apart x seg)
    (hst : ∀ t ∈ P.stubs, ¬ (seg.base ≤ t.addr ∧ t.addr < seg.base + seg.bytes.length))
    (hex : ¬ (seg.base ≤ P.exitAddr ∧ P.exitAddr < seg.base + seg.bytes.length)) :
    CodeIn64 (one P seg) (P.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn [seg] pc = some w := hf
  simp only [Program.fetchIn] at hf'
  by_cases hc : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length
  · rw [if_pos hc] at hf'
    refine ⟨?_, ?_, ?_⟩
    · show Program.fetchIn (P.segments ++ impl) pc = some w
      rw [hP, List.append_assoc, fetchIn_append_none64 _ (fetchIn_none_pre hpre hc), List.cons_append]
      simp only [Program.fetchIn]; rw [if_pos hc]; exact hf'
    · show List.find? (fun t => decide (t.addr = pc)) P.stubs = none
      rw [List.find?_eq_none]
      intro t ht heq
      exact hst t ht (by simp only [decide_eq_true_eq] at heq; omega)
    · show pc ≠ P.exitAddr
      intro he; exact hex (by omega)
  · rw [if_neg hc] at hf'; exact absurd hf' (by simp)

/-- **lift a run on the one-segment program**: it stops at a pc `r`, where the continuation (on `P.link impl`) holds -/
theorem lift {P : Program} {impl : List Segment} {seg : Segment} (hc : CodeIn64 (one P seg) (P.link impl))
    {r ret : W64} {S : State} {Q : State → Prop}
    (h : ReachesRet (one P seg) r S fun S' => ReachesRet (P.link impl) ret S' Q) :
    ReachesRet (P.link impl) ret S Q := by
  obtain ⟨k, S1, h1, -, k2, S2, h2, hr, hq⟩ := h
  exact ⟨_, S2, (Steps.of_codeIn64 hc h1).trans h2, hr, hq⟩

/-- **lift a whole run** (to the return address `ret`) on the one-segment program -/
theorem liftRet {P : Program} {impl : List Segment} {seg : Segment} (hc : CodeIn64 (one P seg) (P.link impl))
    {ret : W64} {S : State} {Q : State → Prop} (h : ReachesRet (one P seg) ret S Q) :
    ReachesRet (P.link impl) ret S Q := by
  obtain ⟨k, S1, h1, hr, hq⟩ := h
  exact ⟨k, S1, Steps.of_codeIn64 hc h1, hr, hq⟩

end FvModexp.Amd64.SegProg
