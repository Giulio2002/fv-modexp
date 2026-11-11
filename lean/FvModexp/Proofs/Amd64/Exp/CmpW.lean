import FvModexp.Proofs.Amd64.CmpSum
import FvModexp.Proofs.Amd64.Exp.LibExp
import FvModexp.Proofs.Amd64.Nat.Callees

/-!
# `nat.cmp` (agent asm's verified amd64 `CmpSum.cmp_summary`) as a callee in the exp layer's program `LibExp` (amd64;
agent infra) — twin of `FvModexp.Arm64.CmpW`

Entry `0x5e5cc0 = 6184128`. Its precondition has no `DataLoaded`/live-set parts; its post is the call state with
`RAX = cmpRes`, `RCX, RDX, RSI` clobbered, `RSP + 8`, the memory framed by `CmpSum.frame`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.CmpW

theorem codeIn (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.CmpAmd64.program (LibExp.program.link impl) := by
  rw [LibExp.eq_only]
  exact Callees.codeIn_single hap (seg := Extracted.seg15) rfl
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide)

theorem sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibExp.program.link impl) 6184128 CmpSum.Pre CmpSum.Post :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn64 (codeIn impl hap) CmpSum.cmp_summary

/-- A call of `nat.cmp` at its entry, continuation form over an opaque return state. -/
theorem call {p : Amd64.Program} (hsum : Summary p 6184128 CmpSum.Pre CmpSum.Post) {S : State} {ret : W64}
    {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 6184128) (hpre : CmpSum.Pre S)
    (K : ∀ S' : State, S'.rip = retAddrOf S → S'.regs 4 = S.regs 4 + 8#64 →
      S'.regs 0 = CmpSum.cmpRes (S.regs 3).toNat (S.regs 6).toNat (FvModexp.Asm.lv S.mem (S.regs 0).toNat (S.regs 3).toNat)
        (FvModexp.Asm.lv S.mem (S.regs 7).toNat (S.regs 6).toNat) →
      (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 4 → i ≠ 6 → S'.regs i = S.regs i) →
      S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = S.df →
      MemFrame S.mem S'.mem (CmpSum.frame S) → S'.mem.regions = S.mem.regions → ReachesRet p ret S' Q) :
    ReachesRet p ret S Q := by
  refine ReachesRet.call_regions hsum hpc hpre fun s' hr hq hrg => ?_
  obtain ⟨v1, v2, v6, f, m, rfl, hf⟩ := hq
  refine K _ hr (by simp [setRegF]) (by simp [setRegF]) (fun i h0 h1 h2 h4 h6 => ?_) rfl rfl rfl hf hrg
  simp [setRegF, h0, h1, h2, h4, h6]

end FvModexp.Amd64.CmpW
