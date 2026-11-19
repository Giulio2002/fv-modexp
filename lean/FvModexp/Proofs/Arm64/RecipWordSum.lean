import FvModexp.Proofs.Arm64.Div64Sum
import FvModexp.Proofs.Common.AsmDivMath
import FvModexp.Proofs.Lib.RecipA64
import FvModexp.Proofs.Common.AsmDivEns

/-!
# `math/big.reciprocalWord(d1 Word) Word` (go-bigmodexpfix `src/math/big/arith.go:333`, Go ABIInternal, arm64)

`u = d1 << nlz(d1)`, `rec, _ = bits.Div(^u, _M, u)`: for `d1 != 0` it returns `recipWord d1 = (2^128-1)/u - 2^64`
(`Common/AsmDivMath.lean`, the reciprocal `divWW` expects). The callee `math/bits.Div64` is `Div64Sum.div64_summary`
(proved on `Lib.DivA64`, moved into this library program by `codeIn_div`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Lib.RecipA64 (program entry)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.RecipWordSum

/-- (adapted from agent expmc `Arm64/Exp/MontAsm.lean` `codeIn_single`, without `link`) -/
theorem codeIn_seg {p P : Program} {S : Segment} (pre post : List Segment)
    (hp : p.segments = [S]) (hP : P.segments = pre ++ S :: post) (hap : ∀ seg ∈ pre, Segment.Apart seg S)
    (hs : ∀ i < S.words.length, P.stubAt (S.base + 4 * i) = none ∧ S.base + 4 * i ≠ P.exitAddr) :
    CodeIn p P := by
  intro pc w hf
  have hf' : Program.fetchIn [S] pc = some w := by rw [← hp]; exact hf
  obtain ⟨i, hi, rfl⟩ := fetchIn_single_some hf'
  have hw : w = S.words[i] := by
    rw [show [S] = S :: [] from rfl, Program.fetchIn_cons_index hi] at hf'; exact (Option.some.inj hf').symm
  refine ⟨?_, (hs i hi).1, (hs i hi).2⟩
  show Program.fetchIn P.segments _ = _
  rw [hP, fetchIn_append_none _ (Program.fetchIn_eq_none fun seg hseg => by
    have := hap seg hseg; unfold Segment.Apart at this; omega), Program.fetchIn_cons_index hi, hw]

set_option maxRecDepth 100000 in
theorem codeIn_div : CodeIn FvModexp.Lib.DivA64.program program :=
  codeIn_seg [FvModexp.Lib.RecipA64.segments[0]'(by decide)] [] (S := FvModexp.Lib.DivA64.segments[0]'(by decide))
    rfl rfl (by decide) (by decide)

theorem div64 :
    Summary program FvModexp.Lib.DivA64.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0 ∧ StackOK s 40 0 ∧
        (s.regs 2).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        (s'.regs 0).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat ∧
        (s'.regs 1).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → s'.regs i = s.regs i) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 40, s.sp.toNat - 24)]) :=
  Summary.of_codeIn codeIn_div FvModexp.Arm64.Div64Sum.div64_summary

theorem recip_val (U : Nat) (h1 : 2 ^ 63 ≤ U) (h2 : U < 2 ^ 64) :
    ((18446744073709551615 - U) * 18446744073709551616 + 18446744073709551615) / U = (2 ^ 128 - 1) / U - 2 ^ 64 := by
  have e : (18446744073709551615 - U) * 18446744073709551616 + 18446744073709551615 = (2 ^ 128 - 1) - U * 2 ^ 64 := by
    rw [Nat.sub_mul]; omega
  rw [e, Nat.sub_mul_div]

theorem recip_lt (U : Nat) (h1 : 2 ^ 63 ≤ U) : (2 ^ 128 - 1) / U - 2 ^ 64 < 2 ^ 64 := by
  have : (2 ^ 128 - 1) / U < 2 ^ 65 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have := Nat.mul_le_mul_left (2 ^ 65) h1
    omega
  omega

/-- the postcondition: `X0 = recipWord d1`, the frame `[SP-88, SP)` (own 48 + `Div64`'s 40 bytes) written -/
def Post (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord (s.regs 0).toNat) ∧
  s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
  (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 29, 30] → s'.regs i = s.regs i) ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat - 40)]

/-- the callee summary of `reciprocalWord` (arm64), for `d1 != 0` (every call site: natdiv.go:586, 655) -/
theorem recip_summary : Summary program entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 48 ∧ StackOK s 88 0 ∧
      (s.regs 0).toNat ≠ 0 ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 88)
    Post := by
  intro s hpc ⟨h30a, h30b, hg, hst, hy, hgA⟩
  unfold Apart at hgA
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  have hn := FvModexp.AsmDiv.clz_norm64 (s.regs 0).toNat hy (s.regs 0).isLt
  generalize hc : clzNat 64 (s.regs 0).toNat = c at hn
  obtain ⟨hc63, hU1, hU2⟩ := hn
  have hcm : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hcl : (c < 64) = True := by simp; omega
  have hc6 : c % 64 = c := Nat.mod_eq_of_lt (by omega)
  have hU : s.regs 0 <<< c = BitVec.ofNat 64 ((s.regs 0).toNat * 2 ^ c) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have hUv : (BitVec.ofNat 64 ((s.regs 0).toNat * 2 ^ c)).toNat = (s.regs 0).toNat * 2 ^ c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hU2
  have hUn : (~~~BitVec.ofNat 64 ((s.regs 0).toNat * 2 ^ c)).toNat = 2 ^ 64 - 1 - (s.regs 0).toNat * 2 ^ c := by
    rw [BitVec.toNat_not, hUv]
  janus_run [Post, hc, hcm, hcl, hc6, hU, hUv, hUn] calls [div64]
  rename_i h0 _ hR hM _
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [h0, BitVec.toNat_ofNat]
    unfold FvModexp.AsmDiv.recipWord
    rw [hc, recip_val _ hU1 hU2, Nat.mod_eq_of_lt (recip_lt _ hU1)]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hR i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]
    simp only [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, if_false]
  · refine ⟨fun a n ha => ?_, fun a n w => ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at ha
      rw [hM.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    · rw [hM.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]

/-- the standalone contract: `reciprocalWord(d1)` with `d1 != 0` returns `recipWord d1`; memory changes only in its
88-byte stack area below `SP` (own frame + `Div64`'s) -/
theorem ensures (d1 : BitVec 64) :
    Ensures program entry [d1]
      (fun s => GuardOK s 48 ∧ StackOK s 88 0 ∧ d1.toNat ≠ 0 ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 88)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord d1.toNat)] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat - 40)]) := by
  refine FvModexp.AsmDiv.A64.ensures_of_summary (hinv := by janus_pre_setRet [Janus.Spec.GuardOK, Janus.Spec.StackOK]) _ _ recip_summary ?_ ?_
  · intro ret hret s hsu ⟨hg, hst, hy, hgA⟩
    have h0 : s.regs 0 = d1 := by have := hsu.args 0 (by simp); simpa using this
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := hsu.lr
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hst, ?_, hgA⟩
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h0]; exact hy
  · intro ret hret s hsu _ s' ⟨hpc, hsp, e0, h18, h28, h29, _, _, hf⟩
    have h0 : s.regs 0 = d1 := by have := hsu.args 0 (by simp); simpa using this
    rw [h0] at e0
    refine ⟨⟨hsp, h28, h29, h18⟩, ?_, hf⟩
    simp only [results, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
    rw [← e0]

end FvModexp.Arm64.RecipWordSum
