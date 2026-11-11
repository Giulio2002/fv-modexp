import FvModexp.Proofs.Arm64.Exp.MontHyp
import FvModexp.Proofs.Arm64.AddMulVVWWSum
import FvModexp.Proofs.Arm64.SubVVSum
import FvModexp.Proofs.Common.AsmModel

/-!
# `nat.montgomery` (arm64): discharging the asm-kernel premises with agent asm's verified summaries

`addMulVVWW_summary` / `subVV_summary` (agent asm, proved on their Extracted-free single-segment library programs) are
moved into the montgomery library program (`codeIn_single`) and weakened to the shapes `AmvPre/AmvQ`, `SubPre/SubQ`
that the montgomery proof uses (`Summary.mono`: value equations `Z + 2^(64n) c = X + Y·m + a` turned into
`mod`/`div` form).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel FvModexp.Arm64.MontHyp

namespace FvModexp.Arm64.MontAsm

/-- A single-segment program is code of `P.link impl` when `P` holds its segment after segments apart from it, and
`P` has no stub nor its exit address on it. -/
theorem codeIn_single {p P : Program} {S : Segment} (pre post : List Segment) (impl : List Segment)
    (hp : p.segments = [S]) (hP : P.segments = pre ++ S :: post) (hap : ∀ seg ∈ pre, Segment.Apart seg S)
    (hs : ∀ i < S.words.length, P.stubAt (S.base + 4 * i) = none ∧ S.base + 4 * i ≠ P.exitAddr) :
    CodeIn p (P.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn [S] pc = some w := by rw [← hp]; exact hf
  obtain ⟨i, hi, rfl⟩ := fetchIn_single_some hf'
  have hw : w = S.words[i] := by
    rw [show [S] = S :: [] from rfl, Program.fetchIn_cons_index hi] at hf'; exact (Option.some.inj hf').symm
  refine ⟨?_, (hs i hi).1, (hs i hi).2⟩
  show Program.fetchIn (P.segments ++ impl) _ = _
  rw [hP, List.append_assoc, fetchIn_append_none _ (Program.fetchIn_eq_none fun seg hseg => by
    have := hap seg hseg; unfold Segment.Apart at this; omega), List.cons_append, Program.fetchIn_cons_index hi, hw]

set_option maxRecDepth 100000 in
theorem codeIn_amv (impl : List Segment) : CodeIn FvModexp.Lib.AddMulVVWWA64.program (LibMont.program.link impl) :=
  codeIn_single [Extracted.seg24, Extracted.seg59] [] impl (S := Extracted.seg65) rfl rfl (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem codeIn_sub (impl : List Segment) : CodeIn FvModexp.Lib.SubVVA64.program (LibMont.program.link impl) :=
  codeIn_single [] [Extracted.seg59, Extracted.seg65] impl (S := Extracted.seg24) rfl rfl (by decide) (by decide)

/-- `Z + P c = S`, `Z < P` ⇒ `Z = S mod P`, `c = S / P`. -/
theorem split_of {Z c S P : Nat} (hP : 0 < P) (hZ : Z < P) (h : Z + P * c = S) : Z = S % P ∧ c = S / P :=
  FvModexp.Asm.split_unique hZ (Nat.mod_lt _ hP) (h.trans (Nat.mod_add_div S P).symm)

theorem amv_sum (impl : List Segment) :
    Summary0 (LibMont.program.link impl) (segAddr LibMont.program amvFn) AmvPre AmvQ := by
  have e : segAddr LibMont.program amvFn = FvModexp.Lib.AddMulVVWWA64.entry := by decide
  rw [e]
  refine Summary.mono (Summary.of_codeIn (codeIn_amv impl) FvModexp.Arm64.AddMulVVWWSum.addMulVVWW_summary)
    (fun s h => ?_) (fun s s' _ h => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, Or.inr h10, h11⟩
  · obtain ⟨junk, f, v, fpsr, m, rfl, hq, hf⟩ := h
    refine ⟨junk, f, v, fpsr, m, rfl, ?_⟩
    have hP : 0 < 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) := Nat.two_pow_pos _
    obtain ⟨e1, e2⟩ := split_of hP (FvModexp.Asm.lv_lt _ _ _) hq
    exact ⟨e1, e2, hf⟩

theorem sub_sum (impl : List Segment) :
    Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ := by
  have e : segAddr LibMont.program subFn = FvModexp.Lib.SubVVA64.entry := by decide
  rw [e]
  refine Summary.mono (Summary.of_codeIn (codeIn_sub impl) FvModexp.Arm64.SubVVSum.subVV_summary)
    (fun s h => ?_) (fun s s' _ h => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, Or.inr h9, Or.inr h10, h11⟩
  · obtain ⟨junk, f, v, fpsr, m, rfl, hq, hb, hf⟩ := h
    refine ⟨junk, f, v, fpsr, m, rfl, ?_, hf⟩
    have hP : 0 < 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) := Nat.two_pow_pos _
    have hZ := FvModexp.Asm.lv_lt m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
    have hX := FvModexp.Asm.lv_lt s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
    have hY := FvModexp.Asm.lv_lt s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
    unfold FvModexp.Asm.lv at hq hZ hX hY
    generalize 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) = P at hq hZ hX hY hP ⊢
    split at hb
    · rw [hb, Nat.mul_one] at hq
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hb, Nat.mul_zero, Nat.add_zero] at hq
      rw [show m.readLE _ _ = (s.mem.readLE (s.mem.readLE (s.sp.toNat + 32) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) -
          s.mem.readLE (s.mem.readLE (s.sp.toNat + 56) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8)) by omega]
      rw [show s.mem.readLE (s.mem.readLE (s.sp.toNat + 32) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) + P -
          s.mem.readLE (s.mem.readLE (s.sp.toNat + 56) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) =
          (s.mem.readLE (s.mem.readLE (s.sp.toNat + 32) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) -
          s.mem.readLE (s.mem.readLE (s.sp.toNat + 56) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8)) + P by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end FvModexp.Arm64.MontAsm
