import FvModexp.Proofs.Amd64.Exp.MontHyp
import FvModexp.Proofs.Amd64.AddMulVVWWSum
import FvModexp.Proofs.Amd64.SubVVSum
import FvModexp.Proofs.Common.AsmModel

/-!
# `nat.montgomery` (amd64): discharging the asm-kernel premises with agent asm's verified summaries (see the arm64 twin)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open Janus.Contracts.EqHashModel FvModexp.Amd64.MontHyp

namespace FvModexp.Amd64.MontAsm

theorem codeIn_single {p P : Amd64.Program} {S : Amd64.Segment} (pre post : List Amd64.Segment) (impl : List Amd64.Segment)
    (hp : p.segments = [S]) (hP : P.segments = pre ++ S :: post) (hap : ∀ seg ∈ pre, Amd64.Segment.Apart seg S)
    (hs : ∀ i < S.bytes.length, P.stubAt (S.base + i) = none ∧ S.base + i ≠ P.exitAddr) :
    CodeIn64 p (P.link impl) := by
  intro pc w hf
  have hf' : Amd64.Program.fetchIn [S] pc = some w := by rw [← hp]; exact hf
  simp only [Amd64.Program.fetchIn] at hf'
  split at hf'
  · rename_i hc
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < S.bytes.length ∧ pc = S.base + i := ⟨pc - S.base, by omega, by omega⟩
    refine ⟨?_, (hs i hi).1, (hs i hi).2⟩
    show Amd64.Program.fetchIn (P.segments ++ impl) _ = _
    rw [hP, List.append_assoc]
    have skip : ∀ (l : List Amd64.Segment) (r : List Amd64.Segment), (∀ seg ∈ l, Amd64.Segment.Apart seg S) →
        Amd64.Program.fetchIn (l ++ r) (S.base + i) = Amd64.Program.fetchIn r (S.base + i) := by
      intro l r hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        have := hl a (List.mem_cons_self ..)
        unfold Amd64.Segment.Apart at this
        rw [List.cons_append]
        simp only [Amd64.Program.fetchIn]
        rw [if_neg (by omega)]
        exact ih fun seg h => hl seg (List.mem_cons_of_mem _ h)
    rw [skip pre _ hap, List.cons_append]
    simp only [Amd64.Program.fetchIn]
    rw [if_pos hc]; exact hf'
  · cases hf'

set_option maxRecDepth 100000 in
theorem codeIn_amv (impl : List Amd64.Segment) :
    CodeIn64 FvModexp.Lib.AddMulVVWWAmd64.program (LibMont.program.link impl) :=
  codeIn_single [Extracted.seg24, Extracted.seg59] [] impl (S := Extracted.seg63) (by rfl) (by rfl) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem codeIn_sub (impl : List Amd64.Segment) :
    CodeIn64 FvModexp.Lib.SubVVAmd64.program (LibMont.program.link impl) :=
  codeIn_single [] [Extracted.seg59, Extracted.seg63] impl (S := Extracted.seg24) (by rfl) (by rfl) (by decide) (by decide)

theorem split_of {Z c S P : Nat} (hP : 0 < P) (hZ : Z < P) (h : Z + P * c = S) : Z = S % P ∧ c = S / P :=
  FvModexp.Asm.split_unique hZ (Nat.mod_lt _ hP) (h.trans (Nat.mod_add_div S P).symm)

theorem amv_sum (impl : List Amd64.Segment) :
    Summary0 (LibMont.program.link impl) (segAddr LibMont.program amvFn) AmvPre AmvQ := by
  have e : segAddr LibMont.program amvFn = FvModexp.Lib.AddMulVVWWAmd64.entry := by decide
  rw [e]
  refine Summary.mono (Summary.of_codeIn64 (codeIn_amv impl) FvModexp.Amd64.AddMulVVWWSum.addMulVVWW_summary)
    (fun s h => ?_) (fun s s' _ h => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, h3, h2, h4, h5, h6, h7, h8, h9, Or.inr h10, h11⟩
  · obtain ⟨junk, f, v, vh, mx, m, z, rfl, hmx, hq, hf⟩ := h
    refine ⟨junk, f, v, vh, mx, m, z, rfl, hmx, ?_⟩
    have hP : 0 < 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) := Nat.two_pow_pos _
    obtain ⟨e1, e2⟩ := split_of hP (FvModexp.Asm.lv_lt _ _ _) hq
    exact ⟨e1, e2, hf⟩

theorem sub_sum (impl : List Amd64.Segment) :
    Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ := by
  have e : segAddr LibMont.program subFn = FvModexp.Lib.SubVVAmd64.entry := by decide
  rw [e]
  refine Summary.mono (Summary.of_codeIn64 (codeIn_sub impl) FvModexp.Amd64.SubVVSum.subVV_summary)
    (fun s h => ?_) (fun s s' _ h => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, h3, h2, h4, h5, h6, h7, Or.inr h8, Or.inr h9, h10⟩
  · obtain ⟨junk, f, v, vh, mx, m, z, rfl, hmx, hq, hb, hf⟩ := h
    refine ⟨junk, f, v, vh, mx, m, z, rfl, hmx, ?_, hf⟩
    have hP : 0 < 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) := Nat.two_pow_pos _
    have hZ := FvModexp.Asm.lv_lt m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)
    have hX := FvModexp.Asm.lv_lt s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)
    have hY := FvModexp.Asm.lv_lt s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)
    unfold FvModexp.Asm.lv at hq hZ hX hY
    generalize 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) = P at hq hZ hX hY hP ⊢
    split at hb
    · rw [hb, Nat.mul_one] at hq
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hb, Nat.mul_zero, Nat.add_zero] at hq
      generalize s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) = X at hq hX ⊢
      generalize s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) = Y at hq hY ⊢
      rw [show X + P - Y = (X - Y) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

end FvModexp.Amd64.MontAsm
