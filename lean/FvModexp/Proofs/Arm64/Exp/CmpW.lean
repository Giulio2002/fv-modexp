import FvModexp.Proofs.Arm64.CmpSum
import FvModexp.Proofs.Arm64.Exp.MontAsm
import FvModexp.Proofs.Arm64.Exp.LibExp

/-!
# `nat.cmp` (agent asm's verified `CmpSum.cmp_summary`) as a callee in the exp layer's program `LibExp` (arm64)

`cmp_summary` is proved on asm's single-segment library program; `codeIn_single` moves it into `LibExp.program.link impl`
(segment `Extracted.seg15`, entry `0x1b3350 = 1782608`). Its precondition has no `DataLoaded`/live-set parts, so a caller
uses it with `Reaches.call` at the callee entry.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.CmpW

set_option maxRecDepth 100000 in
theorem codeIn (impl : List Segment) : Janus.Contracts.EqHashModel.CodeIn FvModexp.Lib.CmpA64.program (LibExp.program.link impl) :=
  MontAsm.codeIn_single [Extracted.seg3, Extracted.seg5, Extracted.seg6, Extracted.seg7, Extracted.seg8, Extracted.seg9, Extracted.seg10, Extracted.seg11, Extracted.seg12, Extracted.seg13, Extracted.seg14]
    [Extracted.seg16, Extracted.seg17, Extracted.seg18, Extracted.seg19, Extracted.seg20, Extracted.seg21, Extracted.seg22, Extracted.seg23, Extracted.seg24, Extracted.seg25, Extracted.seg26, Extracted.seg27, Extracted.seg28, Extracted.seg29, Extracted.seg30, Extracted.seg31, Extracted.seg32, Extracted.seg33, Extracted.seg34, Extracted.seg35, Extracted.seg36, Extracted.seg37, Extracted.seg38, Extracted.seg39, Extracted.seg40, Extracted.seg41, Extracted.seg42, Extracted.seg43, Extracted.seg44, Extracted.seg45, Extracted.seg46, Extracted.seg47, Extracted.seg48, Extracted.seg49, Extracted.seg50, Extracted.seg51, Extracted.seg52, Extracted.seg53, Extracted.seg54, Extracted.seg55, Extracted.seg56, Extracted.seg57, Extracted.seg58, Extracted.seg59, Extracted.seg60, Extracted.seg61, Extracted.seg62, Extracted.seg63, Extracted.seg64, Extracted.seg65, Extracted.seg67, Extracted.seg68, Extracted.seg69, Extracted.seg70, Extracted.seg71, Extracted.seg72, Extracted.seg73, Extracted.seg74, Extracted.seg75, Extracted.seg76, Extracted.seg77, Extracted.seg78, Extracted.seg79, Extracted.seg80, Extracted.seg81, Extracted.seg82, Extracted.seg83] impl (S := Extracted.seg15) rfl rfl (by decide) (by decide)

theorem sum (impl : List Segment) :
    Summary (LibExp.program.link impl) 1782608 CmpSum.Pre CmpSum.Post :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn (codeIn impl) CmpSum.cmp_summary

/-- the cmp result word as a value (`-1`, `0`, `1`) -/
theorem cmpRes_lt {m n X Y : Nat} (h : m < n) : CmpSum.cmpRes m n X Y = 18446744073709551615#64 := by
  unfold CmpSum.cmpRes; rw [if_pos h]

theorem cmpRes_eq_lt {n X Y : Nat} (h : X < Y) : CmpSum.cmpRes n n X Y = 18446744073709551615#64 := by
  unfold CmpSum.cmpRes; simp [h]

theorem cmpRes_eq_ge {n X Y : Nat} (h : Y ≤ X) : ∃ v, v ≤ 1 ∧ CmpSum.cmpRes n n X Y = BitVec.ofNat 64 v := by
  unfold CmpSum.cmpRes
  by_cases h2 : Y < X
  · exact ⟨1, by omega, by simp [h2, Nat.not_lt.mpr h]⟩
  · exact ⟨0, by omega, by simp [h2, Nat.not_lt.mpr h]⟩

/-- A call of `nat.cmp` at its entry, continuation form over an opaque return state. -/
theorem call {p : Program} (hsum : Summary p 1782608 CmpSum.Pre CmpSum.Post) {S : State} {Q : Outcome → Prop}
    (hpc : S.pc = BitVec.ofNat 64 1782608) (hpre : CmpSum.Pre S)
    (K : ∀ S' : State, S'.pc = S.regs 30 → S'.sp = S.sp →
      S'.regs 0 = CmpSum.cmpRes (S.regs 1).toNat (S.regs 4).toNat (S.mem.readLE (S.regs 0).toNat (8 * (S.regs 1).toNat))
        (S.mem.readLE (S.regs 3).toNat (8 * (S.regs 4).toNat)) →
      S'.regs 3 = S.regs 3 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      MemFrame S.mem S'.mem [(S.sp.toNat - 24, S.sp.toNat - 8), (S.sp.toNat + 8, S.sp.toNat + 16),
        (S.sp.toNat + 32, S.sp.toNat + 40)] → S'.mem.regions = S.mem.regions → Reaches p S' Q) :
    Reaches p S Q := by
  refine Reaches.call_regions hsum hpc hpre fun s' hr hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  exact K _ hr rfl (by simp [setReg]; rfl) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) hf hrg

/-- `CmpSum.Pre` from Nat-level facts -/
theorem pre_of {S : State} {sp g x xl y yl r : Nat} (hsp : S.sp = BitVec.ofNat 64 sp) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h30 : S.regs 30 = BitVec.ofNat 64 r) (h0 : S.regs 0 = BitVec.ofNat 64 x) (h1 : S.regs 1 = BitVec.ofNat 64 xl)
    (h3 : S.regs 3 = BitVec.ofNat 64 y) (h4 : S.regs 4 = BitVec.ofNat 64 yl)
    (hr : r % 4 = 0) (hr' : r < 2 ^ 56) (hal : sp % 16 = 0) (h24 : 24 ≤ sp) (hsp48 : sp + 40 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp - 24) 64 true = true) (hg : g + 24 ≤ 2 ^ 48)
    (hga : S.mem.accessible (g + 16) 8 false = true) (hgv : S.mem.readLE (g + 16) 8 < sp)
    (hx : xl = 0 ∨ (x + 8 * xl ≤ 2 ^ 48 ∧ S.mem.accessible x (8 * xl) false = true ∧ Apart x (8 * xl) (sp - 24) 64))
    (hy : yl = 0 ∨ (y + 8 * yl ≤ 2 ^ 48 ∧ S.mem.accessible y (8 * yl) false = true ∧ Apart y (8 * yl) (sp - 24) 64)) :
    CmpSum.Pre S := by
  have t : ∀ v, v ≤ 2 ^ 56 → (BitVec.ofNat 64 v).toNat = v := fun v h => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold CmpSum.Pre GuardOK StackOK CmpSum.SliceOK
  rw [hsp, h28, h30, h0, h1, h3, h4, t sp (by omega), t g (by omega), t r (by omega)]
  refine ⟨hr, hr', ⟨hg, hga, by omega⟩, ⟨hal, h24, by omega, hacc⟩, ?_, ?_⟩
  · rcases hx with h | ⟨h1, h2, h3⟩
    · left; subst h; rfl
    · have : xl < 2 ^ 48 := by omega
      rw [t x (by omega), t xl (by omega)]; exact Or.inr ⟨h2, h3⟩
  · rcases hy with h | ⟨h1, h2, h3⟩
    · left; subst h; rfl
    · rw [t y (by omega), t yl (by omega)]; exact Or.inr ⟨h2, h3⟩

end FvModexp.Arm64.CmpW
