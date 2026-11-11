import FvModexp.Proofs.Amd64.Nat.RshMainA
import FvModexp.Proofs.Amd64.Nat.RshMainB
import FvModexp.Proofs.Amd64.Nat.RshZero
import FvModexp.Proofs.Amd64.Nat.RshSetA

/-!
# `nat.rsh` (amd64): the summary

`full`: `s = 0` (`cap z = 0`: `z.set(x)`), `len x ≤ s/64` (`z[:0]`), else reuse / allocate (`n ≠ 1`, `n = 1`) ×
copy / shift; `ens : Hyp` (posts with `s'.fsBase = s.fsBase ∧ s'.df = s.df`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Rsh

/-- the entry precondition of the internal summary -/
@[reducible] def EntryP (s : State) (zp zl zc x xl xc sh : Nat) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
    s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧ s.regs 7 = BitVec.ofNat 64 x ∧
    s.regs 6 = BitVec.ofNat 64 xl ∧ s.regs 8 = BitVec.ofNat 64 xc ∧ s.regs 9 = BitVec.ofNat 64 sh

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (hsh : sh < 2 ^ 64) :
    Summary (LibRsh.program.link impl) (segAddr Extracted.program fn)
      (fun s => EntryP s zp zl zc x xl xc sh ∧ Pre R b L zp zl zc x xl sh s ∧ xl ≤ xc ∧ xc < 2 ^ 40)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s') := by
  intro s hpc ⟨⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩, hpre, hxc, hxc'⟩
  have he : Entry s zp zl zc x xl xc sh := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibRsh.program.link impl) := by
    rw [LibRsh.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRsh.names
  have c1 : CodeIn64 ((Extracted.program.onlySegments [rshVUfn]).link impl) (LibRsh.program.link impl) := by
    rw [LibRsh.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hRsh := fun b L => RshVUHyp.live (Summary.of_codeIn64 c1 (rshVUHyp impl hap)) R b L
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  have hor : 0 < sh ∨ zc = 0 := hpre.2.2.2.2.2.2.2.2.2.1
  by_cases hs0 : sh = 0
  · subst hs0
    exact setAlloc impl R hmk' hmv' b L zp zl zc x xl xc s he (by omega) hpre
  by_cases hq : xl ≤ sh / 64
  · exact zeroPath impl R b L zp zl zc x xl xc sh s he (by omega) hsh hq hpre
  have hn0 : 0 < need xl sh := by simp only [need]; omega
  by_cases hz : need xl sh ≤ zc
  · exact mainReuse impl R hRsh hmv' b L zp zl zc x xl xc sh s he hxc hxc' hsh (by omega) hn0 hz hpre
  · by_cases hn1 : need xl sh = 1
    · exact mainAlloc1 impl R hRsh hmk' hmv' b L zp zl zc x xl xc sh s he hxc hxc' hsh (by omega) hn0 (by omega)
        hn1 hpre
    · exact mainAlloc4 impl R hRsh hmk' hmv' b L zp zl zc x xl xc sh s he hxc hxc' hsh (by omega) hn0 (by omega)
        hn1 hpre

/-- **`nat.rsh`** (amd64): `z.rsh(x, s)` (`z` apart from `x`, `x` normalised and non-empty, `s = 0` only with
`cap z = 0`) returns a normalised nat holding `X / 2^s`, in `z`'s array (`cap z ≥ len x - s/64`) or a fresh one of
capacity `≥ len x - s/64`; writes only `z`'s array and the window; keeps `FS` and `DF`; no panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    Hyp impl R names 4248 64 := by
  intro b L z zl zc x xl xc sh
  rw [show names = LibRsh.names from rfl, ← LibRsh.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk hmv b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      sh.toNat sh.isLt) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, by simp [h_a0], by simp [h_a1],
      by simp [h_a2], by simp [h_a3], by simp [h_a4], by simp [h_a5], by simp [h_a6]⟩, hpre.1, hpre.2.1, hpre.2.2⟩
    fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

end FvModexp.Amd64.Rsh
