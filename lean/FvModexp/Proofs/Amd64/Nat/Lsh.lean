import FvModexp.Proofs.Amd64.Nat.LshMain
import FvModexp.Proofs.Amd64.Nat.LshMainA
import FvModexp.Proofs.Amd64.Nat.LshMainB
import FvModexp.Proofs.Amd64.Nat.LshZero

/-!
# `nat.lsh` (amd64): the summaries

`full` (`0 < s`, `0 < len x`: reuse / allocate × copy / shift), `ens : Hyp2` (amd64 twin of `EvenHyp.LshHypA` with
`0 < s ∧ 0 < len x`), `fullZ`/`ensZ : HypZ` (`z.lsh(z, s)`, nat.go:955, `s` may be `0`). Posts carry
`s'.fsBase = s.fsBase ∧ s'.df = s.df` (AMD64 DF CONVENTION).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Lsh

/-- the entry precondition of the internal summaries -/
@[reducible] def EntryP (s : State) (zp zl zc x xl xc sh : Nat) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
    s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧ s.regs 7 = BitVec.ofNat 64 x ∧
    s.regs 6 = BitVec.ofNat 64 xl ∧ s.regs 8 = BitVec.ofNat 64 xc ∧ s.regs 9 = BitVec.ofNat 64 sh

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (hxc : xc < 2 ^ 64) :
    Summary (LibLsh.program.link impl) (segAddr Extracted.program fn)
      (fun s => EntryP s zp zl zc x xl xc sh ∧ Pre R b L zp zl zc x xl sh s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s') := by
  intro s hpc ⟨⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩, hpre⟩
  have he : Entry s zp zl zc x xl xc sh := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibLsh.program.link impl) := by
    rw [LibLsh.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibLsh.names
  have c1 : CodeIn64 ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibLsh.program.link impl) := by
    rw [LibLsh.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hLsh := fun b L => LshVUHyp.live (Summary.of_codeIn64 c1 (lshVUHyp impl hap)) R b L
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  have hmc' := MemclrNoHeapPointersLive64.of_codeIn hc3 hmc
  by_cases hz : need xl sh ≤ zc
  · exact mainReuse impl R hLsh hmv' hmc' b L zp zl zc x xl xc sh s he hxc hz hpre
  · by_cases hr0 : sh % 64 = 0
    · exact mainAllocC impl R hLsh hmk' hmv' hmc' b L zp zl zc x xl xc sh s he hxc (by omega) hr0 hpre
    · exact mainAllocS impl R hLsh hmk' hmv' hmc' b L zp zl zc x xl xc sh s he hxc (by omega) hr0 hpre

/-- **`nat.lsh`** (amd64): `z.lsh(x, s)` (`0 < s`, `0 < len x`, `z = x` allowed) returns a normalised nat holding
`X · 2^s`, in `z`'s array (`cap z ≥ len x + s/64 + 1`) or a fresh one of capacity `≥ len x + s/64 + 1`; writes only
`z`'s array and the window; keeps `FS` and `DF`; no panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R) :
    Hyp2 impl R names 4248 64 := by
  intro b L z zl zc x xl xc sh
  rw [show names = LibLsh.names from rfl, ← LibLsh.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk hmv hmc b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      sh.toNat xc.isLt) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, by simp [h_a0], by simp [h_a1],
      by simp [h_a2], by simp [h_a3], by simp [h_a4], by simp [h_a5], by simp [h_a6]⟩, hpre⟩
    fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

set_option maxRecDepth 20000 in
theorem fullZ (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (hxc : xc < 2 ^ 64) :
    Summary (LibLsh.program.link impl) (segAddr Extracted.program fn)
      (fun s => EntryP s zp zl zc x xl xc sh ∧ PreZ R b L zp zl zc x xl sh s)
      (fun s s' => RegsOK s s' ∧ PostZI R b L zp zc x xl sh s s') := by
  intro s hpc ⟨hE, hpre⟩
  by_cases hs0 : sh = 0
  · subst hs0
    obtain ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := hE
    exact zeroSh impl R b L zp zl zc x xl xc s ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ hpre
  · obtain ⟨hA, hzx, -, hx0, -⟩ := hpre
    obtain ⟨k, s', hs, hr, hR, hq⟩ := full impl hap R hmk hmv hmc b L zp zl zc x xl xc sh hxc s hpc
      ⟨hE, hA, by omega, hx0⟩
    exact ⟨k, s', hs, hr, hR, postI_postZI hq⟩

/-- **`z.lsh(z, s)`** (amd64, nat.go:955; `s` may be `0`): `X · 2^s` normalised, in `z`'s array or a fresh one of
capacity `≥ len x + s/64 + 1`. -/
theorem ensZ (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R) :
    HypZ impl R names 4248 64 := by
  intro b L z zl zc x xl xc sh
  rw [show names = LibLsh.names from rfl, ← LibLsh.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (fullZ impl hap R hmk hmv hmc b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      sh.toNat xc.isLt) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, by simp [h_a0], by simp [h_a1],
      by simp [h_a2], by simp [h_a3], by simp [h_a4], by simp [h_a5], by simp [h_a6]⟩, hpre⟩
    fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

end FvModexp.Amd64.Lsh
