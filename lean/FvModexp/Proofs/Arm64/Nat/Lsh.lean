import FvModexp.Proofs.Arm64.Nat.LshMain
import FvModexp.Proofs.Arm64.Nat.LshZero

/-!
# `nat.lsh` (arm64): the summaries

`full` (`0 < s`, `0 < len x`: reuse / allocate × copy / shift), `ens : Hyp2` (= `EvenHyp.LshHypA` with
`0 < s ∧ 0 < len x`), `fullZ`/`ensZ : HypZ` (`z.lsh(z, s)`, nat.go:955, `s` may be `0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Lsh

set_option maxRecDepth 20000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (hxc : xc < 2 ^ 64) :
    Summary (LibLsh.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
        s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧ s.regs 3 = BitVec.ofNat 64 x ∧
        s.regs 4 = BitVec.ofNat 64 xl ∧ s.regs 5 = BitVec.ofNat 64 xc ∧ s.regs 6 = BitVec.ofNat 64 sh ∧
        Pre R b L zp zl zc x xl sh s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibLsh.program.link impl) := by
    rw [LibLsh.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibLsh.names
  have c1 : CodeIn ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibLsh.program.link impl) := by
    rw [LibLsh.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hLsh := fun b L => LshVUHyp.live (Summary.of_codeIn c1 (lshVUHyp impl hap)) R b L
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  have hmc' := MemclrNoHeapPointersLive.of_codeIn hc3 hmc
  by_cases hz : need xl sh ≤ zc
  · exact mainReuse impl R hLsh hmv' hmc' b L zp zl zc x xl xc sh s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hxc hz hpre
  · exact mainAlloc impl R hLsh hmk' hmv' hmc' b L zp zl zc x xl xc sh s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hxc
      (by omega) hpre

/-- **`nat.lsh`** (arm64): `z.lsh(x, s)` (`0 < s`, `0 < len x`, `z = x` allowed) returns a normalised nat holding
`X · 2^s`, in `z`'s array (`cap z ≥ len x + s/64 + 1`) or a fresh one of capacity `≥ len x + s/64 + 1`; writes only
`z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R) :
    Hyp2 impl R names 4256 64 := by
  intro b L z zl zc x xl xc sh
  rw [show names = LibLsh.names from rfl, ← LibLsh.eq_only]
  janus_ensures_old [FvModexp.Arm64.EvenHyp.LshPreA, FvModexp.Arm64.CallEnv, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.win, FvModexp.NatLive]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk hmv hmc b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      sh.toNat xc.isLt)
    hret h_pc h_lr ⟨?_, ?_, by simp [h_x0], by simp [h_x1], by simp [h_x2], by simp [h_x3], by simp [h_x4],
      by simp [h_x5], by simp [h_x6], hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- `Post` (from `ens`) gives `PostZ` -/
theorem post_postZ {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s s' : State}
    (h : Post R b L zp zc x xl sh s s') : PostZ R b L zp zc x xl sh s s' := by
  obtain ⟨p', l', c', h0, h1, h2, L', b', ⟨hv, hn, hl, hc, hlive, hru, hfr⟩, hneed, hrt, hmf, hlf⟩ := h
  refine ⟨p', l', c', h0, h1, h2, L', b', ⟨hv, hn, hl, hc, hlive, ?_⟩, hrt, hmf, hlf⟩
  by_cases hz : xl + sh / 64 + 1 ≤ zc
  · exact Or.inl (hru hz)
  · have hk := hneed (by omega)
    exact Or.inr ⟨hk, hfr (by omega) (by omega)⟩

set_option maxRecDepth 20000 in
theorem fullZ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (hxc : xc < 2 ^ 64) :
    Summary (LibLsh.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
        s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧ s.regs 3 = BitVec.ofNat 64 x ∧
        s.regs 4 = BitVec.ofNat 64 xl ∧ s.regs 5 = BitVec.ofNat 64 xc ∧ s.regs 6 = BitVec.ofNat 64 sh ∧
        PreZ R b L zp zl zc x xl sh s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostZ R b L zp zc x xl sh s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  by_cases hs0 : sh = 0
  · subst hs0
    exact zeroSh impl R b L zp zl zc x xl xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre
  · obtain ⟨hA, hzx, -, hx0, -⟩ := hpre
    obtain ⟨k, s', hs, hr, hk, hq⟩ := full impl hap R hmk hmv hmc b L zp zl zc x xl xc sh hxc s hpc
      ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hA, by omega, hx0⟩
    exact ⟨k, s', hs, hr, hk, post_postZ hq⟩

/-- **`z.lsh(z, s)`** (arm64, nat.go:955; `s` may be `0`): `X · 2^s` normalised, in `z`'s array or a fresh one of
capacity `≥ len x + s/64 + 1`. -/
theorem ensZ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R) :
    HypZ impl R names 4256 64 := by
  intro b L z zl zc x xl xc sh
  rw [show names = LibLsh.names from rfl, ← LibLsh.eq_only]
  janus_ensures_old [FvModexp.Arm64.EvenHyp.LshPreA, FvModexp.NatNorm, FvModexp.Arm64.CallEnv, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.win, FvModexp.NatLive]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (fullZ impl hap R hmk hmv hmc b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      sh.toNat xc.isLt)
    hret h_pc h_lr ⟨?_, ?_, by simp [h_x0], by simp [h_x1], by simp [h_x2], by simp [h_x3], by simp [h_x4],
      by simp [h_x5], by simp [h_x6], hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.Lsh
