import FvModexp.Proofs.Arm64.Nat.RshAlloc
import FvModexp.Proofs.Arm64.Nat.RshZero
import FvModexp.Proofs.Arm64.Nat.RshSetA

/-!
# `nat.rsh` (arm64): the summary

`full`: `s = 0` (`cap z = 0`: `z.set(x)`), `len x ≤ s/64` (`z[:0]`), else reuse / allocate × copy / shift; `ens : Hyp`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Rsh

set_option maxRecDepth 20000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (hsh : sh < 2 ^ 64) :
    Summary (LibRsh.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
        s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧ s.regs 3 = BitVec.ofNat 64 x ∧
        s.regs 4 = BitVec.ofNat 64 xl ∧ s.regs 5 = BitVec.ofNat 64 xc ∧ s.regs 6 = BitVec.ofNat 64 sh ∧
        Pre R b L zp zl zc x xl sh s ∧ xl ≤ xc ∧ xc < 2 ^ 40)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre, hxc, hxc'⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibRsh.program.link impl) := by
    rw [LibRsh.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRsh.names
  have c1 : CodeIn ((Extracted.program.onlySegments [rshVUfn]).link impl) (LibRsh.program.link impl) := by
    rw [LibRsh.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hRsh := fun b L => RshVUHyp.live (Summary.of_codeIn c1 (rshVUHyp impl hap)) R b L
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  have hor : 0 < sh ∨ zc = 0 := hpre.2.2.2.2.2.2.2.2.2.1
  by_cases hs0 : sh = 0
  · subst hs0
    exact setAlloc impl R hmk' hmv' b L zp zl zc x xl xc 0 s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega) hpre
  by_cases hq : xl ≤ sh / 64
  · exact zeroPath impl R b L zp zl zc x xl xc sh s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega) hsh hq hpre
  have hn0 : 0 < need xl sh := by simp only [need]; omega
  by_cases hz : need xl sh ≤ zc
  · exact mainReuse impl R hRsh hmv' b L zp zl zc x xl xc sh s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hxc hxc' (by omega)
      hn0 hz hpre
  · exact mainAlloc impl R hRsh hmk' hmv' b L zp zl zc x xl xc sh s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hxc hxc'
      (by omega) hn0 (by omega) hpre

/-- **`nat.rsh`** (arm64): `z.rsh(x, s)` (`z` apart from `x`, `x` normalised and non-empty, `s = 0` only with
`cap z = 0`) returns a normalised nat holding `X / 2^s`, in `z`'s array (`cap z ≥ len x - s/64`) or a fresh one of
capacity `≥ len x - s/64`; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    Hyp impl R names 4240 64 := by
  intro b L z zl zc x xl xc sh
  rw [show names = LibRsh.names from rfl, ← LibRsh.eq_only]
  janus_ensures_old [FvModexp.Arm64.Rsh.RshPre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.win, FvModexp.NatLive]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk hmv b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      sh.toNat sh.isLt)
    hret h_pc h_lr ⟨?_, ?_, by simp [h_x0], by simp [h_x1], by simp [h_x2], by simp [h_x3], by simp [h_x4],
      by simp [h_x5], by simp [h_x6], hpre.1, hpre.2.1, hpre.2.2⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.Rsh
