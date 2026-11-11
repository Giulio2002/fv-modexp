import FvModexp.Proofs.Arm64.Top.LibRun
import FvModexp.Proofs.Arm64.Nat.SetBytes
import FvModexp.Proofs.Arm64.Nat.SetBytesStd

/-! # `Run` (arm64): the callee summaries on the Run library program `LibRun.program` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.RunCallees

set_option linter.defProp false in
/-- std `nat.setBytes` as a callee of `Run`. -/
def sbStd (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R) :=
  fun (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) =>
    (LibRun.eq_only ▸ SetBytesStd.sum impl hap R hmk b L zp zl zc bp bl bc LibRun.names (fun x hx => by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hx; subst hx; decide) :
      Summary (LibRun.program.link impl) _ _ _)

set_option linter.defProp false in
/-- go-bigmodexpfix `nat.setBytes` as a callee of `Run`. -/
def sbFix (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R) :=
  fun (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) =>
    (LibRun.eq_only ▸ SetBytes.sum impl hap R hmk b L zp zl zc bp bl bc LibRun.names (fun x hx => by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hx; subst hx; decide) :
      Summary (LibRun.program.link impl) _ _ _)

end FvModexp.Arm64.RunCallees

namespace FvModexp.Arm64.RunCallees

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The data frame of a `setBytes` post: `DataLoaded` survives (the written ranges are the window and `z`'s array). -/
theorem setBytes_data {R : RtInv} {L : List (Nat × Nat)} {s s' : State} {zp zc : Nat} {ws : List (Nat × Nat)}
    (hd : Extracted.program.DataLoaded s.mem) (hreg : s'.mem.regions = s.mem.regions) (hro : RoOut R)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 48) true = true) (hsp : 4160 ≤ s.sp.toNat)
    (hlive : NatLive s.mem R L zp zc)
    (hws : ws = winA s 4160 48 ++ [(zp, zp + 8 * zc)])
    (hf : MemFrame s.mem s'.mem (R.rt ++ winA s 4160 48 ++ [(zp, zp + 8 * zc)])) :
    Extracted.program.DataLoaded s'.mem := by
  subst hws
  refine dataLoaded_frame hd hreg hro (by rw [List.append_assoc] at hf; exact hf) fun r hr hlt => ?_
  simp only [winA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact Memory.accessible_mono _ hw (Nat.le_refl _) (by simp; omega)
  · exact Memory.accessible_mono _ hw (by simp; omega) (by simp; omega)
  · obtain ⟨-, -, hacc, -⟩ := hlive (by simp at hlt; omega)
    simpa using hacc

end FvModexp.Arm64.RunCallees

namespace FvModexp.Arm64.RunCallees

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- `sbStd` whose post also says the read-only data is still loaded. -/
theorem sbStdD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) :
    Summary (LibRun.program.link impl) (segAddr Extracted.program SetBytesStd.fn)
      (fun s => RetAddr ((Extracted.program.onlySegments [SetBytesStd.fn]).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, bp, bl, bc] ∧ SetBytesStd.Pre R b L zp zc bp bl s)
      (fun s s' => ((s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        SetBytesStd.Post R b L zp zc bp bl s s') ∧ Extracted.program.DataLoaded s'.mem) := by
  refine Summary.mono (sbStd impl hap R hmk b L zp zl zc bp bl bc).regions (fun s h => h) fun s s' hs ⟨hp, hreg⟩ =>
    ⟨hp, ?_⟩
  obtain ⟨-, -, ⟨⟨-, ⟨-, hsp, -, hw⟩, hd, -, -, -, -, hro⟩, -, hlive, -⟩⟩ := hs
  obtain ⟨-, ⟨p', n', c', -, -, -, -, -, -, -, L', b', -, -, -, -, -, hf, -⟩⟩ := hp
  exact setBytes_data hd hreg hro hw hsp hlive rfl hf

/-- `sbFix` whose post also says the read-only data is still loaded. -/
theorem sbFixD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) :
    Summary (LibRun.program.link impl) (segAddr Extracted.program SetBytes.fn)
      (fun s => RetAddr ((Extracted.program.onlySegments [SetBytes.fn]).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, bp, bl, bc] ∧ SetBytes.Pre R b L zp zc bp bl s)
      (fun s s' => ((s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        SetBytes.Post R b L zp zc bp bl s s') ∧ Extracted.program.DataLoaded s'.mem) := by
  refine Summary.mono (sbFix impl hap R hmk b L zp zl zc bp bl bc).regions (fun s h => h) fun s s' hs ⟨hp, hreg⟩ =>
    ⟨hp, ?_⟩
  obtain ⟨-, -, ⟨⟨-, ⟨-, hsp, -, hw⟩, hd, -, -, -, -, hro⟩, -, hlive, -⟩⟩ := hs
  obtain ⟨-, ⟨p', n', c', -, -, -, -, -, -, -, L', b', -, -, -, -, -, hf, -⟩⟩ := hp
  exact setBytes_data hd hreg hro hw hsp hlive rfl hf

end FvModexp.Arm64.RunCallees
