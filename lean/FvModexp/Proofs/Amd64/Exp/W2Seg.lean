import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.SegProg

set_option autoImplicit false

/-! window-2 (amd64): its own one-segment program `Extracted.seg35` (`SegProg.one LibW.program`) and `codeIn` (agent divmc s80):
runs inside window-2's code are proved on `W2Seg.P` (one segment walk per pc) and lifted to `LibW.program.link impl` with
`SegProg.lift W2Seg.codeIn`. -/

open Janus.Amd64 Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.W2Seg

/-- window-2's one-segment program -/
@[reducible] def P : Program := SegProg.one LibW.program Extracted.seg35

theorem hpre : ∀ x ∈ [Extracted.seg3, Extracted.seg6, Extracted.seg7, Extracted.seg8, Extracted.seg9, Extracted.seg10, Extracted.seg12, Extracted.seg13, Extracted.seg14, Extracted.seg15, Extracted.seg16, Extracted.seg17, Extracted.seg18, Extracted.seg19, Extracted.seg20, Extracted.seg22, Extracted.seg24, Extracted.seg25, Extracted.seg26, Extracted.seg27, Extracted.seg28, Extracted.seg29, Extracted.seg30, Extracted.seg31, Extracted.seg32, Extracted.seg33, Extracted.seg34], Segment.Apart x Extracted.seg35 := by decide +kernel

theorem hst : ∀ t ∈ LibW.program.stubs, ¬ (Extracted.seg35.base ≤ t.addr ∧ t.addr < Extracted.seg35.base + Extracted.seg35.bytes.length) := by
  decide +kernel

theorem hex : ¬ (Extracted.seg35.base ≤ LibW.program.exitAddr ∧
    LibW.program.exitAddr < Extracted.seg35.base + Extracted.seg35.bytes.length) := by decide +kernel

theorem codeIn {impl : List Segment} : CodeIn64 P (LibW.program.link impl) :=
  SegProg.codeIn_one (pre := [Extracted.seg3, Extracted.seg6, Extracted.seg7, Extracted.seg8, Extracted.seg9, Extracted.seg10, Extracted.seg12, Extracted.seg13, Extracted.seg14, Extracted.seg15, Extracted.seg16, Extracted.seg17, Extracted.seg18, Extracted.seg19, Extracted.seg20, Extracted.seg22, Extracted.seg24, Extracted.seg25, Extracted.seg26, Extracted.seg27, Extracted.seg28, Extracted.seg29, Extracted.seg30, Extracted.seg31, Extracted.seg32, Extracted.seg33, Extracted.seg34])
    (post := [Extracted.seg36, Extracted.seg37, Extracted.seg38, Extracted.seg39, Extracted.seg40, Extracted.seg41, Extracted.seg42, Extracted.seg43, Extracted.seg44, Extracted.seg45, Extracted.seg46, Extracted.seg47, Extracted.seg48, Extracted.seg49, Extracted.seg50, Extracted.seg51, Extracted.seg52, Extracted.seg53, Extracted.seg54, Extracted.seg55, Extracted.seg56, Extracted.seg57, Extracted.seg58, Extracted.seg59, Extracted.seg60, Extracted.seg61, Extracted.seg62, Extracted.seg63, Extracted.seg65, Extracted.seg66, Extracted.seg67, Extracted.seg68, Extracted.seg69, Extracted.seg70, Extracted.seg71, Extracted.seg72, Extracted.seg73, Extracted.seg74, Extracted.seg75, Extracted.seg76, Extracted.seg77, Extracted.seg78, Extracted.seg79, Extracted.seg80, Extracted.seg81]) rfl hpre hst hex

end FvModexp.Amd64.W2Seg
