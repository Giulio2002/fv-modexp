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

end FvModexp.Arm64.CmpW
