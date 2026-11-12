import FvModexp.Proofs.Amd64.Top.RunC2Sum
import FvModexp.Proofs.Amd64.Top.RunRA

/-! # `Run` (amd64): the return sites of the `Mod`, `exp` and `Bytes` calls are admissible return addresses of the
callees' programs (proved from the layout, outside the callers' runs: see the arm64 `RunC2RA`). Return sites:
`fn + 0xb94` (after `CALL (*Int).Mod`), `fn + 0xb99` (after the first `CALL (*Int).Bytes`), `fn + 0xbbd` (after
`CALL (*Int).exp`), `fn + 0xbc5` (after the second `CALL (*Int).Bytes`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
theorem raMod (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments RunIface.namesMod).link impl) (0x654340 + 0xb94) :=
  raRun impl hap _ (by decide +kernel) 0xb94 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
theorem raExp (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments RunIface.namesExp).link impl) (0x654340 + 0xbbd) :=
  raRun impl hap _ (by decide +kernel) 0xbbd (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
theorem raBytes (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (h : ret = 0x654340 + 0xb99 ∨ ret = 0x654340 + 0xbc5) :
    RetAddr ((Extracted.program.onlySegments [RunIface.fnBytes]).link impl) ret := by
  rcases h with rfl | rfl
  · exact raRun impl hap _ (by decide +kernel) 0xb99 (by decide +kernel) (by decide)
  · exact raRun impl hap _ (by decide +kernel) 0xbc5 (by decide +kernel) (by decide)

end FvModexp.Amd64.Run
