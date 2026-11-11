import FvModexp.Proofs.Arm64.Top.RunC2Sum
import FvModexp.Proofs.Arm64.Top.RunRA

/-! # `Run` (arm64): the return sites of the `Mod` and `exp` calls are admissible return addresses of the callees'
programs

`janus_run … calls [expW …]` must prove the callee summary's `RetAddr ((Extracted.program.onlySegments namesExp).link impl)
(X30)` at the call; proved inside the caller's run, the kernel re-checks the segment filter by name (`names.contains`
over every segment) as part of the caller's proof term, which made `RunC2EX`'s exp-call declaration ~3.6 GB of kernel
memory (and a `decide` of the same fact alone 7.1 GB). Here it is proved from the layout: `Run` is the extraction's
first segment, no kept callee is named `Run`, and the segments are pairwise apart (`ImplApart`). The facts enter the
callers as hypotheses (`janus_run` uses a `RetAddr` hypothesis from the context). Return sites: `fn + 0x87c` (after
`CALL (*Int).exp`, `0x20393c`) and `fn + 0x85c` (after `CALL (*Int).Mod`, `0x20391c`). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
theorem raExp (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments RunIface.namesExp).link impl) 2111804 :=
  raRun impl hap _ (by decide) _ (by decide) (fun _ _ h => by cases h; decide) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem raMod (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments RunIface.namesMod).link impl) 2111772 :=
  raRun impl hap _ (by decide) _ (by decide) (fun _ _ h => by cases h; decide) (by decide +kernel)

end FvModexp.Arm64.Run
