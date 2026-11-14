import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.Nat.Rsh

set_option autoImplicit false

/-!
# The exp layer (amd64): the closed `nat.shr` instance on `CalleeInstQ.nsQ` (agent asm s69)

`rh : Rsh.Hyp impl R nsQ 4248 64` — asm's amd64 `Rsh.ens` widened to `nsQ` (divmc's `CalleeInstQ`, which leaves
this one instance out). Kept in its own module so `CalleeInstQ` need not import the `nat.shr` proof.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Amd64.EnsWiden (ens_widen)

namespace FvModexp.Amd64.CalleeInstQ

theorem rh {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R) :
    Rsh.Hyp impl R nsQ 4248 64 := fun b L z zl zc x xl xc sh =>
  ens_widen hap subs.2.2.2.2.1 (Rsh.ens impl hap R hmk hmv b L z zl zc x xl xc sh)

end FvModexp.Amd64.CalleeInstQ
