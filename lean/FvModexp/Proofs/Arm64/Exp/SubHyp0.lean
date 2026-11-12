import FvModexp.Proofs.Arm64.Exp.SubMod2NG
import FvModexp.Proofs.Arm64.Nat.NatSub0

set_option autoImplicit false

/-!
# `SubMod2N.SubHypR0` discharged by divmc's empty-tolerant `nat.sub` (`NatSub.ensR0`; agent divmc)

`NatSub.Pre0` has the body of infra's `SubMod2N.SubPre0`, so the premise is `ensR0` itself.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

theorem subHypR0_of (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : SubHypR0 impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatSub.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

end FvModexp.Arm64.SubMod2N
