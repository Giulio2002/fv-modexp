import FvModexp.Proofs.Arm64.Exp.ExpWit
import FvModexp.Proofs.Arm64.Exp.P2DE
import FvModexp.Proofs.Arm64.Exp.P2W4E

set_option autoImplicit false

/-! # The power-of-two rows (arm64): `CalleeInst.nsP` leaves out the power-of-two functions (agent infra) -/

namespace FvModexp.Arm64.P2Wit

open Janus FvModexp

open FvModexp.Arm64.CalleeInst (nsP) in
set_option maxHeartbeats 64000000 in
theorem nf2 : nsP.contains P2W2.fn = false := by decide
open FvModexp.Arm64.CalleeInst (nsP) in
set_option maxHeartbeats 64000000 in
theorem nf4 : nsP.contains P2W4.fn = false := by decide
open FvModexp.Arm64.CalleeInst (nsP) in
set_option maxHeartbeats 64000000 in
theorem nfP : nsP.contains P2Pre.fn = false := by decide
open FvModexp.Arm64.CalleeInst (nsP) in
set_option maxHeartbeats 64000000 in
theorem nfD : nsP.contains NHyp.fnP2 = false := by decide

end FvModexp.Arm64.P2Wit
