import FvModexp.Proofs.Amd64.Exp.W4PSpec
import FvModexp.Proofs.Amd64.Exp.W4PowAll
import FvModexp.Proofs.Amd64.Exp.W4Mid2

set_option autoImplicit false

/-!
# window-4 (amd64): the cut statements discharged (divmc s79 import-chain cut)

`p01Spec` = `p01pow` (the table `powers[0..4)`, `p01 → j4`), `j4Spec` = `j4Ret` (`j4 → RET`); `W4FunE` passes them to
`W4RRC.rrSpec`. Only this module imports the table and `j4 → RET` segments.
-/

namespace FvModexp.Amd64.W4Pro

theorem p01Spec : P01Spec := @p01pow

theorem j4Spec : J4Spec := @j4Ret

end FvModexp.Amd64.W4Pro
