import FvModexp.Proofs.Arm64.Exp.W2Cut
import FvModexp.Proofs.Arm64.Exp.W2RRC
import FvModexp.Proofs.Arm64.Exp.W2Mid2
import FvModexp.Proofs.Arm64.Exp.W2PowAll

/-!
# window-2 (arm64): composition of the cut segments (s67)

`j4Spec` discharges `J4Spec` with `W2Mid2.j4Ret` (`j4 → RET`); `rrSpec` discharges `RRSpec` with `W2RRC.rrRetC`
(`divRet → RET`, itself using `j4Spec` and `p01Spec` = `W2PowAll.p01pow`, the table `powers[0..4)`). `W2FunE` passes `rrSpec` to `W2En.enStep`. The three segments (prologue
`entry → divRet`, `divRet → j4`, `j4 → RET`) are independent modules; only this module imports all of them.
-/

set_option autoImplicit false

namespace FvModexp.Arm64.W2Pro

theorem j4Spec : J4Spec := j4Ret

theorem p01Spec : P01Spec := p01pow

theorem rrSpec : RRSpec := rrRetC (hJ4 := j4Spec) (hP01 := p01Spec)

end FvModexp.Arm64.W2Pro
