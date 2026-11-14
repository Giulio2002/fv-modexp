import FvModexp.Proofs.Arm64.Exp.W4Cut
import FvModexp.Proofs.Arm64.Exp.W4RRC
import FvModexp.Proofs.Arm64.Exp.W4Mid2
import FvModexp.Proofs.Arm64.Exp.W4PowAll

/-!
# window-4 (arm64): composition of the cut segments (s67)

`j4Spec` discharges `J4Spec` with `W4Mid2.j4Ret` (`j4 → RET`); `rrSpec` discharges `RRSpec` with `W4RRC.rrRetC`
(`divRet → RET`, itself using `j4Spec` and `p01Spec` = `W4PowAll.p01pow`, the table `powers[0..4)`). `W4FunE` passes `rrSpec` to `W4En.enStep`. The three segments (prologue
`entry → divRet`, `divRet → j4`, `j4 → RET`) are independent modules; only this module imports all of them.
-/

set_option autoImplicit false

namespace FvModexp.Arm64.W4Pro

theorem j4Spec : J4Spec := j4Ret

theorem p01Spec : P01Spec := p01pow

theorem rrSpec : RRSpec := rrRetC (hJ4 := j4Spec) (hP01 := p01Spec)

end FvModexp.Arm64.W4Pro
