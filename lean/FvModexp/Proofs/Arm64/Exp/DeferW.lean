import FvModexp.Proofs.Arm64.Exp.Defer
import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Arm64.Exp.MontW

/-!
# The `stk.restore` closures as callees in `LibExp` (arm64)

`Defer.sum` (proved on `LibDefer.program`) moved into the exp layer's restricted program `LibExp.program`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.DeferW

def fnW4 : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1"

theorem sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (fn : String)
    (hfn : fn ∈ ["github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1"]) :
    Summary (LibExp.program.link impl) (segAddr LibExp.program fn) Defer.Pre Defer.Post := by
  have hsub : ∀ x, LibDefer.names.contains x = true → LibExp.names.contains x = true :=
    MontW.sub_of_all (by decide)
  have hc := codeIn_restrict_mono hap hsub
  rw [← LibDefer.eq_only, ← LibExp.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn hc (Defer.sum impl fn hfn)
  have e : segAddr LibDefer.program fn = segAddr LibExp.program fn := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [e] at h
  exact h

end FvModexp.Arm64.DeferW
