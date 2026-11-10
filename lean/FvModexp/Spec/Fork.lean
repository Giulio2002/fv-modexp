import EthLib.Base.Fork

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): the fork predicate used by the final statements.

A final statement may not use an instance of a dependency (Janus `CONSUMERS.md`, Extra dependencies), and `fork ≥ .fusaka` is `Fork.fusaka ≤ fork`
through EthLib's `LE Fork` instance. `PostFusaka` states the same thing with plain `Nat` order on the constructor index; `postFusaka_iff` is the bridge. -/

namespace FvModexp.Spec

open EthLib.Base

/-- `fork` is Fusaka or later (EIP-7823 and EIP-7883 are active): the constructor index is at least that of `Fork.fusaka`, in plain `Nat` order. -/
def PostFusaka (fork : Fork) : Prop := Fork.fusaka.ctorIdx ≤ fork.ctorIdx

/-- The bridge to EthLib's order: `PostFusaka fork` is exactly `Fork.fusaka ≤ fork` (EthLib's `LE Fork` is the order of `ctorIdx`). -/
theorem postFusaka_iff (fork : Fork) : PostFusaka fork ↔ Fork.fusaka ≤ fork := Iff.rfl

/-- The same for `fork ≥ .fusaka`, the form used inside the EthLib MODEXP definitions. -/
theorem postFusaka_iff_ge (fork : Fork) : PostFusaka fork ↔ fork ≥ Fork.fusaka := Iff.rfl

end FvModexp.Spec
