/-! # `Box`: an opaque wrapper hiding a hypothesis from `omega` / `janus_run`'s context splitting (arm64 Run modules)

`omega`'s cost grows with every disjunctive hypothesis in scope; wrap such facts in a `Box` after their last implicit
use and unwrap (`.h`) only inside the `have` that needs them (docs/PERF.md "agent top s13/s16"). -/

namespace FvModexp.Arm64.Run

structure Box (P : Prop) : Prop where
  h : P

end FvModexp.Arm64.Run
