/-! # `Box`: an opaque wrapper hiding a hypothesis from `omega` / `janus64_run`'s context splitting (amd64 Run modules)

`janus64_run` destructures every conjunction in the context and `omega` pays for every disjunctive hypothesis in scope:
wrap such facts in a `Box` after their last implicit use and unwrap (`.h`) only where needed (docs/history/PERF-log.md "agent top
s16/s18"). -/

namespace FvModexp.Amd64.Run

/-- A fact hidden from `janus64_run` (which destructures every conjunction in the context). -/
structure Box (P : Prop) : Prop where
  h : P

end FvModexp.Amd64.Run
