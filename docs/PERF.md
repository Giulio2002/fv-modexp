# Performance record (proof elaboration and `janus verify` rows)

Project sanity goal: every `janus verify` row <= 15 min wall and <= 16 GB (hard, `scripts/verify-all.sh` has no override); every proof module's
`lake build` / elaboration <= 5 min and <= 8 GB (target; anything above is profiled and fixed, never given more heartbeats/timeouts/memory);
median row <= 3 min; full run (both ISAs, 6 rows in parallel) <= 2 h.

Procedure for a slow module: `set_option trace.profiler true`, `janus.omega.log` (Janus PROOFS.md section Performance), then split segments,
use summaries, normalise to `Nat`, keep `omega` contexts small, use reducible closers. Record BEFORE and AFTER here.

| date | module / row | before (s, GB) | change | after (s, GB) |
|---|---|---|---|---|
