/-! # Small lemmas of the arm64 `Run` proof, proved once outside the big contexts (docs/history/PERF-log.md "agent top s17")

Budget steps: `omega` over a post-run context costs 10-25 s; these close the same goals in milliseconds. -/

namespace FvModexp.Arm64.Run

/-- Budget after `k` header reads (`RelH … k`) and one more `SetBytes` call (`b1 ≤ b2 + makeCost (nW 32)`). -/
theorem bud_step {b b1 b2 m k : Nat} (h1 : b - k * m ≤ b1) (h2 : b1 ≤ b2 + m) : b - (k + 1) * m ≤ b2 := by
  rw [Nat.succ_mul]; omega

end FvModexp.Arm64.Run
