import FvModexp.Proofs.Amd64.Top.RunDefs

/-! # Small lemmas of the amd64 `Run` proof, proved once outside the big contexts (docs/PERF.md "agent top s17")

* budget steps: `omega` over a post-run context costs 10-25 s; these close the same goals in milliseconds.
* the `errT` descriptor (the `*errors.errorString` type, rodata segment 3): its size word and readability, so the
  `L`-phase modules need no `janus64_data` (≈ 14 s per call). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- Budget after `k` header reads (`RelH … k`) and one more `SetBytes` call (`b1 ≤ b2 + makeCost (nW 32)`). -/
theorem bud_step {b b1 b2 m k : Nat} (h1 : b - k * m ≤ b1) (h2 : b1 ≤ b2 + m) : b - (k + 1) * m ≤ b2 := by
  rw [Nat.succ_mul]; omega

/-- Budget of the `errors.New` return (one 16-byte `newobject`). -/
theorem bud_err {b b1 k : Nat} (h : b - k ≤ b1) : b - (k + allocCost 16) ≤ b1 - 16 := by unfold allocCost; omega

set_option maxRecDepth 20000 in
/-- Both `errT` facts from ONE `janus64_data` (each call evaluates every data segment, ≈ 10 s). -/
theorem errT_data {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE 7355552 8 = 16 ∧ m.accessible 7355552 16 false = true := by
  janus64_data hd
  exact ⟨by rw [h_rodata _ _ (by decide)]; decide, Janus.Arm64.Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩

theorem errT_word {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 7355552 8 = 16 :=
  (errT_data hd).1

theorem errT_acc {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.accessible 7355552 16 false = true :=
  (errT_data hd).2

end FvModexp.Amd64.Run
