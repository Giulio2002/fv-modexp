import FvModexp.Proofs.Arm64.Conv

/-! # `Run` (arm64): the goroutine's `stackguard0` slot survives a frame change of the `Run` window

Proved once with a three-fact context (it used to be an inline `omega` in every segment module, paying for the whole
segment context: up to 38 s; docs/history/PERF-log.md "agent top s18"). -/

open Janus Janus.Arm64

namespace FvModexp.Arm64.Run

theorem gS_read {m m' : Memory} {rt : List (Nat × Nat)} {s : State} {g : Nat}
    (hMF : MemFrame m m' (rt ++ winA s 4800 40)) (hga : Apart g 8 (s.sp.toNat - 4800) (4800 + 40))
    (hgr : Outside g 8 rt) : m'.readLE g 8 = m.readLE g 8 :=
  hMF.readLE _ _ (by
    simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    unfold Apart at hga; exact ⟨hgr, by omega, by omega⟩)

end FvModexp.Arm64.Run
