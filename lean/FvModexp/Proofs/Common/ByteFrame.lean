import Janus

/-!
# Frames at byte granularity

`MemFrame m m' rs` / `LiveFrame m m' L ws` say that multi-byte reads outside the ranges agree. An EMPTY range `(x, x)`
in `rs` still constrains reads that straddle `x` (`Outside a n [(x, x)]` is `a + n ≤ x ∨ x ≤ a`), although no byte is
in it. Reading byte by byte (`Memory.readLE_congr`) removes that artefact: `MemFrame.of_bytes` /
`LiveFrame.of_bytes` rebuild a frame from single-byte facts, and `MemFrame.byte` / `LiveFrame.byte` give them. Used to
compose frames whose ranges include a nil operand's empty array (`(p, p + 8 * 0)` with an arbitrary pointer `p`).
-/

open Janus Janus.Arm64 Janus.Tactic

set_option autoImplicit false

namespace FvModexp.ByteFrame

theorem MemFrame.byte {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a : Nat}
    (ho : Outside a 1 rs) : m'.bytes a = m.bytes a := by
  have := h.readLE a 1 ho
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

theorem LiveFrame.byte {m m' : Memory} {L ws : List (Nat × Nat)} (h : LiveFrame m m' L ws) {a : Nat}
    (hin : InRanges a 1 L) (ho : Outside a 1 ws) : m'.bytes a = m.bytes a := by
  have := h.readLE a 1 hin ho
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

theorem MemFrame.of_bytes {m m' : Memory} {rs : List (Nat × Nat)}
    (hb : ∀ a, Outside a 1 rs → m'.bytes a = m.bytes a) (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) :
    MemFrame m m' rs :=
  ⟨fun a n ho => Memory.readLE_congr fun i hi => hb (a + i) (ho.of_sub (by omega) (by omega)), hacc⟩

theorem LiveFrame.of_bytes {m m' : Memory} {L ws : List (Nat × Nat)}
    (hb : ∀ a, InRanges a 1 L → Outside a 1 ws → m'.bytes a = m.bytes a) : LiveFrame m m' L ws :=
  ⟨fun a n hin ho => Memory.readLE_congr fun i hi =>
    hb (a + i) (hin.sub (by omega) (by omega)) (ho.of_sub (by omega) (by omega))⟩

/-- a frame stays a frame when its ranges are replaced by ranges that cover the same bytes -/
theorem MemFrame.mono1 {m m' : Memory} {rs rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (sub : ∀ a, Outside a 1 rs' → Outside a 1 rs) : MemFrame m m' rs' :=
  MemFrame.of_bytes (fun a ho => MemFrame.byte h (sub a ho)) h.accessible

theorem LiveFrame.mono1 {m m' : Memory} {L ws ws' : List (Nat × Nat)} (h : LiveFrame m m' L ws)
    (sub : ∀ a, Outside a 1 ws' → Outside a 1 ws) : LiveFrame m m' L ws' :=
  LiveFrame.of_bytes fun a hin ho => LiveFrame.byte h hin (sub a ho)

/-- a byte outside an empty range -/
theorem outside1_empty (a x : Nat) : Outside a 1 [(x, x)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

end FvModexp.ByteFrame
