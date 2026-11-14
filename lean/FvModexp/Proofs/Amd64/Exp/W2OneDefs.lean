import FvModexp.Proofs.Amd64.Exp.W2ZmDefs
import FvModexp.Proofs.Amd64.Exp.W2Posts

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `one := make(nat, numWords); one[0] = 1` (nat.go:1541-1542) — definitions
(agent expmc s49)

Twin of `Arm64.W2One`'s `OnePost`. Code: RR join `rrJ` = fn+0x766 (`AX = n`, RR header in `BX, CX, R8`, `zz` in
`SI, DX`; spills `0x220/0xf8/0x100`, `0x190/0xa0`), `CMPQ AX, $4; JA` → `n ≤ 4`: the frame buffer `sp + 0x150`
(two `MOVUPS X15` = 32 zero bytes); `n > 4`: `makeslice(Word, n, n)` (call +0x7c0); join +0x803 (`JBE` on `n = 0`),
`one → 0x210`, `one[0] = 1`, `var powers [4]nat` zeroed (`0x1b0 … 0x210`), `stk.nat(5n)` (call +0x84d; `5n` is the entry spill `0x148`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

/-- the RR join (after the `len(RR) < numWords` fix-up) -/
abbrev rrJ : Nat := 6212454

/-- the ranges `rrJ → stk.nat entry` writes besides `R.rt` (makeslice window + return slot, spills `0xa0`,
  `0xf8/0x100`, `0x190`, `0x220`, `one` frame buffer, `powers`, `&one`) -/
@[reducible] def ow (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4296, sp + 0x18), (sp + 0xa0, sp + 0xa8), (sp + 0xf8, sp + 0x108), (sp + 0x150, sp + 0x170),
    (sp + 0x190, sp + 0x198), (sp + 0x1b0, sp + 0x218), (sp + 0x220, sp + 0x228)]

theorem ow_in (sp : Nat) : ∀ q ∈ ow sp, sp - 4296 ≤ q.1 ∧ q.2 ≤ sp - 4296 + (4296 + 0x2a8) := by
  intro q hq; simp only [ow, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- a write into one of the `ow` words keeps the frame -/
theorem ow_mf {sp : Nat} {M M' : Memory} (h : MemFrame M M' (ow sp)) {a k : Nat} (v : Nat)
    (hw : (sp - 4296 ≤ a ∧ a + k ≤ sp + 0x18) ∨ (sp + 0xa0 ≤ a ∧ a + k ≤ sp + 0xa8) ∨
      (sp + 0xf8 ≤ a ∧ a + k ≤ sp + 0x108) ∨ (sp + 0x150 ≤ a ∧ a + k ≤ sp + 0x170) ∨
      (sp + 0x190 ≤ a ∧ a + k ≤ sp + 0x198) ∨ (sp + 0x1b0 ≤ a ∧ a + k ≤ sp + 0x218) ∨
      (sp + 0x220 ≤ a ∧ a + k ≤ sp + 0x228)) :
    MemFrame M (M'.writeLE a k v) (ow sp) := by
  refine h.writeLE_inRanges v ?_
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4296, sp + 0x18), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0xa0, sp + 0xa8), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0xf8, sp + 0x108), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x150, sp + 0x170), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x190, sp + 0x198), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x1b0, sp + 0x218), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x220, sp + 0x228), by simp [ow], h1, h2⟩

/-- the facts at the `stk.nat(5n)` call -/
@[reducible] def OnePost (R : RtInv) (L L' : List (Nat × Nat)) (b b' g fs sp n : Nat) (M M' : Memory) (onep : Nat) :
    Prop :=
  Env R L' g fs sp M' ∧ LiveExt R L L' ∧ b - (if 4 < n then blockSize (8 * n) true else 0) ≤ b' ∧
  MemFrame M M' (R.rt ++ ow sp) ∧ LiveFrame M M' L [] ∧ R.inv b' L' g (view R.rt L' M') ∧
  M'.regions = M.regions ∧ M'.readLE (sp + 0x210) 8 = onep ∧ M'.readLE onep (8 * n) = 1 ∧
  ((onep = sp + 0x150 ∧ n ≤ 4) ∨ (InRanges onep (8 * n) L' ∧ InRanges onep (8 * n) R.rt ∧ ApartAll onep (8 * n) L ∧
    M'.accessible onep (8 * n) true = true ∧ onep + 8 * n ≤ 2 ^ 48 ∧ onep % 8 = 0))

theorem rd8 (m : Memory) (a k : Nat) : m.readLE a (8 * (k + 1)) = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) (8 * k) := by
  rw [show 8 * (k + 1) = 8 + 8 * k by omega, Arm64.Memory.readLE_add]

theorem rd_zero (m : Memory) : ∀ (k a : Nat), (∀ j, j < k → m.readLE (a + 8 * j) 8 = 0) → m.readLE a (8 * k) = 0
  | 0, a, _ => by simp
  | k + 1, a, h => by
    rw [rd8, rd_zero m k (a + 8) (fun j hj => by rw [show a + 8 + 8 * j = a + 8 * (j + 1) by omega]; exact h _ (by omega)),
      show m.readLE a 8 = m.readLE (a + 8 * 0) 8 from rfl, h 0 (by omega)]

/-- `one`'s value from its words -/
theorem one_val (m : Memory) (p n : Nat) (hn : 0 < n) (h0 : m.readLE p 8 = 1)
    (hz : ∀ j, j < n - 1 → m.readLE (p + 8 + 8 * j) 8 = 0) : m.readLE p (8 * n) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [rd8, h0, rd_zero m k (p + 8) (fun j hj => hz j (by omega))]

theorem ow_out {R : RtInv} {L : List (Nat × Nat)} {sp : Nat} (h : Outside (sp - 4296) (4296 + 0x2a8) R.rt) :
    ∀ r ∈ ow sp, InRanges r.1 (r.2 - r.1) L ∨ Outside r.1 (r.2 - r.1) R.rt := by
  intro r hr
  simp only [ow, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (h.of_sub (by simp only; omega) (by simp only; omega))

end FvModexp.Amd64.W2Pro
