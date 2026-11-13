import FvModexp.Proofs.Amd64.Exp.W2CF
import FvModexp.Proofs.Amd64.Exp.W2ZcDefs

set_option autoImplicit false

/-!
# window-2 prologue (amd64): the power table (nat.go:1549-1554) — shared definitions (agent expmc s49)

Twin of `Arm64.W2PowDefs`. `buf = stk.nat(5n)` returns at `p01` = fn+0x852 (`AX = bp`, `CX = cap`); then
`powers[0] = buf[0:n:2n].montgomery(one, RR, …)` (call +0x8fa), `powers[1] = buf[n:2n:3n].montgomery(x, RR, …)`
(call +0x9cf), and the loop `powers[i] = buf[i·n:(i+1)·n:(i+2)·n].montgomery(powers[i-1], powers[1], …)`, head
`CMPQ AX, $0x4` at fn+0xaad (`AX = i`), body fn+0x9f6, call +0xa80, exit `j4` = fn+0xb05. Entry `d` lives at
`bp + 8·(d·n)`, its header at `sp + 0x1b0 + 24·d` (`W2Pro.Ent` with `pp d = bp + 8·(d·n)`, `pcap = 2n`).
Anchor `M0` = the memory at `p01`; every frame word the table code writes is in `pw sp`.
Slots: `bc → 0xf0`, `bp → 0x218`, `3n → 0x148`, `k0 = -t → 0xd8` (written after `p01`), `i+1 → 0x148`, `3i → 0x140`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf InpC)

/-- return of `stk.nat(5n)` -/
abbrev p01 : Nat := 6212690
/-- the table-loop head `CMPQ AX, $0x4` (`AX = i`) -/
abbrev powHead : Nat := 6213293
/-- the end of the table: `z = z.make(2n)` -/
abbrev j4 : Nat := 6213381

/-- the table entry pointer / capacity -/
abbrev tp (bp n : Nat) : Nat → Nat := fun d => bp + 8 * (d * n)
abbrev tc (n : Nat) : Nat → Nat := fun _ => 2 * n

/-- the frame words `p01 → j4` writes: callee window, `k0`, `bc`, `3n`/`3i`/`i+1`, headers, `bp` -/
@[reducible] def pw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4296, sp + 0x60), (sp + 0xd8, sp + 0xe0), (sp + 0xf0, sp + 0xf8), (sp + 0x140, sp + 0x150),
    (sp + 0x1b0, sp + 0x210), (sp + 0x218, sp + 0x220)]

/-- everything `p01 → j4` may change since the anchor -/
@[reducible] def pl (R : RtInv) (sp bp bc : Nat) : List (Nat × Nat) := R.rt ++ pw sp ++ [(bp, bp + 8 * bc)]

@[reducible] def FP (R : RtInv) (L : List (Nat × Nat)) (sp bp bc : Nat) (M0 M : Memory) : Prop :=
  MemFrame M0 M (pl R sp bp bc) ∧ LiveFrame M0 M L [(bp, bp + 8 * bc)]

/-- the static facts of the table at the anchor `M0` (memory-independent but for accessibility / guard words) -/
def PStatic (R : RtInv) (L : List (Nat × Nat)) (g fs sp n mp mc k0 bp bc : Nat) (M0 : Memory) : Prop :=
  Env R L g fs sp M0 ∧ 0 < n ∧ n ≤ 2 ^ 16 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧ k0 < 2 ^ 64 ∧ Inp R L sp n M0 mp ∧
  5 * n ≤ bc ∧ bc < 2 ^ 40 ∧ M0.accessible bp (8 * bc) true = true ∧ bp + 8 * bc ≤ 2 ^ 48 ∧
  (InRanges bp (8 * bc) L ∨ Outside bp (8 * bc) R.rt) ∧ Apart bp (8 * bc) (sp - 4296) (4296 + 0x2a8) ∧
  Apart (g + 16) 8 bp (8 * bc) ∧ Apart (fs - 8) 8 bp (8 * bc) ∧ Apart bp (8 * bc) mp (8 * n) ∧
  (∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])

/-- the frame slots the table reads (at a table state `M`) -/
@[reducible] def PSl (sp n mp mc k0 bp bc : Nat) (M : Memory) : Prop :=
  M.readLE (sp + 0x290) 8 = mp ∧ M.readLE (sp + 0x298) 8 = n ∧ M.readLE (sp + 0x2a0) 8 = mc ∧
  M.readLE (sp + 0xd8) 8 = k0 ∧ M.readLE (sp + 0x78) 8 = 2 * n ∧ M.readLE (sp + 0xf0) 8 = bc ∧
  M.readLE (sp + 0x218) 8 = bp

theorem FP.write {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M : Memory}
    (h : FP R L sp bp bc M0 M) (hLs : LiveSep L [(sp - 4296, sp + 0x2a8)]) (hs : 4296 ≤ sp) {a k : Nat} (v : Nat)
    (hw : (sp - 4296 ≤ a ∧ a + k ≤ sp + 0x60) ∨ (sp + 0xd8 ≤ a ∧ a + k ≤ sp + 0xe0) ∨
      (sp + 0xf0 ≤ a ∧ a + k ≤ sp + 0xf8) ∨ (sp + 0x140 ≤ a ∧ a + k ≤ sp + 0x150) ∨
      (sp + 0x1b0 ≤ a ∧ a + k ≤ sp + 0x210) ∨ (sp + 0x218 ≤ a ∧ a + k ≤ sp + 0x220)) :
    FP R L sp bp bc M0 (M.writeLE a k v) := by
  have hw' : sp - 4296 ≤ a ∧ a + k ≤ sp + 0x2a8 := by omega
  refine ⟨h.1.writeLE_inRanges v ?_, h.2.writeLE v (FvModexp.Expmc.outside_of_liveSep hLs hw'.1 hw'.2)⟩
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4296, sp + 0x60), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 0xd8, sp + 0xe0), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 0xf0, sp + 0xf8), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 0x140, sp + 0x150), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 0x1b0, sp + 0x210), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 0x218, sp + 0x220), by simp [pl, pw], h1, h2⟩

theorem FP.call {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M M' : Memory} {rp rc : Nat}
    (h : FP R L sp bp bc M0 M)
    (hc : MemFrame M M' (R.rt ++ [(sp - 8 - 4288, sp - 8 + 104)] ++ [(rp, rp + 8 * rc)]))
    (hl : LiveFrame M M' L [(rp, rp + 8 * rc)]) (hr : bp ≤ rp ∧ rp + 8 * rc ≤ bp + 8 * bc) (hs : 4296 ≤ sp) :
    FP R L sp bp bc M0 M' := by
  refine ⟨h.1.trans hc (fun a n ho => ⟨ho, ?_⟩),
    h.2.trans (FvModexp.Expmc.liveFrame_widen hl (fun a n ho => ?_)) (fun _ _ h => h)⟩
  · simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega

/-- a frame slot outside `pw` reads as at the anchor -/
theorem FP.slot {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 bp bc : Nat} {M0 M : Memory}
    (hs : PStatic R L g fs sp n mp mc k0 bp bc M0) (h : FP R L sp bp bc M0 M) {K : Nat} (h1 : 0x60 ≤ K)
    (h2 : K + 8 ≤ 0x2a8) (hw : Outside (sp + K) 8 (pw sp)) : M.readLE (sp + K) 8 = M0.readLE (sp + K) 8 := by
  have hs0 : 4296 ≤ sp := hs.1.2.1
  have hrt : Outside (sp + K) 8 R.rt := hs.1.2.2.2.2.2.2.2.1.of_sub (by omega) (by omega)
  have u1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at u1
  refine h.1.readLE _ _ ?_
  simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true] at hw ⊢
  exact ⟨⟨hrt, hw⟩, by omega⟩

/-- a held object apart from the frame and from `buf` reads as at the anchor -/
theorem FP.read {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M : Memory} {a k : Nat}
    (h : FP R L sp bp bc M0 M) (hh : InRanges a k L ∨ Outside a k R.rt) (hs : 4296 ≤ sp)
    (h1 : Apart a k (sp - 4296) (4296 + 0x2a8)) (h2 : Apart a k bp (8 * bc)) : M.readLE a k = M0.readLE a k := by
  unfold Apart at h1 h2
  exact FvModexp.Expmc.held_readLE hh h.1 h.2 (by simp only [pw, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)

theorem rd_w8 {m : Memory} {a b v : Nat} (h : a = b) (hv : v < 2 ^ 64) : (m.writeLE a 8 v).readLE b 8 = v := by
  subst h; rw [Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at hv ⊢; exact hv)

/-- a table slice `buf[d·n : … : (d+2)·n]` (`d ≤ 3`) is a montgomery result buffer -/
theorem buf_sub {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g fs sp n mp mc k0 bp bc M0) {d : Nat} (hd : d ≤ 3) :
    Buf R L g fs sp n M0 (bp + 8 * (d * n)) (2 * n) := by
  obtain ⟨-, hn, hn16, -, -, -, -, hbc, hbc', hba, hbb, hbh, hbw, hbg, hbf, -⟩ := hs
  have e1 : d * n + 2 * n ≤ bc := by
    have := Nat.mul_le_mul_right n (show d + 2 ≤ 5 by omega); rw [Nat.add_mul] at this; omega
  refine ⟨Nat.le_refl _, by omega, Arm64.Memory.accessible_sub (m := M0) hba (Or.inr rfl) (by omega) (by omega),
    by omega, hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_, ?_, ?_⟩
  · unfold Apart at hbw ⊢; omega
  · unfold Apart at hbg ⊢; omega
  · unfold Apart at hbf ⊢; omega

/-- a table entry is a montgomery input -/
theorem inp_ent {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g fs sp n mp mc k0 bp bc M0) {d : Nat} (hd : d ≤ 4) :
    Inp R L sp n M0 (bp + 8 * (d * n)) := by
  obtain ⟨-, hn, hn16, -, -, -, -, hbc, hbc', hba, hbb, hbh, hbw, -⟩ := hs
  have e1 : d * n + n ≤ bc := by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ 5 by omega); rw [Nat.add_mul] at this; omega
  refine ⟨Arm64.Memory.accessible_sub (m := M0) hba (Or.inr rfl) (by omega) (by omega), by omega,
    hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_⟩
  unfold Apart at hbw ⊢; omega

end FvModexp.Amd64.W2Pro
