import Janus
import FvModexp.Proofs.Common.Link

/-!
# Conventions for function summaries: the ISA-independent vocabulary

See `docs/CONVENTIONS.md`. Everything here is about `Janus.Arm64.Memory` (the memory of both ISAs), the
live runtime `R : RtInv` and the live set `L`; nothing mentions registers or an `Extracted` program.

Values
* `natVal m p n`   : the value of the `n` 64-bit little-endian limbs at `p` (a Go `nat` = `[]Word`).
* `limbs m p n`    : the same limbs as a `List Nat` (least significant first), for algorithm models.
* `beVal m p n`    : the `n` bytes at `p` read as a big-endian integer (a Go `[]byte` as a number).

Objects and the runtime
* `Held R L a n`   : `[a, a+n)` is held by the caller: inside a live object (`InRanges a n L`) or caller
                     memory outside the runtime (`Outside a n R.rt`, e.g. a stack buffer). What a runtime
                     call can never change (`LiveFrame` / `MemFrame`).
* `NatLive m R L p c` : the backing array `[p, p + 8c)` of a nat of capacity `c` is held, 8-aligned,
                     writable, below `2^48` (nothing for `c = 0`).
* `NatNorm m p n`  : no leading zero limb (`nat.norm`'s postcondition).
* `LiveExt R L L'` : `L'` is `L` plus fresh, pairwise apart runtime objects (what a summary returns).

Costs
* `allocCost n`    : an upper bound of the block of an `n`-byte allocation (`blockSize_le`).
* `makeCap n`, `makeCost n` : the capacity / cost of `nat.make(n)` when it allocates (`nat.go:57`).
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Contracts Janus.Spec

/-! ## Values -/

/-- The value of the `n` limbs at `p`: a little-endian read of `8 n` bytes. -/
@[reducible] def natVal (m : Memory) (p n : Nat) : Nat := m.readLE p (8 * n)

/-- The `n` limbs at `p`, least significant first. -/
def limbs (m : Memory) (p n : Nat) : List Nat := (List.range n).map fun i => m.readLE (p + 8 * i) 8

/-- The value of the `n` bytes at `p`, big-endian (`p` is the most significant byte). -/
def beVal (m : Memory) (p : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => beVal m p n * 256 + (m.bytes (p + n)).toNat

theorem natVal_lt (m : Memory) (p n : Nat) : natVal m p n < 2 ^ (64 * n) := by
  have := Memory.readLE_lt m p (8 * n)
  rwa [show (256 : Nat) ^ (8 * n) = 2 ^ (64 * n) by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this

theorem natVal_succ (m : Memory) (p n : Nat) :
    natVal m p (n + 1) = natVal m p n + 2 ^ (64 * n) * m.readLE (p + 8 * n) 8 := by
  unfold natVal
  rw [show 8 * (n + 1) = 8 * n + 8 by omega, Memory.readLE_add]
  congr 2
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

@[simp] theorem natVal_zero (m : Memory) (p : Nat) : natVal m p 0 = 0 := rfl

/-- The value of `n` limbs is unchanged by a write frame that avoids them. -/
theorem natVal_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p n : Nat}
    (ho : Outside p (8 * n) rs) : natVal m' p n = natVal m p n := h.readLE _ _ ho

@[simp] theorem beVal_zero (m : Memory) (p : Nat) : beVal m p 0 = 0 := rfl

theorem beVal_succ (m : Memory) (p n : Nat) :
    beVal m p (n + 1) = beVal m p n * 256 + (m.bytes (p + n)).toNat := rfl

theorem beVal_lt (m : Memory) (p n : Nat) : beVal m p n < 256 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := (m.bytes (p + n)).isLt
    rw [beVal_succ, Nat.pow_succ]
    have : beVal m p n * 256 + 256 ≤ 256 ^ n * 256 := by
      have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt ih); rw [Nat.succ_mul] at this; exact this
    omega

/-- Splitting a big-endian read: the first `a` bytes are the high part. -/
theorem beVal_add (m : Memory) (p a b : Nat) :
    beVal m p (a + b) = beVal m p a * 256 ^ b + beVal m (p + a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, beVal_succ, ih, beVal_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_assoc]

/-- The bytes are all that matters. -/
theorem beVal_congr {m m' : Memory} {p n : Nat} (h : ∀ i, i < n → m'.bytes (p + i) = m.bytes (p + i)) :
    beVal m' p n = beVal m p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [beVal_succ, beVal_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- A frame that avoids the bytes keeps their big-endian value. -/
theorem beVal_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p n : Nat}
    (ho : Outside p n rs) : beVal m' p n = beVal m p n := by
  apply beVal_congr
  intro i hi
  have h1 := h.readLE (p + i) 1 (Outside.of_sub ho (by omega) (by omega))
  simp only [Memory.readLE_one] at h1
  exact BitVec.eq_of_toNat_eq h1

/-- The same for a live frame (the bytes are in a live object, outside the written ranges). -/
theorem beVal_liveFrame {m m' : Memory} {L ws : List (Nat × Nat)} (h : LiveFrame m m' L ws) {p n : Nat}
    (hin : InRanges p n L) (ho : Outside p n ws) : beVal m' p n = beVal m p n := by
  apply beVal_congr
  intro i hi
  have h1 := h.readLE (p + i) 1 (hin.sub (by omega) (by omega)) (Outside.of_sub ho (by omega) (by omega))
  simp only [Memory.readLE_one] at h1
  exact BitVec.eq_of_toNat_eq h1

/-! ## Objects and the runtime -/

/-- `[a, a + n)` is held by the caller: a sub-range of a live object, or caller memory outside the
runtime-owned ranges. No runtime call (and no summary of this project) changes it unless the summary
names it among the ranges it writes. -/
def Held (R : RtInv) (L : List (Nat × Nat)) (a n : Nat) : Prop := InRanges a n L ∨ Outside a n R.rt

theorem Held.sub {R : RtInv} {L : List (Nat × Nat)} {a n b k : Nat} (h : Held R L b k) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : Held R L a n :=
  h.imp (fun h => h.sub h1 h2) (fun h => h.of_sub h1 h2)

/-- A held range keeps its bytes through a summary's frame (`MemFrame` outside `R.rt ++ ws`,
`LiveFrame` outside `ws`). -/
theorem Held.readLE {R : RtInv} {L ws : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (h : Held R L a n) (hf : MemFrame m m' (R.rt ++ ws)) (hl : LiveFrame m m' L ws) (ho : Outside a n ws) :
    m'.readLE a n = m.readLE a n := by
  rcases h with h | h
  · exact hl.readLE a n h ho
  · exact hf.readLE a n (by simp only [Janus.outside_append]; exact ⟨h, ho⟩)

theorem Held.beVal {R : RtInv} {L ws : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (h : Held R L a n) (hf : MemFrame m m' (R.rt ++ ws)) (hl : LiveFrame m m' L ws) (ho : Outside a n ws) :
    beVal m' a n = beVal m a n := by
  apply beVal_congr
  intro i hi
  have h1 := (h.sub (a := a + i) (n := 1) (by omega) (by omega)).readLE hf hl (Outside.of_sub ho (by omega) (by omega))
  simp only [Memory.readLE_one] at h1
  exact BitVec.eq_of_toNat_eq h1

/-- The backing array `[p, p + 8c)` of a nat of capacity `c`: held, 8-aligned, writable, below `2^48`.
Nothing is required for `c = 0` (the pointer of an empty slice is arbitrary). -/
def NatLive (m : Memory) (R : RtInv) (L : List (Nat × Nat)) (p c : Nat) : Prop :=
  0 < c → p % 8 = 0 ∧ Held R L p (8 * c) ∧ m.accessible p (8 * c) true = true ∧ p + 8 * c ≤ 2 ^ 48

/-- A nat is normalised: no leading zero limb. -/
def NatNorm (m : Memory) (p n : Nat) : Prop := n = 0 ∨ m.readLE (p + 8 * (n - 1)) 8 ≠ 0

/-- `L'` is `L` plus new objects that the runtime allocated: inside `R.rt`, apart from everything in `L`
(and from each other). This is what a summary says about the live set. -/
def LiveExt (R : RtInv) (L L' : List (Nat × Nat)) : Prop :=
  ∃ ns : List (Nat × Nat), L' = L ++ ns ∧
    (∀ r ∈ ns, InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L) ∧
    ns.Pairwise fun a b => Apart a.1 (a.2 - a.1) b.1 (b.2 - b.1)

theorem LiveExt.refl (R : RtInv) (L : List (Nat × Nat)) : LiveExt R L L :=
  ⟨[], by simp, by simp, List.Pairwise.nil⟩

theorem LiveExt.mem_old {R : RtInv} {L L' : List (Nat × Nat)} (h : LiveExt R L L') {r : Nat × Nat}
    (hr : r ∈ L) : r ∈ L' := by
  obtain ⟨ns, rfl, -⟩ := h; exact List.mem_append_left _ hr

theorem LiveExt.inRanges_old {R : RtInv} {L L' : List (Nat × Nat)} (h : LiveExt R L L') {a n : Nat}
    (hr : InRanges a n L) : InRanges a n L' :=
  hr.of_subset fun _ hr => h.mem_old hr

theorem LiveExt.held {R : RtInv} {L L' : List (Nat × Nat)} (h : LiveExt R L L') {a n : Nat}
    (hr : Held R L a n) : Held R L' a n :=
  hr.imp h.inRanges_old id

theorem LiveExt.trans {R : RtInv} {L L' L'' : List (Nat × Nat)} (h : LiveExt R L L')
    (h' : LiveExt R L' L'') : LiveExt R L L'' := by
  obtain ⟨ns, rfl, hn1, hn2⟩ := h
  obtain ⟨ms, rfl, hm1, hm2⟩ := h'
  refine ⟨ns ++ ms, by simp, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hn1 r hr
    · obtain ⟨h1, h2⟩ := hm1 r hr
      refine ⟨h1, fun q hq => h2 q (List.mem_append_left _ hq)⟩
  · rw [List.pairwise_append]
    refine ⟨hn2, hm2, fun a ha b hb => ?_⟩
    exact ((hm1 b hb).2 a (List.mem_append_right _ ha)).symm

/-- One fresh object. -/
theorem LiveExt.single {R : RtInv} {L : List (Nat × Nat)} {lo hi : Nat}
    (h1 : InRanges lo (hi - lo) R.rt) (h2 : ApartAll lo (hi - lo) L) : LiveExt R L (L ++ [(lo, hi)]) :=
  ⟨[(lo, hi)], rfl, by simpa using ⟨h1, h2⟩, by simp⟩

/-! ## Costs -/

/-- The allocation budget bound used by summaries: a block of `bytes` bytes costs at most
`allocCost bytes` (`blockSize_le`, any noscan flag). -/
def allocCost (bytes : Nat) : Nat := 2 * bytes + 24

theorem blockSize_le_allocCost (bytes : Nat) (noscan : Bool) :
    blockSize bytes noscan ≤ allocCost bytes := Janus.Contracts.blockSize_le bytes noscan

/-- The capacity `nat.make(n)` allocates (`nat.go:57`): `1` for `n = 1`, else `n + 4`. -/
def makeCap (n : Nat) : Nat := if n = 1 then 1 else n + 4

/-- The budget `nat.make(n)` may consume: the block of its `makeslice(Word, n, makeCap n)`. -/
def makeCost (n : Nat) : Nat := allocCost (8 * makeCap n)

theorem le_makeCap (n : Nat) : n ≤ makeCap n := by unfold makeCap; split <;> omega

/-! ## Frames -/

/-- A frame with no written ranges holds with any. -/
theorem LiveFrame.of_nil' {m m' : Memory} {L : List (Nat × Nat)} (h : LiveFrame m m' L []) (ws : List (Nat × Nat)) :
    LiveFrame m m' L ws := ⟨fun a n hin _ => h.readLE a n hin trivial⟩

/-- A store inside one of the written ranges `ws` keeps the live frame. -/
theorem LiveFrame.writeLE_ws {m m' : Memory} {L ws : List (Nat × Nat)} (h : LiveFrame m m' L ws) {a k : Nat}
    (v : Nat) (hin : InRanges a k ws) : LiveFrame m (m'.writeLE a k v) L ws :=
  ⟨fun b n hb hw => by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := MemFrame.outside_mem hw hr
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h.readLE b n hb hw⟩

/-- The object just added to the live set. -/
theorem inRanges_snoc (L : List (Nat × Nat)) (a n : Nat) : InRanges a n (L ++ [(a, a + n)]) :=
  ⟨(a, a + n), by simp, Nat.le_refl _, Nat.le_refl _⟩

/-- A store into a live object keeps the invariant. -/
theorem inv_store_live {R : RtInv} {b g a n v : Nat} {L : List (Nat × Nat)} {m : Memory}
    (h : R.inv b L g (view R.rt L m)) (hin : InRanges a n L) : R.inv b L g (view R.rt L (m.writeLE a n v)) := by
  rw [view_writeLE_live hin]; exact h

/-- A store outside the runtime-owned ranges keeps the invariant. -/
theorem inv_store_out {R : RtInv} {b g a n v : Nat} {L : List (Nat × Nat)} {m : Memory}
    (h : R.inv b L g (view R.rt L m)) (hout : Outside a n R.rt) : R.inv b L g (view R.rt L (m.writeLE a n v)) := by
  rw [view_writeLE_out hout]; exact h

/-- A store into a held range keeps the invariant. -/
theorem inv_store_held {R : RtInv} {b g a n v : Nat} {L : List (Nat × Nat)} {m : Memory}
    (h : R.inv b L g (view R.rt L m)) (hh : Held R L a n) : R.inv b L g (view R.rt L (m.writeLE a n v)) :=
  hh.elim (inv_store_live h) (inv_store_out h)

end FvModexp
