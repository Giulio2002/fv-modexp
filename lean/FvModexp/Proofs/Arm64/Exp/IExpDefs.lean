import FvModexp.Proofs.Arm64.Exp.NNilD
import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.ByteFrame

/-!
# `(*Int).exp` (arm64): the facts at `nat.expNN`'s return (`AtN`) and byte-level frame arithmetic (pure)

* `AtN`: the facts at `expNN`'s return (memory `M`): the result `(p, l, c)` (`p` the register value, i.e. below
  `2^64`; an empty result's pointer is irrelevant) holds `V = x^y mod m`, normalised, cap
  `< 2^40`, live in `L'`, the old array of `z` or a fresh one; `M` differs from the entry memory only in `R.rt`, the
  window and `z`'s old array (frames at byte granularity: a nil `z` has an empty, arbitrarily placed array).
* `atN_of`: `AtN` from `ExpSpec`'s precondition, the frame of segments A-C and `ExpN.PostNil`.
* `post_of`: `AtN` and segment D's continuation facts (`runD`'s `KF`) give `IntPost` and the result's cap bound.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntOK IntPre IntPost IntV arrW)

/-- `RunIface.arrW` behind an irreducible name: elaborating a statement whose `Outside`/frame list contains the
`if` of `arrW` may evaluate its condition `0 < m.readLE (z + 24) 8` by `whnf` (a byte-by-byte unfolding of `readLE`;
measured: a one-line term proof took 24 s). `zarr_eq` converts. -/
@[irreducible] def ZArr (m : Memory) (zA : Nat) : List (Nat × Nat) := arrW m zA

theorem zarr_eq (m : Memory) (zA : Nat) : ZArr m zA = arrW m zA := by unfold ZArr; rfl

/-- the facts at `expNN`'s return (memory `M`; result `(p, l, c)` holding `V`, live set `L'`, budget `b'`) -/
structure AtN (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (stk above : Nat) (s : State) (zA V p l c b' : Nat)
    (L' : List (Nat × Nat)) (M : Memory) : Prop where
  val : natVal M p l = V
  norm : NatNorm M p l
  lc : l ≤ c
  c40 : c < 2 ^ 40
  p64 : p < 2 ^ 64
  ext : LiveExt R L L'
  bud : b - B ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  live : NatLive M R L' p c
  orf : c = 0 ∨ (p = s.mem.readLE (zA + 8) 8 ∧ c = s.mem.readLE (zA + 24) 8) ∨
    (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s stk above ++ ZArr s.mem zA)
  lf : LiveFrame s.mem M L (ZArr s.mem zA)

/-- an operand's value survives a frame that misses its array -/
theorem natVal_eq0 {m M : Memory} {p l c lo hi : Nat} (hlc : l ≤ c)
    (hout : 0 < c → Outside p (8 * c) [(lo, hi)]) (hF : MemFrame m M [(lo, hi)]) : natVal M p l = natVal m p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; rfl
  · have := hout (by omega)
    exact hF.readLE _ _ (this.of_sub (Nat.le_refl _) (by omega))

/-- a byte outside `z`'s old array as a written range is outside the range `(p, p + 8 c)` of its header fields -/
theorem out_arrW {m : Memory} {zA a : Nat} (h : Outside a 1 (ZArr m zA)) :
    Outside a 1 [(m.readLE (zA + 8) 8, m.readLE (zA + 8) 8 + 8 * m.readLE (zA + 24) 8)] := by
  rw [zarr_eq] at h
  unfold arrW at h
  generalize m.readLE (zA + 8) 8 = p at h ⊢
  generalize m.readLE (zA + 24) 8 = c at h ⊢
  split at h
  · exact h
  · have : c = 0 := by omega
    subst this; exact outside1_empty a p

/-- a range apart from `z`'s old array (when it exists) is outside it as a written range -/
theorem outside_arrW {m : Memory} {zA a k : Nat}
    (h : 0 < m.readLE (zA + 24) 8 → Apart a k (m.readLE (zA + 8) 8) (8 * m.readLE (zA + 24) 8)) :
    Outside a k (ZArr m zA) := by
  rw [zarr_eq]
  unfold arrW
  generalize m.readLE (zA + 8) 8 = p at h ⊢
  generalize m.readLE (zA + 24) 8 = c at h ⊢
  split
  · rename_i hc
    have := h hc; unfold Apart at this
    simp only [outside_cons, outside_nil, and_true]; omega
  · exact trivial

/-- the bytes `expNN` and segments A-C may write lie in `ExpSpec`'s frame -/
theorem out_atN {rt : List (Nat × Nat)} {t stk above K zp zc a : Nat} (hst : stk ≤ t) (hK : K + 1632 ≤ stk)
    (hab : 48 ≤ above) (hR : Outside a 1 rt) (hW : Outside a 1 [(t - stk, t - 8), (t + 8, t + above)])
    (hZ : Outside a 1 [(zp, zp + 8 * zc)]) :
    Outside a 1 (rt ++ [(t - 320 - (K + 1312), t - 320 - 8), (t - 320 + 8, t - 320 + 120)] ++ [(zp, zp + 8 * zc)]) ∧
      Outside a 1 [(t - 328, t - 8), (t + 8, t + 48)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at hW hZ ⊢
  exact ⟨⟨⟨hR, by omega, by omega⟩, hZ⟩, by omega, by omega⟩

/-- the slots of `(*Int).exp`'s frame that `expNN` does not write -/
theorem out_slot {rt : List (Nat × Nat)} {t stk above K zp zc a k i : Nat} (hst : stk ≤ t) (hK : K + 1632 ≤ stk)
    (hab : 48 ≤ above) (hrt : Outside (t - stk) (stk + above) rt)
    (hz : 0 < zc → zp + 8 * zc ≤ t - stk ∨ t + above ≤ zp)
    (ha : (t - 328 ≤ a ∧ a + k ≤ t - 312) ∨ (t - 200 ≤ a ∧ a + k ≤ t + 48)) (hi : i < k) :
    Outside (a + i) 1
      (rt ++ [(t - 320 - (K + 1312), t - 320 - 8), (t - 320 + 8, t - 320 + 120)] ++ [(zp, zp + 8 * zc)]) := by
  simp only [outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
  rcases Nat.eq_zero_or_pos zc with h0 | h0
  · subst h0; omega
  · have := hz h0; omega

/-- a byte of a live object (outside `ExpSpec`'s window) is outside segments A-C's frame -/
theorem out_live {t stk above a : Nat} {r : Nat × Nat} (hst : stk ≤ t) (hab : 48 ≤ above) (hstk : 328 ≤ stk)
    (h : Outside r.1 (r.2 - r.1) [(t - stk, t + above)]) (e1 : r.1 ≤ a) (e2 : a + 1 ≤ r.2) :
    Outside a 1 [(t - 328, t - 8), (t + 8, t + 48)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

/-- the bytes segment D writes and `(*Int).exp`'s whole frame -/
theorem out_post {rt : List (Nat × Nat)} {t stk above zA a : Nat} {ws : List (Nat × Nat)} (h4416 : 4416 ≤ stk)
    (ho : Outside a 1 (rt ++ [(t - stk, t - 8), (t + 8, t + above)] ++ (zA, zA + 32) :: ws)) :
    Outside a 1 [(zA, zA + 32)] ∧ Outside a 1 (rt ++ [(t - 4416, t - 328)]) ∧
      Outside a 1 (rt ++ [(t - stk, t - 8), (t + 8, t + above)] ++ ws) := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
  obtain ⟨⟨hR, hW1, hW2⟩, hZ, hws⟩ := ho
  exact ⟨hZ, ⟨hR, by omega⟩, ⟨hR, hW1, hW2⟩, hws⟩

/-- `z`'s header is kept up to `expNN`'s return -/
theorem AtN.hdr {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA : Nat}
    {V p l c b' : Nat} {L' : List (Nat × Nat)} {M : Memory}
    (hA : AtN R b B L stk above s zA V p l c b' L' M) (hzH : Held R L zA 32) (hzW : Outside zA 32 (win s stk above))
    (hzap : 0 < s.mem.readLE (zA + 24) 8 → Apart zA 32 (s.mem.readLE (zA + 8) 8) (8 * s.mem.readLE (zA + 24) 8))
    (a k : Nat) (h1 : zA ≤ a) (h2 : a + k ≤ zA + 32) : M.readLE a k = s.mem.readLE a k := by
  have hoA : Outside a k (ZArr s.mem zA) := by
    refine outside_arrW ?_
    intro hc
    have h3 := hzap hc
    revert h3 h1 h2
    generalize s.mem.readLE (zA + 8) 8 = q
    generalize s.mem.readLE (zA + 24) 8 = c
    intro h1 h2 h3
    unfold Apart at h3 ⊢; omega
  rcases hzH with hi | ho
  · exact hA.lf.readLE a k (hi.sub h1 h2) hoA
  · refine hA.mf.readLE a k ?_
    simp only [win, outside_cons, outside_nil, and_true] at hzW
    rw [outside_append, outside_append]
    refine ⟨⟨ho.of_sub h1 h2, ?_⟩, hoA⟩
    simp only [winA, outside_cons, outside_nil, and_true]; omega

end FvModexp.Arm64.IExp
