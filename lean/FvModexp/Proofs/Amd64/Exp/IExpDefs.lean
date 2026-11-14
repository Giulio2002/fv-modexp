import FvModexp.Proofs.Amd64.Exp.NNilD
import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Common.ByteFrame

/-!
# `(*Int).exp` (amd64; agent expmc s76, twin of the arm64 IExpDefs): the facts at `nat.expNN`'s return (`AtN`) and byte-level frame arithmetic (pure)

* `AtN`: the facts at `expNN`'s return (memory `M`): the result `(p, l, c)` (`p` the register value, i.e. below
  `2^64`; an empty result's pointer is irrelevant) holds `V = x^y mod m`, normalised, cap
  `< 2^40`, live in `L'`, the old array of `z` or a fresh one; `M` differs from the entry memory only in `R.rt`, the
  window and `z`'s old array (frames at byte granularity: a nil `z` has an empty, arbitrarily placed array).
* `atN_of`: `AtN` from `ExpSpec`'s precondition, the frame of segments A-C and `ExpN.PostNil`.
* `post_of`: `AtN` and segment D's continuation facts (`runD`'s `KF`) give `IntPost` and the result's cap bound.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IExp

open FvModexp.Amd64.RunIface (IntOK IntPre IntPost IntV arrW)

/-- `RunIface.arrW` behind an irreducible name: elaborating a statement whose `Outside`/frame list contains the
`if` of `arrW` may evaluate its condition `0 < m.readLE (z + 24) 8` by `whnf` (a byte-by-byte unfolding of `readLE`;
measured: a one-line term proof took 24 s). `zarr_eq` converts. -/
@[irreducible] def ZArr (m : Janus.Arm64.Memory) (zA : Nat) : List (Nat × Nat) := arrW m zA

theorem zarr_eq (m : Janus.Arm64.Memory) (zA : Nat) : ZArr m zA = arrW m zA := by unfold ZArr; rfl

/-- the facts at `expNN`'s return (memory `M`; result `(p, l, c)` holding `V`, live set `L'`, budget `b'`) -/
structure AtN (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (stk above : Nat) (s : State) (zA V p l c b' : Nat)
    (L' : List (Nat × Nat)) (M : Janus.Arm64.Memory) : Prop where
  val : natVal M p l = V
  norm : NatNorm M p l
  lc : l ≤ c
  c40 : c < 2 ^ 40
  p64 : p < 2 ^ 64
  ext : LiveExt R L L'
  bud : b - B ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  live : NatLive M R L' p c
  orf : c = 0 ∨ (p = s.mem.readLE (zA + 8) 8 ∧ c = s.mem.readLE (zA + 24) 8) ∨
    (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s stk above ++ ZArr s.mem zA)
  lf : LiveFrame s.mem M L (ZArr s.mem zA)

/-- an operand's value survives a frame that misses its array -/
theorem natVal_eq0 {m M : Janus.Arm64.Memory} {p l c lo hi : Nat} (hlc : l ≤ c)
    (hout : 0 < c → Outside p (8 * c) [(lo, hi)]) (hF : MemFrame m M [(lo, hi)]) : natVal M p l = natVal m p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; rfl
  · have := hout (by omega)
    exact hF.readLE _ _ (this.of_sub (Nat.le_refl _) (by omega))

/-- a byte outside `z`'s old array as a written range is outside the range `(p, p + 8 c)` of its header fields -/
theorem out_arrW {m : Janus.Arm64.Memory} {zA a : Nat} (h : Outside a 1 (ZArr m zA)) :
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
theorem outside_arrW {m : Janus.Arm64.Memory} {zA a k : Nat}
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

/-- `z`'s header is kept up to `expNN`'s return -/
theorem AtN.hdr {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA : Nat}
    {V p l c b' : Nat} {L' : List (Nat × Nat)} {M : Janus.Arm64.Memory}
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
    rw [outside_append, outside_append]
    exact ⟨⟨ho.of_sub h1 h2, hzW.of_sub h1 h2⟩, hoA⟩

end FvModexp.Amd64.IExp
