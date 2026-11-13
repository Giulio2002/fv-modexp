import FvModexp.Proofs.Amd64.Exp.W4FunA
import FvModexp.Proofs.Amd64.Exp.W4XnS

set_option autoImplicit false

/-!
# window-4 (amd64): the per-layer `AncI` bridge of the prologue chain posts (agent expmc s58)

The prologue posts (`XnQ` → `XnJQ`/`XnAQ` → … → `DivQ`) record each step as a `Keeps`/`KeepsX` relation at the
level `l0` of the step. Each lemma here consumes one layer: it moves the anchored invariant `AncI` (anchor `M0`,
`L0`) through the layer's steps (`AncI.keep`/`AncI.keepX`; the scratch ranges are stack nats above the anchor's
length, `AncI.aloc`) and turns the budget relation into a lower bound `bA`. The result is `LshR`: `AncI` at the
division's return memory, the fresh `zz` buffer (in `R.rt`, apart from `L0`), and the tail of `DivQ` (`RRPost`,
`OneChain`, `RetQ`) unchanged.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- the window-4 post from the division's return on, anchored at `M0` (stack level `lenM` at the division) -/
@[reducible] def DivR (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t zzp zzc lenM Xv : Nat) (s' : State) : Prop :=
  ∃ (M' : Memory) (L' : List (Nat × Nat)) (b' rp rl rc : Nat) (M1 : Memory) (rrq rrc onep : Nat) (M2 : Memory)
    (L2 : List (Nat × Nat)) (b2 : Nat),
    AncI R L0 sp K st M0 L' M' ∧ bA ≤ b' ∧ stLen M' st = lenM ∧ M'.readLE rp (8 * rl) = 2 ^ (128 * n) % Mv ∧
    RRPost R b' L' g sp n rp rl rc zzp zzc M' M1 rrq rrc ∧ OneChain R b' L' L2 b2 sp n st M1 M2 ∧
    RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * lenM) (17 * n) st n0 onep fbp
      Mv Xv (2 ^ (128 * n) % Mv) M2 s'

/-- `DivR` with the `zz` buffer allocated by the `lsh` layer -/
@[reducible] def LshR (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t lenM Xv : Nat) (s' : State) : Prop :=
  ∃ zzp zzc : Nat, 2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L0 ∧
    DivR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t zzp zzc lenM Xv s'

/-- the budget of the `xj` layer at level `l` up to the division (`xjBud` = this + the post-division costs) -/
@[reducible] def xjPre (n costD l : Nat) : Nat :=
  stackNatCost l (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l + StackNat.rnd (2 * n)) (2 * n) + costD))

theorem xjPre_le (n costD l : Nat) : xjPre n costD l ≤ xjBud n costD l := by
  simp only [xjPre, xjBud]; omega

theorem ex_nil {R : RtInv} {L0 : List (Nat × Nat)} {st : Nat} {M0 : Memory} :
    ∀ e ∈ ([] : List (Nat × Nat)), ALoc R L0 st M0 e := fun _ he => by cases he

theorem ex_one {R : RtInv} {L0 : List (Nat × Nat)} {st : Nat} {M0 : Memory} {e0 : Nat × Nat}
    (h : ALoc R L0 st M0 e0) : ∀ e ∈ [e0], ALoc R L0 st M0 e := fun e he => by
  rw [List.mem_singleton] at he; subst he; exact h

theorem apartAll_old {R : RtInv} {L0 L : List (Nat × Nat)} {p k : Nat} (hx : LiveExt R L0 L) (h : ApartAll p k L) :
    ApartAll p k L0 := fun r hr => h r (hx.mem_old hr)

/-! small arithmetic (never `omega` in the contexts holding the posts: it times out unfolding them) -/
theorem fbud1 {bA c b b' : Nat} (h1 : bA + c ≤ b) (h2 : b - c ≤ b') : bA ≤ b' := by omega
theorem fbud2 {bA c d b b' : Nat} (h1 : bA + (c + d) ≤ b) (h2 : b - c ≤ b') : bA + d ≤ b' := by omega
theorem flvB (l a c : Nat) : l + a + a ≤ l + c + a + a := by omega
theorem flvC {x l a c d e : Nat} (h : x ≤ l + d + a + a) : x ≤ l + c + d + e + a + a := by omega
theorem flvL {l a x m : Nat} (h0 : m ≤ l) (h : l + a + a ≤ x) : m ≤ x := by omega
theorem fle_add {a b c : Nat} (h : a ≤ b) : a ≤ b + c := Nat.le_trans h (Nat.le_add_right _ _)

/-- a stack nat `[l, l + k)` just pushed (`stLen M = l + rnd k`) is `ALoc` -/
theorem aloc_push {R : RtInv} {L0 L : List (Nat × Nat)} {sp K st l k : Nat} {M0 M : Memory}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l) (he : stLen M st = l + StackNat.rnd k) :
    ALoc R L0 st M0 (stW M st + 8 * l, 8 * k) :=
  AncI.aloc hA hl (by have := hA.2.2.1; have := rnd_ge k; omega)

/-- the division layer -/
theorem divQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st)
    (hrr : ALoc R L0 st M0 (rrp, 8 * (2 * n))) (hK : K + 8 ≤ sp) (hb : bA + costD ≤ b)
    (h : DivQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv M s') :
    DivR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t zzp zzc (stLen M st) Xv s' := by
  obtain ⟨Mw, M', L', b', rp, rl, rc, M1, rrq, rrc, onep, M2, L2, b2, k1, k2, hb', hlen, hv, hRR, hOC, hRet⟩ := h
  have hA1 := AncI.keep hA k1 hl hl' (ex_one hrr) hK
  have hlw : stLen M st ≤ stLen Mw st := k1.2.2.2.2.2.2.2.2.1
  have hA2 := AncI.keep hA1 k2 hl (Nat.le_trans hl' hlw) (ex_one hrr) hK
  exact ⟨M', L', b', rp, rl, rc, M1, rrq, rrc, onep, M2, L2, b2, hA2, fbud1 hb hb', hlen, hv, hRR, hOC, hRet⟩

/-- the `stk.nat(2n)` layer before the division -/
theorem sn2Q_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st)
    (hrr : ALoc R L0 st M0 (rrp, 8 * (2 * n))) (hK : K + 8 ≤ sp)
    (hb : bA + (stackNatCost (stLen M st) (2 * n) + costD) ≤ b)
    (h : Sn2Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv M s') :
    DivR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t zzp zzc
      (stLen M st + StackNat.rnd (2 * n)) Xv s' := by
  obtain ⟨M1, M2, L2, b2, k1, k2, hb2, hlen, hD⟩ := h
  have hA1 := AncI.keep hA k1 hl hl' (ex_one hrr) hK
  have hl1 : stLen M st ≤ stLen M1 st := k1.2.2.2.2.2.2.2.2.1
  have hA2 := AncI.keep hA1 k2 hl (Nat.le_trans hl' hl1) (ex_one hrr) hK
  rw [← hlen]
  exact divQ_anc hA2 hl (by rw [hlen]; exact fle_add hl') hrr hK (fbud2 hb hb2) hD

/-- the `lsh` layer (allocates `zz`) -/
theorem lshQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t rrp Xv : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st)
    (hrr : ALoc R L0 st M0 (rrp, 8 * (2 * n))) (hK : K + 8 ≤ sp)
    (hb : bA + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (stLen M st) (2 * n) + costD)) ≤ b)
    (h : LshQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t rrp Xv M s') :
    LshR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t (stLen M st + StackNat.rnd (2 * n)) Xv s' := by
  obtain ⟨M1, M2, L2, b2, zzp, zzc, k1, k2, hb2, hlen, hzc, hzin, hzap, hS⟩ := h
  have hA1 := AncI.keep hA k1 hl hl' (ex_one hrr) hK
  have hl1 : stLen M st ≤ stLen M1 st := k1.2.2.2.2.2.2.2.2.1
  have hA2 := AncI.keep hA1 k2 hl (Nat.le_trans hl' hl1) (ex_one hrr) hK
  have hS' := sn2Q_anc (bA := bA) hA2 hl (by rw [hlen]; exact hl') hrr hK (by rw [hlen]; exact fbud2 hb hb2) hS
  rw [hlen] at hS'
  exact ⟨zzp, zzc, hzc, hzin, apartAll_old hA.1.1 hzap, hS'⟩

/-- the `stk.nat(2n)` layer of `rr` -/
theorem sn1Q_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t Xv : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hb : bA + xjPre n costD l0 ≤ b)
    (h : Sn1Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t Xv M s') :
    LshR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp t
      (l0 + StackNat.rnd (2 * n) + StackNat.rnd (2 * n)) Xv s' := by
  obtain ⟨M2, L2, b2, k1, hb2, hlen, hL⟩ := h
  have hA2 := AncI.keep hA k1 hl hl' ex_nil hK
  have hL' := lshQ_anc (bA := bA) hA2 hl (by rw [hlen]; exact Nat.le_add_right _ _) (aloc_push hA2 hl hlen) hK
    (by rw [hlen]; exact fbud2 hb hb2) hL
  rwa [hlen] at hL'

/-- the `newton` layer (`k0`) -/
theorem xjQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp Xv : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hb : bA + xjPre n costD l0 ≤ b)
    (h : XjQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp Xv M s') :
    LshR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp (Exp.newton 64 (Mv % Exp.B))
      (l0 + StackNat.rnd (2 * n) + StackNat.rnd (2 * n)) Xv s' := by
  obtain ⟨M1, k1, hlen, hS⟩ := h
  have hA1 := AncI.keepX hA k1 hl hl' ex_nil hK
  exact sn1Q_anc hA1 hl (by rw [hlen]; exact hl') hK hb hS

/-- the result of the join layers: some level between the two paths' -/
@[reducible] def JR (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp l0 Xv : Nat) (s' : State) : Prop :=
  ∃ lenM : Nat, l0 + StackNat.rnd (2 * n) + StackNat.rnd (2 * n) ≤ lenM ∧
    lenM ≤ l0 + StackNat.rnd n + StackNat.rnd (2 * n) + StackNat.rnd (2 * n) ∧
    LshR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp (Exp.newton 64 (Mv % Exp.B)) lenM Xv s'

/-- path B's `stk.nat(n)` layer (`x` extended to `n` words) -/
theorem xnBQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hb : bA + (stackNatCost l0 n + xjPre n costD (l0 + StackNat.rnd n)) ≤ b)
    (h : XnBQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X M s') :
    JR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp l0 X s' := by
  obtain ⟨M3, L2, b2, k1, hb2, hlen, hX⟩ := h
  have hA3 := AncI.keepX hA k1 hl hl' ex_nil hK
  exact ⟨_, flvB _ _ _, Nat.le_refl _,
    xjQ_anc hA3 (fle_add hl) (Nat.le_of_eq hlen.symm) hK (fbud2 hb hb2) hX⟩

/-- the join (`x` as given, or extended by path B) -/
theorem xnJQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hbC : bA + xjPre n costD l0 ≤ b) (hbB : bA + (stackNatCost l0 n + xjPre n costD (l0 + StackNat.rnd n)) ≤ b)
    (h : XnJQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X M s') :
    JR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp l0 X s' := by
  rcases h with h | h
  · exact ⟨_, Nat.le_refl _, flvB _ _ _, xjQ_anc hA hl hl' hK hbC h⟩
  · exact xnBQ_anc hA hl hl' hK hbB h

/-- path A's division layer (`x := x mod m`, then the join at the current level) -/
theorem xnA2Q_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp qp k X : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hq : ALoc R L0 st M0 (qp, 8 * k))
    (hbC : bA + (costD + xjPre n costD (stLen M st)) ≤ b)
    (hbB : bA + (costD + (stackNatCost (stLen M st) n + xjPre n costD (stLen M st + StackNat.rnd n))) ≤ b)
    (h : XnA2Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp qp k X M s') :
    JR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp (stLen M st) (X % Mv) s' := by
  obtain ⟨M5, L5, b5, k1, hb5, hlen, hJ⟩ := h
  have hA5 := AncI.keepX hA k1 hl hl' (ex_one hq) hK
  exact xnJQ_anc hA5 hA.2.1 (Nat.le_of_eq hlen.symm) hK (fbud2 hbC hb5) (fbud2 hbB hb5) hJ

/-- path A (`len x > n`): `q := stk.nat(k)`, `z2 := stk.nat(n)`, then the division layer -/
theorem xnAQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp k X : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hbC : bA + (stackNatCost l0 k + (stackNatCost (l0 + StackNat.rnd k) n +
      (costD + xjPre n costD (l0 + StackNat.rnd k + StackNat.rnd n)))) ≤ b)
    (hbB : bA + (stackNatCost l0 k + (stackNatCost (l0 + StackNat.rnd k) n +
      (costD + (stackNatCost (l0 + StackNat.rnd k + StackNat.rnd n) n +
        xjPre n costD (l0 + StackNat.rnd k + StackNat.rnd n + StackNat.rnd n))))) ≤ b)
    (h : XnAQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp k X M s') :
    JR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp (l0 + StackNat.rnd k + StackNat.rnd n)
      (X % Mv) s' := by
  obtain ⟨M2, L2, b2, M4, L4, b4, k1, hlen2, hb2, k2, hb4, hlen4, hA2Q⟩ := h
  have hA2 := AncI.keepX hA k1 hl hl' ex_nil hK
  have hq := aloc_push hA2 hl hlen2
  have hA4 := AncI.keepX hA2 k2 hl (by rw [hlen2]; exact Nat.le_add_right _ _) (ex_one hq) hK
  have hJ := xnA2Q_anc (bA := bA) hA4 hl (by rw [hlen4]; exact fle_add (Nat.le_add_right _ _)) hK hq
    (by rw [hlen4]; exact fbud2 (fbud2 hbC hb2) hb4) (by rw [hlen4]; exact fbud2 (fbud2 hbB hb2) hb4) hA2Q
  rwa [hlen4] at hJ

/-- the upper bound of the division level over both paths -/
@[reducible] def lvU (n xl l0 : Nat) : Nat :=
  l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n + StackNat.rnd (2 * n) + StackNat.rnd (2 * n)

/-- the budget conditions of `xnQ_anc` -/
@[reducible] def XnBudA (n costD l0 xl bA b : Nat) : Prop :=
  bA + xjPre n costD l0 ≤ b ∧ bA + (stackNatCost l0 n + xjPre n costD (l0 + StackNat.rnd n)) ≤ b ∧
  bA + (stackNatCost l0 (xl - n + 1) + (stackNatCost (l0 + StackNat.rnd (xl - n + 1)) n +
      (costD + xjPre n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n)))) ≤ b ∧
  bA + (stackNatCost l0 (xl - n + 1) + (stackNatCost (l0 + StackNat.rnd (xl - n + 1)) n +
      (costD + (stackNatCost (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
        xjPre n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n))))) ≤ b

/-- **the whole `x` normalisation post, anchored**: some level `lenM` of the division (between the anchor and
`lvU`), the normalised `x` value (`X` itself when `len x ≤ n`, else `X mod m`), and `LshR` -/
theorem xnQ_anc {R : RtInv} {L0 L : List (Nat × Nat)} {K bA b costD : Nat} {M0 M : Memory}
    {g fs sp n mp Mv yp ylen Y yi zp zc st n0 l0 fbp xl X : Nat} {s' : State}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stLen M st) (hK : K + 8 ≤ sp)
    (hb : XnBudA n costD l0 xl bA b)
    (h : XnQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp xl X M s') :
    ∃ lenM Xv : Nat, stLen M0 st ≤ lenM ∧ lenM ≤ lvU n xl l0 ∧ ((xl ≤ n ∧ Xv = X) ∨ Xv = X % Mv) ∧
      LshR R L0 K bA M0 g fs sp n mp Mv yp ylen Y yi zp zc st n0 fbp (Exp.newton 64 (Mv % Exp.B)) lenM Xv s' := by
  obtain ⟨hbC, hbB, hbAC, hbAB⟩ := hb
  rcases h with ⟨hc, h⟩ | ⟨-, h⟩
  · obtain ⟨lenM, h1, h2, hR⟩ := xnJQ_anc hA hl hl' hK hbC hbB h
    exact ⟨lenM, X, flvL hl h1, flvC h2, Or.inl ⟨hc, rfl⟩, hR⟩
  · obtain ⟨lenM, h1, h2, hR⟩ := xnAQ_anc hA hl hl' hK hbAC hbAB h
    exact ⟨lenM, X % Mv, flvL (fle_add (fle_add hl)) h1, h2, Or.inr rfl, hR⟩

end FvModexp.Amd64.W4Pro
