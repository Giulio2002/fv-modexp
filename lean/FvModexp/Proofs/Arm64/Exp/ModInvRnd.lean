import FvModexp.Proofs.Arm64.Exp.ModInvCall

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the facts inside a Hensel round, and how a callee keeps them (agent infra)

`Mid … M L1 b1 p l c q ql qc`: at memory `M` (live set `L1`, invariant at budget `b1`) the spills `Fw2`, the runtime
facts `RtM`, both arrays `z = (p, l, c)` and `zz = (q, ql, qc)` owned and apart, `cap z ≥ numWords + 1`, `cap zz > 0`.
Pure lemmas (address-independent; used by every call site of the loop and the final round): the operand facts a callee
precondition needs at the callee state (`SP' = SP - 240`), and the facts after a callee that writes one owned array
(`call_keep`: the other one, `x`, the spills and the runtime facts survive; `own_new`: the result is owned).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

/-- the facts at memory `M` inside a round (see the module doc) -/
@[reducible] def Mid (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (s : State) (zp zc st xp xl xc n : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 p l c q ql qc : Nat) : Prop :=
  Fw2 s M st xp xl xc n ∧ RtM R kc L s zp zc st M L1 b1 ∧
    Own R kc L L1 s zp zc st xp xl M p c ∧ Own R kc L L1 s zp zc st xp xl M q qc ∧
    Apart p (8 * c) q (8 * qc) ∧ l ≤ c ∧ ql ≤ qc ∧ NW n + 1 ≤ c ∧ 0 < qc

/-- a held range keeps its bytes through a frame, checked byte by byte (an empty range in the frame never matters) -/
theorem held_bytes {rt L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (hh : InRanges a n L ∨ Outside a n rt) (hf : MemFrame m m' (rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (h : ∀ i, i < n → Outside (a + i) 1 ws1 ∧ Outside (a + i) 1 ws2) : m'.readLE a n = m.readLE a n := by
  apply Memory.readLE_congr
  intro i hi
  have hh1 : InRanges (a + i) 1 L ∨ Outside (a + i) 1 rt :=
    hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have := Expmc.held_readLE hh1 hf hl (h i hi).1 (h i hi).2
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

set_option maxRecDepth 20000 in
/-- `x`'s words are unchanged at every memory the runtime facts describe -/
theorem x_val {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) {k : Nat} (hk : k ≤ xl) :
    M.readLE xp (8 * k) = s.mem.readLE xp (8 * k) := by
  obtain ⟨-, -, -, -, -, -, -, hzc0, -, -, hxc, -, -, ⟨-, -, -, hxh, hxw⟩, -, -, hzx, -, -, -, hsx, -⟩ := hpre
  obtain ⟨-, hF, hLF, -⟩ := hrt
  rw [List.append_assoc] at hF
  have hzx' := hzx hzc0
  unfold Apart at hzx'
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  refine held_bytes ((hxh.sub (Nat.le_refl _) (by omega))) hF hLF fun i hi => ⟨?_, ?_⟩
  · simp only [winA, outside_cons, outside_nil, and_true]; omega
  · simp only [stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨by omega, ?_, ?_⟩
    · have := (hsx (by omega)).1; unfold Apart at this; omega
    · rcases Nat.lt_or_ge (stLen s.mem st) (stCap s.mem st) with h | h
      · have := (hsx (by omega)).2 h; unfold Apart at this; omega
      · omega

/-- the stack's header and free part after a callee's `StackBack`, for a range the callee's live set holds -/
theorem stkApart_back {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {a k : Nat}
    (hb : StackBack R L1 L2 st M M') (h : StkApart M st a k) (hh : Held R L1 a k) : StkApart M' st a k := by
  intro hk
  obtain ⟨h1, h2⟩ := h hk
  obtain ⟨-, hlen, hor⟩ := hb
  refine ⟨h1, fun hlt => ?_⟩
  rcases hor with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
  · rw [e2, hlen] at hlt; rw [e0, e2, hlen]; exact h2 hlt
  · have := fresh_apart hIn hAp hh
    unfold Apart at this ⊢
    have : 8 * stLen M' st + 8 * (stCap M' st - stLen M' st) = 8 * stCap M' st := by omega
    omega

set_option maxRecDepth 20000 in
/-- a callee window at `SP' = SP - 240` (`stk ≤ kc`, `above ≤ 88`) misses the spill slots `[SP - 152, SP + 72)` and
the saved FP / LR `[SP - 248, SP - 232)` -/
theorem slot_out {s : State} {kc stk above a : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    (hsp : 240 + kc ≤ s.sp.toNat) {S' : State} (hS' : S'.sp.toNat = s.sp.toNat - 240)
    (ha : s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 152 ≤ a) :
    Outside a 8 (winA S' stk above) := by
  simp only [winA, hS', outside_cons, outside_nil, and_true]; omega

theorem out_sub {p n a k i j : Nat} {rs : List (Nat × Nat)} (hin : InRanges p n rs) (ho : Outside a k rs)
    (_hij : i ≤ j) (hj : j ≤ n) : Outside a k [(p + i, p + j)] := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem ho hr
  simp only [outside_cons, outside_nil, and_true]; omega

/-- an owned array stays owned after a callee: its array is live in the new live set, and the stack came back -/
theorem own_back {R : RtInv} {kc : Nat} {L L1 L2 : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat}
    {M M' : Memory} {o oc : Nat} (h : Own R kc L L1 s zp zc st xp xl M o oc) (hlive : NatLive M' R L2 o oc)
    (hsb : StackBack R L1 L2 st M M') : Own R kc L L2 s zp zc st xp xl M' o oc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨a1, a2, hlive, a4, a5, a6, a7, fun hc => ?_⟩
  have hc' : 0 < oc := by omega
  exact stkApart_back hsb a8 (a3 hc').2.1 hc

end FvModexp.Arm64.ModInv
