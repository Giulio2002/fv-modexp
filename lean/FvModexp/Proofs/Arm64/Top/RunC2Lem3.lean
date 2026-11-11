import FvModexp.Proofs.Arm64.Top.RunC2Lem2

/-!
# `Run` (arm64): compute part — frames, slots, budget and value from `C2` to `V` (pure lemmas)

After `z.Mod(z, y)` / `z.exp(z, y, m, false)` (frame: `R.rt`, the callee window at `SP - 624`, the header of `z` and its
old array) and `z.Bytes()` (frame: `R.rt`, the callee window), the facts `RelV` needs, stated over memories so that the
segment proofs only instantiate them (no `omega` in the large post-run contexts).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

open RunIface

/-- The two calls keep everything outside `R.rt` and `Run`'s window `W` (`z`'s header lies in `Run`'s frame, its old
array is a runtime object). -/
theorem frame_TV {R : RtInv} {M M1 M2 : Memory} {sc t : State} {sp W stkM aboveM z : Nat}
    (hW : 624 + stkM ≤ W) (hab : aboveM ≤ 160) (hspW : W ≤ sp)
    (hsc : sc.sp.toNat = sp - 624) (ht : t.sp.toNat = sp - 624) (hz1 : sp - W ≤ z) (hz2 : z + 32 ≤ sp + 40)
    (harr : 0 < M.readLE (z + 24) 8 → InRanges (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) R.rt)
    (h1 : MemFrame M M1 (R.rt ++ winA sc stkM aboveM ++ (z, z + 32) :: arrW M z))
    (h2 : MemFrame M1 M2 (R.rt ++ winA t stkM aboveM)) :
    MemFrame M M2 (R.rt ++ [(sp - W, sp + 40)]) :=
  h1.trans h2 fun a n h => by
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h
    obtain ⟨hr, hw⟩ := h
    refine ⟨out_post hr (by unfold Apart; omega) (by unfold Apart; omega) fun hc => ?_, ?_⟩
    · have := InRanges.apart (harr hc) hr; unfold Apart at this ⊢; omega
    · simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hr, by omega, by omega⟩

/-- A slot of `Run`'s frame that neither callee writes: outside `R.rt`, in the caller part `[SP - 8, SP + 8)` of the
callee window or above it, apart from `z`'s header. -/
theorem slot_TV {R : RtInv} {M M1 M2 : Memory} {sc t : State} {stkM aboveM z a n q : Nat}
    (ht : t.sp = sc.sp) (hq : sc.sp.toNat = q) (hr : Outside a n R.rt)
    (hw : (q - 8 ≤ a ∧ a + n ≤ q + 8 ∧ 8 ≤ q) ∨ q + aboveM ≤ a)
    (hz : a + n ≤ z ∨ z + 32 ≤ a)
    (harr : 0 < M.readLE (z + 24) 8 → InRanges (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) R.rt)
    (h1 : MemFrame M M1 (R.rt ++ winA sc stkM aboveM ++ (z, z + 32) :: arrW M z))
    (h2 : MemFrame M1 M2 (R.rt ++ winA t stkM aboveM)) :
    M2.readLE a n = M.readLE a n := by
  have hwA : Outside a n (winA sc stkM aboveM) := by
    simp only [winA, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hwA' : Outside a n (winA t stkM aboveM) := by
    simp only [winA, ht] at hwA ⊢; exact hwA
  rw [h2.readLE a n (by rw [Janus.outside_append]; exact ⟨hr, hwA'⟩), h1.readLE a n ?o1]
  case o1 =>
    rw [Janus.outside_append, Janus.outside_append]
    refine ⟨⟨hr, hwA⟩, ?_⟩
    simp only [Janus.outside_cons]
    refine ⟨hz, ?_⟩
    simp only [arrW]
    generalize M.readLE (z + 24) 8 = cap at harr ⊢
    generalize M.readLE (z + 8) 8 = ptr at harr ⊢
    rcases Nat.eq_zero_or_pos cap with h0 | hc
    · subst h0; simp only [Nat.lt_irrefl, if_false, Janus.outside_nil]
    · have := InRanges.apart (harr hc) hr; unfold Apart at this
      simp only [hc, if_true, Janus.outside_cons, Janus.outside_nil, and_true]; omega

/-- The objects of the caller's live set `L` are unchanged by the two calls. -/
theorem liveFrame_TV {R : RtInv} {M M1 M2 : Memory} {L L1 L2 : List (Nat × Nat)} {sp W z : Nat}
    (hext1 : LiveExt R L L1) (hext2 : LiveExt R L1 L2) (hLs : LiveSep L [(sp - W, sp + 40)])
    (hz1 : sp - W ≤ z) (hz2 : z + 32 ≤ sp + 40)
    (harr : 0 < M.readLE (z + 24) 8 → ApartAll (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) L)
    (h1 : LiveFrame M M1 L1 ((z, z + 32) :: arrW M z)) (h2 : LiveFrame M1 M2 L2 []) :
    LiveFrame M M2 L [] :=
  ⟨fun a n hin _ => by
    rw [h2.readLE a n (hext2.inRanges_old (hext1.inRanges_old hin)) trivial]
    refine h1.readLE a n (hext1.inRanges_old hin) ?_
    obtain ⟨r, hr, i1, i2⟩ := hin
    have hw := hLs r hr
    simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hw
    simp only [arrW]
    generalize M.readLE (z + 24) 8 = cap at harr ⊢
    generalize M.readLE (z + 8) 8 = ptr at harr ⊢
    rcases Nat.eq_zero_or_pos cap with h0 | hc
    · subst h0; simp only [Nat.lt_irrefl, if_false, Janus.outside_cons, Janus.outside_nil, and_true]; omega
    · have := harr hc r hr; unfold Apart at this
      simp only [hc, if_true, Janus.outside_cons, Janus.outside_nil, and_true]; omega⟩

/-- The budget of `Mod` + `Bytes` fits the compute allowance `callB`. -/
theorem budget_c2m {b b1 b2 b3 X w lw0 lw2 lb E : Nat} (h0 : lw0 ≤ w) (h2 : lw2 ≤ w) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hb2 : b1 - ModBudget (max lw0 lw2) ≤ b2) (hb3 : b2 - BytesBudget lb ≤ b3) :
    b - (X + (ModBudget w + E + BytesBudget maxW)) ≤ b3 := by
  have e1 : ModBudget (max lw0 lw2) ≤ ModBudget w := by
    unfold ModBudget opCost allocCost; omega
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

/-- The budget of `exp` + `Bytes` fits the compute allowance `callB`. -/
theorem budget_c2e {b b1 b2 b3 X w yW lw0 lw1 lw2 lb M : Nat} (h0 : lw0 ≤ w) (h1 : lw1 ≤ w) (h2 : lw2 ≤ w)
    (hy : lw1 ≤ yW) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hb2 : b1 - ExpBudget (max (max lw0 lw1) lw2) lw1 ≤ b2) (hb3 : b2 - BytesBudget lb ≤ b3) :
    b - (X + (M + ExpBudget w yW + BytesBudget maxW)) ≤ b3 := by
  have e1 : ExpBudget (max (max lw0 lw1) lw2) lw1 ≤ ExpBudget w yW := by
    unfold ExpBudget opCost allocCost
    have : max (max lw0 lw1) lw2 ≤ w := by omega
    exact Nat.mul_le_mul (by omega) (by omega)
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

/-- The `Mod`/`exp` budget fits what `Run` has left after the operands (the `Bytes` allowance kept apart). -/
theorem budget_c2e0 {b b1 X w yW lw0 lw1 lw2 lb M A : Nat} (h0 : lw0 ≤ w) (h1 : lw1 ≤ w) (h2 : lw2 ≤ w)
    (hy : lw1 ≤ yW) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hB : X + (M + ExpBudget w yW + BytesBudget maxW) + A ≤ b) :
    ExpBudget (max (max lw0 lw1) lw2) lw1 + BytesBudget lb ≤ b1 := by
  have e1 : ExpBudget (max (max lw0 lw1) lw2) lw1 ≤ ExpBudget w yW := by
    unfold ExpBudget opCost allocCost
    have : max (max lw0 lw1) lw2 ≤ w := by omega
    exact Nat.mul_le_mul (by omega) (by omega)
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

/-- The value `Run` computes, as `resV`. -/
theorem resV_eq (s : State) (p len : BitVec 64) (h2 : 0 < opV s p len 2) :
    resV s p len = opV s p len 0 ^ opV s p len 1 % opV s p len 2 := by
  unfold resV; rw [if_neg (by omega)]

/-- A value below the modulus fits `modLen` bytes. -/
theorem lt_modLen (s : State) (p len : BitVec 64) {v : Nat} (h : v < opV s p len 2) : v < 256 ^ hdrV s p len 2 := by
  have := padBE_lt s.mem p.toNat len.toNat (96 + opStart s p len 2) (opLen s p len 2)
  simp only [opV, opLen, show (2 : Nat) = 0 ↔ False by decide, show (2 : Nat) = 1 ↔ False by decide,
    if_false] at h this
  omega

end FvModexp.Arm64.Run
