import FvModexp.Proofs.Arm64.Exp.ModInvJ2

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `JM` → `J2` (nat.go:1322-1325) (agent infra)

From `JM` (`+0x15c`): `zz := nat(nil).make(2·numWords)` (`2·numWords ≥ 4`: the `makeslice` path at `+0x1e0`, the small
lemma `zzalloc`), `z.setWord(k0)` (`k0 ≠ 0`, `cap z ≥ numWords + 1`: the store `z[0] = k0`, `setw`), `i = 2`, the jump
to the loop head `J2` with `j = 1` and `Z0 = natVal z (numWords + 1)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- stack-slot stores keep an owned array owned -/
theorem own_stk {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 : List (Nat × Nat)} {p c : Nat}
    (h : Own R kc L L1 s zp zc st xp xl M p c) (hF : MemFrame M M' (winA s (K kc) A)) :
    Own R kc L L1 s zp zc st xp xl M' p c := by
  obtain ⟨⟨-, ⟨-, hal, -, -⟩, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hstw, -, -⟩, -⟩ := hpre
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hal hstw
  have hr : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    hF.readLE _ _ (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
  have e0 : stW M' st = stW M st := by have := hr 0 (by omega); simpa using this
  exact own_mono h (LiveExt.refl _ _) (fun a k w => by rw [hF.accessible]) e0 (hr 8 (by omega)) (hr 16 (by omega))

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
theorem mkzz (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4608 ≤ kc)
    (kJ : J2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s) :
    JM impl R kc sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S zp' zc' L1 b1 hpre hn hpc hsp h28 h18 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hfw hrt hb hown hcap
  unfold Goal
  have hn2 := hpre.2.2.2.2.1
  have hsv := hpre.2.1
  have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hty : Outside wT 16 R.rt := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hx1 : natVal s.mem xp xl % 2 = 1 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hnw1 : 2 ≤ NW n := by simp only [NW]; omega
  have hnw2 : NW n ≤ 2 ^ 12 := by simp only [NW]; omega
  have hk0 : k0 s xp xl n < 2 ^ 64 := by
    unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
  have hk0p : 0 < k0 s xp xl n := by
    unfold k0; rw [show min 64 n = 64 by omega]; exact newton64_pos _ hx1
  have hok : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * NW n, 2 * NW n + 4] :=
    hsv.1 _ _ _ (by omega)
  have hmc : makeCost (2 * NW n) = allocCost (8 * (2 * NW n + 4)) := by
    unfold makeCost makeCap; rw [if_neg (show ¬ (2 * NW n = 1) by omega)]
  have hbl := blockSize_le_allocCost (8 * (2 * NW n + 4)) true
  have hbs : blockSize (8 * (2 * NW n + 4)) true ≤ b1 := by simp only [cost] at hcost; omega
  have hzc0 : 0 < zc' := by omega
  have hzlt := hown.1
  have hzp' := hown.2.1
  have hadd : BitVec.ofNat 64 (NW n) + BitVec.ofNat 64 (NW n) = BitVec.ofNat 64 (2 * NW n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [show (1797104 + 0x15c : Nat) = 1797452 from rfl] at hpc
  janus_run [hadd] until [1797584]
  sorry

end FvModexp.Arm64.ModInv
