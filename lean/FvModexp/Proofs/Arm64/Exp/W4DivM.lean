import FvModexp.Proofs.Arm64.Exp.W4DivK

/-!
# window-4 prologue (arm64): the remainder `RR = 2^(128 n) mod m` after the `RR` division (`rem_div`)

Pure lemma over `DvPost`: the remainder is the old `RR` buffer or a fresh object; either way it is apart from the frame,
the stack header, the stack's free part and `zz`; `zz` is unchanged; `1 ≤ len ≤ n`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem rem_div {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret b b' costD stkD qp rrp zzp zzc r rl rc : Nat}
    {r29 : BitVec 64} {M M' : Memory}
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [(rrp, 8 * (2 * n))] M)
    (hZ : ZZ R L g sp n mp xp yp ylen zp zc st l0 zzp zzc M) (hzzK : AW sp K zzp (8 * zzc)) (hKD : stkD ≤ K)
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (hzzr : Apart zzp (8 * zzc) rrp (8 * (2 * n))) (hzl : 2 * n + 1 ≤ zzc)
    (hzv : M.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n)) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv) (hmB : Mv < Exp.B ^ n)
    (hD : DvPost R b costD L L' b' g sp stkD st qp rrp n zzp (2 * n + 1) mp M M' r rl rc) :
    0 < rl ∧ rl ≤ n ∧ rc < 2 ^ 40 ∧ r < 2 ^ 64 ∧ M'.accessible r (8 * rl) false = true ∧ r + 8 * rl ≤ 2 ^ 48 ∧
    (InRanges r (8 * rl) L' ∨ Outside r (8 * rl) R.rt) ∧ Apart r (8 * rl) (sp - 4288) (4288 + 1040) ∧
    Apart r (8 * rl) st 24 ∧ Apart r (8 * rl) (stFree M' st).1 (stFree M' st).2 ∧ Apart zzp (8 * zzc) r (8 * rl) ∧
    M'.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n) ∧ M'.readLE r (8 * rl) = 2 ^ (128 * n) % Mv := by
  obtain ⟨-, hce, hK, -, hn, -, -, -, -, hmO, hmV, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hsth, -, hsok, -, hl0, hcap, -, -, huw, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨⟨hzb1, hzb2, hzb3, hzb4, hzH, hzb6, hzb7⟩, -, -, -, -, -, hzS, hzU, -⟩ := hZ
  obtain ⟨⟨hv, hN, hlc, hc40, hlive, hor⟩, -, -, -, ⟨hsok', hlen', hst'⟩, hfr, hF, hL, -⟩ := hD
  have hrt : Outside (sp - K) (K + 1040) R.rt := hce.2.2.2.2.2.2.2.1
  -- zz is unchanged
  have hlc0 := hsok.2.2.2.2.2.1
  have hzz' : M'.readLE zzp (8 * (2 * n + 1)) = M.readLE zzp (8 * (2 * n + 1)) := by
    have hF' : MemFrame M M' (R.rt ++ [(sp - stkD, sp - 8), (sp + 8, sp + 112)] ++
        ([(qp, qp + 8 * (2 * n)), (rrp, rrp + 8 * (2 * n))] ++ stkWs M st)) := by
      simpa only [List.append_assoc] using hF
    simp only [AW, Apart, stUp] at hzzK hzzr hzS hzU huw
    refine FvModexp.Expmc.held_readLE (hzH.imp (fun h => h.sub (by omega) (by omega))
      (fun h => h.of_sub (by omega) (by omega))) hF' hL ?_ ?_
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  have hval : M'.readLE r (8 * rl) = 2 ^ (128 * n) % Mv := by
    have := hv; simp only [natVal] at this; rw [this, hzv, hmV]
  have hV := rr_pos (n := n) hMo hM1
  have hrl0 : 0 < rl := by
    rcases Nat.eq_zero_or_pos rl with h | h
    · rw [h, Nat.mul_zero, Memory.readLE_zero] at hval; omega
    · exact h
  have hBn : Exp.B ^ n = 2 ^ (64 * n) := by rw [Exp.B_eq, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, ← Nat.pow_mul]
  have hrln : rl ≤ n := norm_len_le hN (by rw [hval, ← hBn]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hmB)
  obtain ⟨r8, rH, racc, r48⟩ := hlive (by omega)
  have hlen0 : 0 < stLen M st := by omega
  have hrsub : InRanges r (8 * rl) L' ∨ Outside r (8 * rl) R.rt :=
    rH.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  refine ⟨hrl0, hrln, hc40, by omega, M'.accessible_sub racc (Or.inl rfl) (by omega) (by omega), by omega, hrsub,
    ?_, ?_, ?_, ?_, by rw [hzz', hzv], hval⟩
  all_goals by_cases hold : r = rrp ∧ rc = 2 * n
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hold)
    | (have hfresh : 8 * rc ≥ 0 ∧ InRanges r (8 * rc) R.rt ∧ ApartAll r (8 * rc) L := by
          rcases hor with h | ⟨-, hin, hap⟩
          · exact absurd h hold
          · exact ⟨Nat.zero_le _, hin, hap⟩
       obtain ⟨-, hin, hap⟩ := hfresh)
  · simp only [AW, Apart] at hrW ⊢; omega
  · have := out_inR hrt hin; unfold Apart; omega
  · unfold Apart at hrS ⊢; omega
  · have := apart_held' hin hap hsth; unfold Apart at this ⊢; omega
  · -- the old RR buffer and the free part
    have hlc' := hsok'.2.2.2.2.2.1
    rcases hst' with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [stFree, stLen, stCap, stW] at hlen' e1 e2 hrB hlc' ⊢; unfold Apart at hrB ⊢; omega
    · obtain ⟨-, rH0, -, -⟩ := hrL (by omega)
      have := apart_held' hin hap rH0
      simp only [stFree, stLen, stCap, stW] at hlen' this hlc' ⊢; unfold Apart at this ⊢; omega
  · have hc' : 0 < stCap M' st := by
      have := hsok'.2.2.2.2.2.1; simp only [stLen, stCap] at hlen' this hlen0 ⊢; omega
    have := hfr hold (by omega) hc'
    have hlc' := hsok'.2.2.2.2.2.1
    simp only [stFree, stLen, stCap, stW] at this hlc' ⊢; unfold Apart at this ⊢; omega
  · unfold Apart at hzzr ⊢; omega
  · have := apart_held' hin hap hzH; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the frame slots above div's spill area survive the division -/
theorem slot_div {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret b b' costD stkD qp rrp zzp zzl r rl rc : Nat}
    {r29 : BitVec 64} {M M' : Memory}
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [(rrp, 8 * (2 * n))] M)
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (hrW : AW sp K rrp (8 * (2 * n)))
    (hD : DvPost R b costD L L' b' g sp stkD st qp rrp n zzp zzl mp M M' r rl rc)
    (j : Nat) (hj1 : 112 ≤ j) (hj2 : j + 8 ≤ 1040) : M'.readLE (sp + j) 8 = M.readLE (sp + j) 8 := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, -, -, -, huw, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, hF, -, -⟩ := hD
  have hrt : Outside (sp - K) (K + 1040) R.rt := hce.2.2.2.2.2.2.2.1
  have hlc := hsok.2.2.2.2.2.1
  refine hF.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [AW, Apart, stUp] at hrW huw
    simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [AW, Apart, stUp] at hstw huw
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega

end FvModexp.Arm64.W4Pro
