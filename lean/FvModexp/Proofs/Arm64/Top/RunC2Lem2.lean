import FvModexp.Proofs.Arm64.Top.RunCDefs

/-!
# `Run` (arm64): the compute calls — `IntPre` of `Bytes` on the result of `Mod`/`exp`, small facts
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- `RelD` reads only `SP`, `X28`, `X29`, `X18` and the memory of the state. -/
theorem RelD.congr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c p len cp : BitVec 64} {s : State} {ret k : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S T : State} (h : RelD R b L c p len cp s ret k Lk bk S)
    (hm : T.mem = S.mem) (hsp : T.sp = S.sp) (h28 : T.regs 28 = S.regs 28) (h29 : T.regs 29 = S.regs 29)
    (h18 : T.regs 18 = S.regs 18) : RelD R b L c p len cp s ret k Lk bk T := by
  unfold RelD at *
  rw [hm, hsp, h28, h29, h18]; exact h

/-- A normalised nat of value `1` is the one-limb `1`. -/
theorem natVal_eq_one {m : Memory} {p n : Nat} (hn : NatNorm m p n) (h : natVal m p n = 1) :
    n = 1 ∧ m.readLE p 8 = 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp at h
  · have := natVal_ge_norm m p n hn h0
    rw [h] at this
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge 1 n with h2 | h2
      · have : 2 ^ 64 ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · omega
    subst hn1
    refine ⟨rfl, ?_⟩
    have := natVal_succ m p 0
    simp only [natVal_zero, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add] at this
    omega

theorem intV_eq (m : Memory) (a : Nat) : RunIface.IntV m a = natAt m (a + 8) := by
  simp only [RunIface.IntV, natAt, show a + 8 + 8 = a + 16 by omega]

/-- A range apart from the runtime-owned ranges, the callee window, the header `z` and (if any) `z`'s old array is
outside the frame of an `IntPost`. -/
theorem out_post {rt : List (Nat × Nat)} {T : State} {M : Memory} {stk above z a n : Nat}
    (hr : Outside a n rt) (hw : Apart a n (T.sp.toNat - stk) (stk + above)) (hz : Apart a n z 32)
    (harr : 0 < M.readLE (z + 24) 8 → Apart a n (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8)) :
    Outside a n (rt ++ winA T stk above ++ (z, z + 32) :: RunIface.arrW M z) := by
  unfold Apart at hw hz
  by_cases hc : 0 < M.readLE (z + 24) 8
  · have := harr hc; unfold Apart at this
    simp only [winA, RunIface.arrW, if_pos hc, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨⟨hr, by omega, by omega⟩, by omega, by omega⟩
  · simp only [winA, RunIface.arrW, if_neg hc, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨⟨hr, by omega, by omega⟩, by omega⟩

open RunIface in
/-- `IntPre` of `x.Bytes()` on the result `z` of `Mod` / `exp` (same call site `SP`, `X28`), from the callee's
`IntPre` facts about `z` and its `IntPost`. -/
theorem intPre_one {R : RtInv} {b2 B2 : Nat} {L1 L2 : List (Nat × Nat)} {T : State} {M M1 : Memory} {stk above z : Nat}
    (hTm : T.mem = M) (hce : CallEnv R L1 T stk above) (hgl : Globals R M (win T stk above)) (hsv : Serves R)
    (hok0 : IntOK M R L1 z) (hzw : Outside z 32 (win T stk above)) (hzg : Apart z 32 ((T.regs 28).toNat + 16) 8)
    (harr : 0 < M.readLE (z + 24) 8 →
      Outside (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) (win T stk above) ∧
      Apart (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) ((T.regs 28).toNat + 16) 8 ∧
      Apart gA 32 (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8))
    (hgz : Apart gA 32 z 32)
    (hMF1 : MemFrame M M1 (R.rt ++ winA T stk above ++ (z, z + 32) :: arrW M z))
    (hreg : M1.regions = M.regions) (hext : LiveExt R L1 L2)
    (hinv2 : R.inv b2 L2 (T.regs 28).toNat (view R.rt L2 M1)) (hok : IntOK M1 R L2 z)
    (hor : 0 < M1.readLE (z + 24) 8 →
      (M1.readLE (z + 8) 8 = M.readLE (z + 8) 8 ∧ M1.readLE (z + 24) 8 = M.readLE (z + 24) 8) ∨
      (InRanges (M1.readLE (z + 8) 8) (8 * M1.readLE (z + 24) 8) R.rt ∧
        ApartAll (M1.readLE (z + 8) 8) (8 * M1.readLE (z + 24) 8) L1))
    (hB : B2 ≤ b2) :
    ∀ t : State, t.sp = T.sp → t.mem = M1 → t.regs 28 = T.regs 28 → IntPre R b2 B2 L2 stk above [z] t := by
  intro t hsp hm h28
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := hce
  rw [hTm] at hg2 hg3 hw hd
  obtain ⟨e0, e1, e2, e3, a1, a2, a3, hacc, hrt, hwg⟩ := hgl
  have hacc1 : ∀ a n w, M1.accessible a n w = M.accessible a n w := hMF1.accessible
  have hgM : M1.readLE ((T.regs 28).toNat + 16) 8 = M.readLE ((T.regs 28).toNat + 16) 8 :=
    hMF1.readLE _ _ (out_post hgr hga hzg.symm fun hc => (harr hc).2.1.symm)
  have hwr : ∀ r ∈ win T stk above, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by dsimp only; omega)
  have hwg' := hwg
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwg'
  have hG : ∀ k, k + 8 ≤ 32 → M1.readLE (gA + k) 8 = M.readLE (gA + k) 8 := fun k hk =>
    hMF1.readLE _ _ (out_post (hrt.of_sub (by omega) (by omega)) (by unfold Apart; omega)
      (by unfold Apart at hgz ⊢; omega) fun hc => by have := (harr hc).2.2; unfold Apart at this ⊢; omega)
  unfold IntPre CallEnv GuardOK StackOK win
  rw [hsp, hm, h28]
  refine ⟨⟨⟨hg1, by rw [hacc1]; exact hg2, by rw [hgM]; exact hg3⟩, ⟨hal, hb', ha, by rw [hacc1]; exact hw⟩, ?dl,
    hout, hga, hgr, hext.liveSep hLs hwr, hro⟩, hsv, ⟨?g1, ?g2, ?g3, ?g4, a1, a2, a3, by rw [hacc1]; exact hacc, hrt, hwg⟩,
    hB, hinv2, ?ints, List.pairwise_singleton _ _⟩
  case dl =>
    refine dataLoaded_frame hd hreg hro (by rw [List.append_assoc] at hMF1; exact hMF1) fun r hr hlt => ?_
    simp only [winA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨-, -, -, hza, -, hlv, -⟩ := hok0
    rcases hr with (rfl | rfl) | rfl | hr
    · exact Memory.accessible_mono _ hw (Nat.le_refl _) (by dsimp only; omega)
    · exact Memory.accessible_mono _ hw (by dsimp only; omega) (by dsimp only; omega)
    · simpa using hza
    · simp only [RunIface.arrW] at hr
      split at hr
      · rename_i hc; simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨-, -, h3, -⟩ := hlv hc
        simpa using h3
      · simp at hr
  case g1 => rw [a1, hG 8 (by omega), ← a1]; exact e0
  case g2 => rw [a2, hG 16 (by omega), ← a2]; exact e1
  case g3 => rw [a3, hG 24 (by omega), ← a3]; exact e2
  case g4 => exact (hG 0 (by omega)).trans e3
  case ints =>
    intro a ha
    simp only [List.mem_singleton] at ha; subst ha
    refine ⟨hok, by simpa [win] using hzw, fun hc => ?_, hzg, fun hc => ?_⟩
    · rcases hor hc with ⟨hp, hcc⟩ | ⟨hin, -⟩
      · rw [hp, hcc]; simpa [win] using (harr (by rw [← hcc]; exact hc)).1
      · have := InRanges.apart hin (hout : Outside _ _ R.rt)
        simp only [Janus.outside_cons, Janus.outside_nil, and_true]; unfold Apart at this; omega
    · rcases hor hc with ⟨hp, hcc⟩ | ⟨hin, -⟩
      · rw [hp, hcc]; exact (harr (by rw [← hcc]; exact hc)).2.1
      · exact (InRanges.apart hin hgr).symm

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts RunIface

/-- After `Mod`/`exp` on the first `*Int` `z` of the call: the callee's post, and the `IntPre` of `z.Bytes()` at the
same `SP`/`X28`. -/
theorem afterInt {R : RtInv} {b1 B B2 : Nat} {L1 : List (Nat × Nat)} {stk above z v : Nat} {ys : List Nat}
    {sc s' : State} {sp0 g : BitVec 64} {M : Memory}
    (hIP : ∀ t : State, t.sp = sp0 → t.mem = M → t.regs 28 = g → IntPre R b1 B L1 stk above (z :: ys) t)
    (hpost : IntPost R b1 B L1 stk above z v sc s') (e1 : sc.sp = sp0) (e2 : sc.mem = M) (e3 : sc.regs 28 = g)
    (hreg : s'.mem.regions = sc.mem.regions) (hgz : Apart gA 32 z 32)
    (hga : 0 < sc.mem.readLE (z + 24) 8 →
      Apart gA 32 (sc.mem.readLE (z + 8) 8) (8 * sc.mem.readLE (z + 24) 8))
    (hBB : B + B2 ≤ b1) :
    ∃ (L2 : List (Nat × Nat)) (b2 : Nat), LiveExt R L1 L2 ∧ b1 - B ≤ b2 ∧ IntV s'.mem z = v ∧
      R.inv b2 L2 (sc.regs 28).toNat (view R.rt L2 s'.mem) ∧ IntOK s'.mem R L2 z ∧
      MemFrame sc.mem s'.mem (R.rt ++ winA sc stk above ++ (z, z + 32) :: arrW sc.mem z) ∧
      LiveFrame sc.mem s'.mem L1 ((z, z + 32) :: arrW sc.mem z) ∧
      (∀ t : State, t.sp = sc.sp → t.mem = s'.mem → t.regs 28 = sc.regs 28 → IntPre R b2 B2 L2 stk above [z] t) := by
  obtain ⟨hv, L2, b2, hext, hb2, hinv2, hok, hor, hMF, hLF⟩ := hpost
  obtain ⟨hce, hsv, hgl, hB, -, hints, -⟩ := hIP sc e1 e2 e3
  obtain ⟨hok0, hzw, harw, hzg, harg⟩ := hints z (List.mem_cons_self ..)
  have hgl' : Globals R sc.mem (win sc stk above) := hgl
  refine ⟨L2, b2, hext, hb2, hv, hinv2, hok, hMF, hLF,
    intPre_one rfl hce hgl' hsv hok0 hzw hzg (fun hc => ⟨harw hc, harg hc, hga hc⟩) hgz hMF hreg hext hinv2 hok hor
      (by omega)⟩

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts RunIface

/-- An operand's word count is at most `⌈len / 8⌉` of its byte length. -/
theorem lenW_op {R : RtInv} {M : Memory} {s : State} {p len : BitVec 64} {L L1 : List (Nat × Nat)} {j : Nat}
    (h : OpDone R M s p len L L1 j) (hj : j < 3) : lenW M (opAt s j) ≤ opW s p len j := by
  obtain ⟨-, hv, hn, -⟩ := h
  simp only [natAt, show opAt s j + 8 + 8 = opAt s j + 16 by omega] at hv
  have hlt := padBE_lt s.mem p.toNat len.toNat (96 + opStart s p len j) (opLen s p len j)
  have hol : opLen s p len j = hdrV s p len j := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp only [opLen, ↓reduceIte] <;> rfl
  have h256 : (256 : Nat) ^ hdrV s p len j = 2 ^ (8 * hdrV s p len j) := by rw [Nat.pow_mul]
  have hlt' : natVal M (M.readLE (opAt s j + 8) 8) (M.readLE (opAt s j + 16) 8) < 2 ^ (8 * hdrV s p len j) := by
    rw [hv, ← h256, ← hol]; exact hlt
  exact len_le_of_lt M _ _ _ hn hlt'

theorem budget_mod {b b1 X w lw0 lw2 lb E A : Nat} (h0 : lw0 ≤ w) (h2 : lw2 ≤ w) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hB : X + (ModBudget w + E + BytesBudget maxW) + A ≤ b) :
    ModBudget (max lw0 lw2) + BytesBudget lb ≤ b1 := by
  have e1 : ModBudget (max lw0 lw2) ≤ ModBudget w := by
    unfold ModBudget opCost allocCost; omega
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

end FvModexp.Arm64.Run
