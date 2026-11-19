import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Amd64.Exp.SetRetWinX

set_option autoImplicit false

/-!
# `*Int`-level preconditions survive installing the return address (amd64, Janus v0.4.0 `hinv`; top s55)

`RunIface.IntPre` and the precondition of `RunIface.ExpSpec` (`(*Int).exp` as `Run` calls it) are invariant under
`State.setRet` when the return slot `[RSP, RSP + 8)` lies inside the window `win s stk above` (`8 ≤ above`): every
operand header (`Outside a 32 win`) and array (`Outside arr (8 cap) win`), the `natOne` words, the pool's `New` word and
the globals are outside the window (frame lemmas of `SetRetWin`). `janus64_pre_setRet` could not close the
`ModX` conjunct (its apartness fact is behind `0 < cap →`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.RunIface

open FvModexp.Amd64.SetRetWin

/-- a word of an operand header outside the window survives -/
theorem hdrRd {s : State} {ret stk above a k n : Nat} (hab : 8 ≤ above) (h : Outside a 32 (win s stk above))
    (hk : k + n ≤ 32) : (s.setRet ret).mem.readLE (a + k) n = s.mem.readLE (a + k) n :=
  rd hab (Outside.of_sub h (Nat.le_add_right a k) (by omega))

/-- the value of an operand array (length `l ≤ cap`) outside the window survives -/
theorem arrVal {s : State} {ret stk above p l c : Nat} (hab : 8 ≤ above)
    (h : 0 < c → Outside p (8 * c) (win s stk above)) (hl : l ≤ c) :
    natVal (s.setRet ret).mem p l = natVal s.mem p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · rw [h0, natVal_zero, natVal_zero]
  · exact rd hab (Outside.of_sub (h (by omega)) (Nat.le_refl _) (by omega))

/-- `NatNorm` of an operand array (length `l ≤ cap`) outside the window survives -/
theorem arrNorm {s : State} {ret stk above p l c : Nat} (hab : 8 ≤ above)
    (h : 0 < c → Outside p (8 * c) (win s stk above)) (hl : l ≤ c) (hn : NatNorm s.mem p l) :
    NatNorm (s.setRet ret).mem p l := by
  refine natNorm (stk := stk) hab ?_ hn
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (Outside.of_sub (h (by omega)) (Nat.le_refl _) (by omega))

theorem intOK_setRet {s : State} {ret stk above a : Nat} {R : RtInv} {L : List (Nat × Nat)} (hab : 8 ≤ above)
    (ho : Outside a 32 (win s stk above))
    (hA : 0 < s.mem.readLE (a + 24) 8 →
      Outside (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8) (win s stk above))
    (h : IntOK s.mem R L a) : IntOK (s.setRet ret).mem R L a := by
  have e8 := hdrRd (ret := ret) (k := 8) (n := 8) hab ho (by decide)
  have e16 := hdrRd (ret := ret) (k := 16) (n := 8) hab ho (by decide)
  have e24 := hdrRd (ret := ret) (k := 24) (n := 8) hab ho (by decide)
  have e0 : (s.setRet ret).mem.readLE a 1 = s.mem.readLE a 1 := rd hab (Outside.of_sub ho (Nat.le_refl _) (by omega))
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := h
  unfold IntOK
  rw [e0, e8, e16, e24, setRet_accessible]
  exact ⟨i1, i2, i3, i4, i5, natLive.2 i6, i7, arrNorm hab hA i7 i8, i9, i10⟩

theorem intPre_setRet {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {xs : List Nat} {s : State}
    {ret : Nat} (hab : 8 ≤ above) (h : IntPre R b B L stk above xs s) : IntPre R b B L stk above xs (s.setRet ret) := by
  unfold IntPre at h ⊢
  obtain ⟨hce, hsv, hG, hB, hinv, hops, hpw⟩ := h
  have hstk : stk ≤ (s.regs 4).toNat := hce.2.1.1
  have hlo : (s.regs 4).toNat - stk ≤ (s.regs 4).toNat := Nat.sub_le _ _
  have hhi : (s.regs 4).toNat + 8 ≤ (s.regs 4).toNat + above := Nat.add_le_add_left hab _
  have hsl : Outside (s.regs 4).toNat 8 R.rt :=
    Outside.of_sub hce.2.2.2.2.1 hlo (by rw [← Nat.add_assoc, Nat.sub_add_cancel hstk]; exact hhi)
  have hh : ∀ a ∈ xs, ∀ k, k + 8 ≤ 32 → (s.setRet ret).mem.readLE (a + k) 8 = s.mem.readLE (a + k) 8 :=
    fun a ha k hk => hdrRd hab (hops a ha).2.1 hk
  refine ⟨callEnv hab hce, hsv, globalsR hlo hhi hG, hB, by rw [view_setRet hsl]; exact hinv, fun a ha => ?_, ?_⟩
  · obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hops a ha
    rw [hh a ha 8 (by decide), hh a ha 24 (by decide)]
    exact ⟨intOK_setRet hab o2 o3 o1, o2, o3, o4, o5, o6, o7⟩
  · refine List.Pairwise.imp_of_mem ?_ hpw
    intro a a' ha ha' hp
    rw [hh a ha 8 (by decide), hh a ha 24 (by decide), hh a' ha' 8 (by decide), hh a' ha' 24 (by decide)]
    exact hp

/-- the `natOne` word survives (`OneG` keeps it outside the window) -/
theorem oneG_natOne {R : RtInv} {L : List (Nat × Nat)} {s : State} {ret stk above : Nat} {xs : List Nat}
    (hab : 8 ≤ above) (h : OneG R L s.mem (win s stk above) xs) :
    (s.setRet ret).mem.readLE natOneA 8 = s.mem.readLE natOneA 8 := by
  unfold OneG at h
  obtain ⟨op, ⟨-, -, -, -, -, -, n7, -⟩, -⟩ := h
  exact rd hab (Outside.of_sub n7 (Nat.le_refl _) (Nat.add_le_add_left (by decide) _))

theorem oneG_setRet {R : RtInv} {L : List (Nat × Nat)} {s : State} {ret stk above : Nat} {xs : List Nat}
    (hab : 8 ≤ above)
    (hh : ∀ a ∈ xs, ∀ k, k + 8 ≤ 32 → (s.setRet ret).mem.readLE (a + k) 8 = s.mem.readLE (a + k) 8)
    (h : OneG R L s.mem (win s stk above) xs) : OneG R L (s.setRet ret).mem (win (s.setRet ret) stk above) xs := by
  unfold OneG at h ⊢
  obtain ⟨op, ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩, hall⟩ := h
  refine ⟨op, ⟨(rd hab (Outside.of_sub n7 (Nat.le_refl _) (Nat.add_le_add_left (by decide) _))).trans n1,
    (rd hab (Outside.of_sub n7 (Nat.le_add_right _ _) (by rw [Nat.add_assoc]; exact Nat.add_le_add_left (by decide) _))).trans n2,
    (rd hab (Outside.of_sub n7 (Nat.le_add_right _ _) (by rw [Nat.add_assoc]; exact Nat.add_le_add_left (by decide) _))).trans n3,
    (rd hab n11).trans n4, by rw [setRet_accessible]; exact n5, n6, n7, by rw [setRet_accessible]; exact n8, n9, n10,
    n11⟩, fun a ha => ?_⟩
  rw [hh a ha 8 (by decide), hh a ha 24 (by decide)]
  exact hall a ha

/-- the precondition of `ExpSpec` survives -/
theorem expPre_setRet {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above : Nat} {z y mm : BitVec 64} {s : State}
    (ret : Nat) (hab : 8 ≤ above)
    (h : IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R s.mem (win s stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 wbA 4 ∧ ModX s.mem z.toNat) :
    IntPre R b (ExpBudget (max (max (lenW (s.setRet ret).mem z.toNat) (lenW (s.setRet ret).mem y.toNat))
          (lenW (s.setRet ret).mem mm.toNat)) (lenW (s.setRet ret).mem y.toNat)) L stk above
          [z.toNat, y.toNat, mm.toNat] (s.setRet ret) ∧ 0 < IntV (s.setRet ret).mem mm.toNat ∧
        IntLenLe (s.setRet ret).mem z.toNat maxW ∧ IntLenLe (s.setRet ret).mem y.toNat maxW ∧
        IntLenLe (s.setRet ret).mem mm.toNat maxW ∧
        OneG R L (s.setRet ret).mem (win (s.setRet ret) stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R (s.setRet ret).mem (win (s.setRet ret) stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 wbA 4 ∧
        ModX (s.setRet ret).mem z.toNat := by
  obtain ⟨hI, hv, hlz, hly, hlm, hone, hpool, hm0, hwb, hX⟩ := h
  have hops := hI.2.2.2.2.2.1
  have hh : ∀ a ∈ [z.toNat, y.toNat, mm.toNat], ∀ k, k + 8 ≤ 32 →
      (s.setRet ret).mem.readLE (a + k) 8 = s.mem.readLE (a + k) 8 :=
    fun a ha k hk => hdrRd hab (hops a ha).2.1 hk
  have hzm : z.toNat ∈ [z.toNat, y.toNat, mm.toNat] := by simp
  have hym : y.toNat ∈ [z.toNat, y.toNat, mm.toNat] := by simp
  have hmm : mm.toNat ∈ [z.toNat, y.toNat, mm.toNat] := by simp
  have hm := hops _ hmm
  unfold lenW IntLenLe IntV ModX at *
  rw [hh _ hzm 16 (by decide), hh _ hym 16 (by decide), hh _ hmm 16 (by decide), hh _ hzm 8 (by decide),
    hh _ hzm 24 (by decide), hh _ hmm 8 (by decide)]
  unfold PoolG at hpool ⊢
  obtain ⟨p1, p2, p3, p4⟩ := hpool
  refine ⟨intPre_setRet hab hI, ?_, hlz, hly, hlm, oneG_setRet hab hh hone, ⟨p1, (rd hab p4).trans p2, p3, p4⟩, hm0,
    hwb, hX⟩
  rw [arrVal hab hm.2.2.1 hm.1.2.2.2.2.2.2.1]
  exact hv

end FvModexp.Amd64.RunIface
