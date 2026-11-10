import FvModexp.Proofs.Amd64.Nat.SetBytesStdDefs

/-! # `nat.setBytes` (amd64): establishing `Mid` at the word-loop head (reuse of `z`, or `makeslice`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.SetBytesStd

/-- `z` is reused (`nW ≤ zc`): the memory `M0` at the head is the entry memory with stack stores. -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc bp bl : BitVec 64} {s : State} {ret : Nat}
    {M0 : Janus.Arm64.Memory} (hlive : NatLive s.mem R L zp.toNat zc.toNat)
    (hzb : 0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) bp.toNat bl.toNat)
    (hzw : 0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4160 48) ∧
      Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8)
    (hLs : LiveSep L (win s 4160 48)) (hout : Outside ((s.regs 4).toNat - 4160) (4160 + 48) R.rt) (hsp : 4160 ≤ (s.regs 4).toNat)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (hnz : nW bl ≤ zc.toNat) (hz0 : 0 < zc.toNat)
    (h1 : M0.readLE (s.regs 4).toNat 8 = ret) (h2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hbuf : ∀ a k, bp.toNat ≤ a → a + k ≤ bp.toNat + bl.toNat → M0.readLE a k = s.mem.readLE a k)
    (hF : MemFrame s.mem M0 (win s 4160 48)) :
    Mid R b L zp zc bp bl s ret zp.toNat zc.toNat L b M0 := by
  obtain ⟨h8, hheld, hacc, hle⟩ := hlive hz0
  have hw := (hzw hz0).1
  simp only [Outside, and_true] at hw
  refine ⟨h1, h2, hbuf, hnz, h8, hle, by rw [hF.accessible]; exact hacc, hzb hz0, by unfold Apart; omega, hheld,
    LiveExt.refl R L, Nat.sub_le _ _, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · refine RtInv.inv_frame' hF (fun r hr => ?_) hinv
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; left
    exact hout.of_sub (Nat.le_refl _) (by omega)
  · exact hF.mono fun a n h => by simp only [Janus.outside_append] at h; exact h.1.2
  · exact LiveFrame.of_win hF hLs

theorem apartAll_sub {a n k : Nat} {L : List (Nat × Nat)} (h : ApartAll a n L) (hk : k ≤ n) : ApartAll a k L :=
  fun r hr => by have := h r hr; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- `nat.make` allocated: the array is `makeslice`'s fresh block `[ptr, ptr + round)`; `M0` is the memory at the call. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc bp bl : BitVec 64} {s : State} {ret : Nat}
    {M0 m : Janus.Arm64.Memory} {ptr round c : Nat}
    (hLs : LiveSep L (win s 4160 48)) (hout : Outside ((s.regs 4).toNat - 4160) (4160 + 48) R.rt) (hsp : 4160 ≤ (s.regs 4).toNat)
    (hheld : Held R L bp.toNat bl.toNat) (hbwin : Outside bp.toNat bl.toNat (win s 4160 48))
    (h1 : M0.readLE (s.regs 4).toNat 8 = ret) (h2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hbuf : ∀ a k, bp.toNat ≤ a → a + k ≤ bp.toNat + bl.toNat → M0.readLE a k = s.mem.readLE a k)
    (hF : MemFrame s.mem M0 (win s 4160 48))
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [((s.regs 4).toNat - 56 - 4096, (s.regs 4).toNat - 56), ((s.regs 4).toNat - 56 + 8, (s.regs 4).toNat - 56 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr ≤ 2 ^ 48 - round)
    (hacc : s.mem.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost (nW bl)) (hnc : nW bl ≤ c) :
    Mid R b L zp zc bp bl s ret ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  have hcw : ∀ a k, Outside a k R.rt → a + k ≤ (s.regs 4).toNat - 4160 ∨ (s.regs 4).toNat - 24 ≤ a →
      Outside a k (R.rt ++ [((s.regs 4).toNat - 56 - 4096, (s.regs 4).toNat - 56), ((s.regs 4).toNat - 56 + 8, (s.regs 4).toNat - 56 + 8 + 24)]) := by
    intro a k ha hk
    rw [Janus.outside_append]
    refine ⟨ha, ?_⟩
    have hs := hsp
    generalize (s.regs 4).toNat = sp at hk hs ⊢
    show (a + k ≤ sp - 56 - 4096 ∨ sp - 56 ≤ a) ∧ (a + k ≤ sp - 56 + 8 ∨ sp - 56 + 8 + 24 ≤ a) ∧ True
    refine ⟨by omega, by omega, trivial⟩
  have hrtw : ∀ a k, (s.regs 4).toNat - 4160 ≤ a → a + k ≤ (s.regs 4).toNat + 48 → Outside a k R.rt :=
    fun a k ha hk => hout.of_sub ha (by omega)
  have hbufm : ∀ a k, bp.toNat ≤ a → a + k ≤ bp.toNat + bl.toNat → m.readLE a k = s.mem.readLE a k := by
    intro a k ha hk
    rw [← hbuf a k ha hk]
    rcases hheld with hin | hrt
    · exact hLF.readLE a k (hin.sub ha hk) trivial
    · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hbwin
      exact hMF.readLE a k (hcw a k (hrt.of_sub ha hk) (by omega))
  have hApb : Apart ptr round bp.toNat bl.toNat := by
    rcases hheld with hin | hrt
    · exact ApartAll.apart_of_inRanges hAp hin
    · exact (InRanges.apart hIn hrt).symm
  have hApw : Apart ptr round ((s.regs 4).toNat - 4160) (4160 + 48) := (InRanges.apart hIn hout).symm
  unfold Apart at hApb hApw
  have hround : round ≤ 2 ^ 48 := by have := Janus.Arm64.Memory.accessible_bound _ hacc; omega
  refine ⟨?_, ?_, hbufm, hnc, h8, by omega, ?_, by unfold Apart; omega, by unfold Apart; omega,
    Or.inl ((inRanges_snoc L ptr round).sub (Nat.le_refl _) (by omega)),
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, hinv,
    Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), apartAll_sub hAp hsz⟩, ?_, ?_⟩
  · rw [hMF.readLE _ _ (hcw _ _ (hrtw _ _ (by omega) (by omega)) (by omega)), h1]
  · rw [hMF.readLE _ _ (hcw _ _ (hrtw _ _ (by omega) (by omega)) (by omega)), h2]
  · rw [hMF.accessible, hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  · refine hF.trans hMF fun a k h => ?_
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    exact ⟨h.1.2, h.1.1, by omega, by omega⟩
  · exact (LiveFrame.of_win hF hLs).trans (LiveFrame.of_nil' hLF _) fun _ _ h => h

end FvModexp.Amd64.SetBytesStd

namespace FvModexp.Amd64.SetBytesStd

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- The empty buffer: `z[:0]` is returned, only the frame's stack slots were written. -/
theorem post_empty {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc bp bl : BitVec 64} {s s' : State}
    (hF : MemFrame s.mem s'.mem (win s 4160 48)) (h0 : (s'.regs 0).toNat = zp.toNat) (h1 : (s'.regs 3).toNat = 0)
    (h2 : (s'.regs 1).toNat = zc.toNat) (hbl : bl.toNat = 0) (hlive : NatLive s.mem R L zp.toNat zc.toNat)
    (hLs : LiveSep L (win s 4160 48)) (hout : Outside ((s.regs 4).toNat - 4160) (4160 + 48) R.rt)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) : Post R b L zp zc bp bl s s' := by
  refine ⟨zp.toNat, 0, zc.toNat, h0, h1, h2, by simp [hbl], Or.inl rfl,
    Nat.zero_le _, Nat.zero_le _, L, b, LiveExt.refl R L, Nat.sub_le _ _, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · refine RtInv.inv_frame' hF (fun r hr => ?_) hinv
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; left
    exact hout.of_sub (Nat.le_refl _) (by omega)
  · intro hc
    obtain ⟨h8, hh, hacc, hle⟩ := hlive hc
    exact ⟨h8, hh, by rw [hF.accessible]; exact hacc, hle⟩
  · exact hF.mono fun a n h => by simp only [Janus.outside_append] at h; exact h.1.2
  · exact LiveFrame.of_win hF hLs

end FvModexp.Amd64.SetBytesStd
