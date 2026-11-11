import FvModexp.Proofs.Amd64.Int.IntBytesDefs

/-! # `(*Int).Bytes` (amd64): the facts after `makeslice` (frames of the call, the loop-head invariant `Inv … 0`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface

namespace FvModexp.Amd64.IntBytes

theorem apartAll_sub {a n k : Nat} {L : List (Nat × Nat)} (h : ApartAll a n L) (hk : k ≤ n) : ApartAll a k L :=
  fun r hr => by have := h r hr; unfold Apart at this ⊢; omega

/-- The makeslice callee stack (`RSP = s.rsp - 48` at the callee) as the contract states it. -/
@[reducible] def csW (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 48 - 4096, (s.regs 4).toNat - 48), ((s.regs 4).toNat - 48 + 8, (s.regs 4).toNat - 48 + 8 + 24)]

set_option maxRecDepth 20000 in
theorem cs_out {R : RtInv} {s : State} {a k : Nat} (hsp : 4160 ≤ (s.regs 4).toNat) (ha : Outside a k R.rt)
    (hk : a + k ≤ (s.regs 4).toNat - 4160 ∨ (s.regs 4).toNat - 16 ≤ a) : Outside a k (R.rt ++ csW s) := by
  rw [Janus.outside_append]
  refine ⟨ha, ?_⟩
  have hs := hsp
  simp only [csW]
  generalize (s.regs 4).toNat = sp at hk hs ⊢
  simp only [Janus.outside_cons, Janus.outside_nil, and_true]
  exact ⟨by omega, by omega⟩

/-- A range held by the caller and outside the frame window reads the same after the call as at entry. -/
theorem read_kept {R : RtInv} {L : List (Nat × Nat)} {s : State} {M0 m : Janus.Arm64.Memory} {a0 n0 : Nat}
    (hsp : 4160 ≤ (s.regs 4).toNat) (hH : Held R L a0 n0)
    (hW : a0 + n0 ≤ (s.regs 4).toNat - 4160 ∨ (s.regs 4).toNat + 16 ≤ a0)
    (hbuf : ∀ a k, a0 ≤ a → a + k ≤ a0 + n0 → M0.readLE a k = s.mem.readLE a k)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ csW s)) :
    ∀ a k, a0 ≤ a → a + k ≤ a0 + n0 → m.readLE a k = s.mem.readLE a k := by
  intro a k ha hk
  rw [← hbuf a k ha hk]
  rcases hH with hin | hrt
  · exact hLF.readLE a k (hin.sub ha hk) trivial
  · exact hMF.readLE a k (cs_out hsp (hrt.of_sub ha hk) (by omega))

set_option maxRecDepth 20000 in
/-- The frame of entry → after the call: stack stores in the window, then the callee's ranges. -/
theorem frame_call {R : RtInv} {s : State} {M0 m : Janus.Arm64.Memory} (hsp : 4160 ≤ (s.regs 4).toNat)
    (hF : MemFrame s.mem M0 (win s 4160 16)) (hMF : MemFrame M0 m (R.rt ++ csW s)) :
    MemFrame s.mem m (R.rt ++ win s 4160 16) := by
  refine hF.trans hMF fun a k h => ?_
  simp only [win, csW, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  obtain ⟨hr, hw⟩ := h
  exact ⟨hw, hr, by omega, by omega⟩

set_option maxRecDepth 20000 in
/-- The loop-head invariant with no byte stored yet, from `makeslice`'s post (`[ptr, ptr + round)` fresh). -/
theorem inv_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {x : BitVec 64} {s : State} {ret : Nat}
    {M0 m : Janus.Arm64.Memory} {ptr round ap N : Nat}
    (hLs : LiveSep L (win s 4160 16)) (hout : Outside ((s.regs 4).toNat - 4160) (4160 + 16) R.rt)
    (hsp : 4160 ≤ (s.regs 4).toNat)
    (hH : Held R L ap N) (hW : ap + N ≤ (s.regs 4).toNat - 4160 ∨ (s.regs 4).toNat + 16 ≤ ap)
    (h1 : M0.readLE (s.regs 4).toNat 8 = ret) (h2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hbuf : ∀ a k, ap ≤ a → a + k ≤ ap + N → M0.readLE a k = s.mem.readLE a k)
    (hF : MemFrame s.mem M0 (win s 4160 16)) (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ csW s))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : s.mem.accessible ptr round true = true)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : N ≤ round) (hcost : round ≤ BytesBudget (N / 8)) (hN : 0 < N) :
    Inv R b L x s ret ptr ap N 0 (L ++ [(ptr, ptr + round)]) (b - round) m := by
  have hApb : Apart ptr round ap N := by
    rcases hH with hin | hrt
    · exact ApartAll.apart_of_inRanges hAp hin
    · exact (InRanges.apart hIn hrt).symm
  have hApw : Apart ptr round ((s.regs 4).toNat - 4160) (4160 + 16) := (InRanges.apart hIn hout).symm
  unfold Apart at hApb hApw
  refine ⟨?_, ?_, read_kept hsp hH hW hbuf hLF hMF, hN, by omega, ?_, by unfold Apart; omega, by unfold Apart; omega,
    (inRanges_snoc L ptr round).sub (Nat.le_refl _) (by omega), hIn.sub (Nat.le_refl _) (by omega),
    apartAll_sub hAp hsz, fun i hi => absurd hi (Nat.not_lt_zero _),
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, hinv, frame_call hsp hF hMF, ?_⟩
  · rw [hMF.readLE _ _ (cs_out hsp (hout.of_sub (by omega) (by omega)) (by omega)), h1]
  · rw [hMF.readLE _ _ (cs_out hsp (hout.of_sub (by omega) (by omega)) (by omega)), h2]
  · rw [hMF.accessible, hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  · exact (LiveFrame.of_win hF hLs).trans (LiveFrame.of_nil' hLF _) fun _ _ h => h

set_option maxRecDepth 20000 in
/-- `len(abs) = 0`: `makeslice(uint8, 0, 0)` (live set and budget kept), no loop iteration, `buf[0:]` returned. -/
theorem post_zero {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {x : BitVec 64} {s s' : State} {M0 m : Janus.Arm64.Memory}
    (hLs : LiveSep L (win s 4160 16)) (hsp : 4160 ≤ (s.regs 4).toNat)
    (hF : MemFrame s.mem M0 (win s 4160 16)) (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ csW s))
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L m)) (hl0 : s.mem.readLE (x.toNat + 16) 8 = 0)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) (hm : s'.mem = m) (h1 : (s'.regs 3).toNat = 0) (h2 : (s'.regs 1).toNat = 0) :
    Post R b L x s s' := by
  refine ⟨hfs, hdf, _, 0, 0, rfl, h1, h2, Nat.le_refl _, ?_, Or.inl rfl, L, b, LiveExt.refl R L, Nat.sub_le _ _,
    by rw [hm]; exact hinv, fun h => absurd h (Nat.lt_irrefl _), by rw [hm]; exact frame_call hsp hF hMF, ?_⟩
  · simp only [beVal_zero, IntV, hl0]; rfl
  · rw [hm]; exact (LiveFrame.of_win hF hLs).trans hLF fun _ _ h => h

end FvModexp.Amd64.IntBytes
