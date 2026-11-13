import FvModexp.Proofs.Amd64.Exp.OddDefs

set_option autoImplicit false

/-!
# `nat.expNNOdd` (amd64): the postcondition from a window's postcondition (agent expmc s64; twin of `Arm64.OddPost`)

A window's post (`ExpW4.PostG` / `ExpW2.PostG`, unfolded: cost `C`, stack window `win S stk 0x70` with bottom
`t - 0x390 - K`) at its entry state `S` (after the prologue's stores, frame `[(t - 0x78, t), (t + 0x38, t + 0x60)]`,
`t` = the entry `RSP`) and the epilogue's final state `s''` give `ExpOdd.PostG` at the entry state `s`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpOdd

/-- the prologue's written ranges -/
@[reducible] def pw (t : Nat) : List (Nat × Nat) := [(t - 0x78, t), (t + 0x38, t + 0x60)]

theorem out_pw {a k t K : Nat} (h : Apart a k (t - 0x388 - 8 - K) (K + 0x400)) (hK : K + 0x390 ≤ t) :
    Outside a k (pw t) := by
  unfold Apart at h; simp only [pw, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem post_gen {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat}
    {st zp zc xp xl xc yp ylen mp n mc costD : Nat} {s S s' s'' : State} {C stk : Nat}
    (hP : ExpW4.EPreA R b L K (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x388) st zp zc xp xl xc yp ylen
      mp n mc s)
    (hFs : MemFrame s.mem S.mem (pw (s.regs 4).toNat))
    (hSsp : (S.regs 4).toNat = (s.regs 4).toNat - 0x78) (hstk : stk = K + 0x318) (h14 : S.regs 14 = s.regs 14)
    (hC : C = OCost n xl ylen costD (stLen s.mem st) ∨ C = OCost n xl ylen costD (stLen S.mem st))
    (hq : ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧
      s'.regs 1 = BitVec.ofNat 64 c ∧
      natVal s'.mem p l = natVal S.mem xp xl ^ natVal S.mem yp ylen % natVal S.mem mp n ∧ NatNorm s'.mem p l ∧
      l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧
      ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - C ≤ b' ∧
        R.inv b' L' (S.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
        ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
        StackBackL R L L' st S.mem s'.mem ∧
        MemFrame S.mem s'.mem (R.rt ++ win S stk 0x70 ++ [(zp, zp + 8 * zc)] ++ stkWs S.mem st) ∧
        LiveFrame S.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs S.mem st) ∧ ResSep S.mem s'.mem st p c)
    (e0 : s''.regs 0 = s'.regs 0) (e3 : s''.regs 3 = s'.regs 3) (e1 : s''.regs 1 = s'.regs 1)
    (em : s''.mem = s'.mem) :
    PostG R b L K costD (s.regs 14).toNat zp zc st xp xl yp ylen mp n s s'' := by
  obtain ⟨⟨-, -, -, -, -, -, hK1, -, hCE, -⟩, -, -, -, -, -, -, -, hmO, -, -, -, hyO, -, -, -, -, -, hxO, -, -, -, -, -,
    hxc0, -, -, -, -, -, -, hstw, -, -, harr, -, -, -, -, -, -, -, -, -⟩ := hP
  obtain ⟨-, hK0, -, -, -, -, -, hrt, -, -, hLs, -⟩ := hCE
  generalize ht : (s.regs 4).toNat = t at hSsp hFs hmO hyO hxO hstw harr hK0 hrt hLs
  have rd : ∀ {a k : Nat}, Apart a k (t - 0x388 - 8 - K) (K + 0x400) → S.mem.readLE a k = s.mem.readLE a k :=
    fun h => hFs.readLE _ _ (out_pw h (by omega))
  have ew : stW S.mem st = stW s.mem st := rd (by unfold Apart at hstw ⊢; omega)
  have el : stLen S.mem st = stLen s.mem st := rd (by unfold Apart at hstw ⊢; omega)
  have ec : stCap S.mem st = stCap s.mem st := rd (by unfold Apart at hstw ⊢; omega)
  have hws : stkWs S.mem st = stkWs s.mem st := by simp only [stkWs, ew, el, ec]
  obtain ⟨p, l, c, q0, q1, q2, hv, hn, hlc, hc, L', b', hx, hb, hinv, hlive, hof, hsb, hF, hLF, hRS⟩ := hq
  refine ⟨p, l, c, e0.trans q0, e3.trans q1, e1.trans q2, ?_, by rw [em]; exact hn, hlc, hc, L', b', hx, ?_,
    by rw [em, ← h14]; exact hinv, by rw [em]; exact hlive, hof, ?_, ?_, ?_, ?_⟩
  · rw [em, hv]; simp only [natVal]
    rw [rd (by have := hxO.2.1; unfold Apart at this ⊢; omega), rd hyO.2.1, rd hmO.2.1]
  · rcases hC with rfl | rfl
    · exact hb
    · rw [el] at hb; exact hb
  · obtain ⟨⟨k1, k2, k3⟩, k4⟩ := hsb
    rw [em]
    refine ⟨⟨k1, k2.trans el, by rw [← ew, ← ec]; exact k3⟩, fun hn => k4 ?_⟩
    rw [ew, ec]; exact hn
  · rw [em]
    refine MemFrame.trans hFs hF fun a k ho => ?_
    rw [outside_append, outside_append, outside_append] at ho
    obtain ⟨⟨⟨hr, hw⟩, hz⟩, hs⟩ := ho
    simp only [win, ht, outside_cons, outside_nil, and_true] at hw
    refine ⟨by simp only [pw, outside_cons, outside_nil, and_true]; omega, ?_⟩
    rw [hws, outside_append, outside_append, outside_append]
    refine ⟨⟨⟨hr, ?_⟩, hz⟩, hs⟩
    simp only [win, hSsp, hstk, outside_cons, outside_nil, and_true]; omega
  · rw [em, ← hws]
    refine (LiveFrame.of_win (hFs.mono fun a k ho => ?_) (LiveSep.sub_win hLs (Nat.le_refl (t - 0x388 - 8 - K))
      (Nat.le_refl _))).trans hLF fun _ _ h => h
    simp only [pw, outside_cons, outside_nil, and_true] at ho ⊢; omega
  · rw [em]; exact ResSep.pre hRS ew ec

set_option maxRecDepth 20000 in
/-- `expNNOdd`'s saved `BP` and return address (`[t - 8, t + 8)`) are outside a window's framed ranges -/
theorem slot_keep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat}
    {st zp zc xp xl xc yp ylen mp n mc : Nat} {s S : State} {stk : Nat}
    (hP : ExpW4.EPreA R b L K (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x388) st zp zc xp xl xc yp ylen
      mp n mc s)
    (hzA : Apart zp (8 * zc) ((s.regs 4).toNat - 0x388 - 8 - K) (K + 0x400))
    (hc0 : stCap s.mem st = 0 → stW s.mem st = 0)
    (hFs : MemFrame s.mem S.mem (pw (s.regs 4).toNat))
    (hSsp : (S.regs 4).toNat = (s.regs 4).toNat - 0x78) (hstk : stk = K + 0x318) :
    Outside ((s.regs 4).toNat - 8) 16 (R.rt ++ win S stk 0x70 ++ [(zp, zp + 8 * zc)] ++ stkWs S.mem st) := by
  obtain ⟨⟨-, -, -, -, -, -, hK1, -, hCE, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hstw, -, -, harr, -, -, -, -, -, -, -, -, -⟩ := hP
  obtain ⟨-, hK0, -, -, -, -, -, hrt, -, -, -, -⟩ := hCE
  generalize ht : (s.regs 4).toNat = t at hSsp hFs hzA hstw harr hK0 hrt
  have rd : ∀ {a k : Nat}, Apart a k (t - 0x388 - 8 - K) (K + 0x400) → S.mem.readLE a k = s.mem.readLE a k :=
    fun h => hFs.readLE _ _ (out_pw h (by omega))
  have ew : stW S.mem st = stW s.mem st := rd (by unfold Apart at hstw ⊢; omega)
  have el : stLen S.mem st = stLen s.mem st := rd (by unfold Apart at hstw ⊢; omega)
  have ec : stCap S.mem st = stCap s.mem st := rd (by unfold Apart at hstw ⊢; omega)
  have hfree : t - 8 + 16 ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ t - 8 := by
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · have := hc0 h0; omega
    · have := (harr h0).1; unfold Apart at this; omega
  unfold Apart at hzA hstw
  rw [outside_append, outside_append, outside_append]
  refine ⟨⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [win, hSsp, hstk, outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, ew, el, ec, outside_cons, outside_nil, and_true]; omega

end FvModexp.Amd64.ExpOdd
