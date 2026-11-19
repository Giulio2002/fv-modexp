import FvModexp.Proofs.Amd64.Nat.StackNatXN

set_option autoImplicit false

/-!
# `(*stack).nat` (amd64): the preconditions of the `growslice` and `memclrNoHeapPointers` calls of `slices.Grow`
(pure lemmas about an abstract call state, the amd64 twin of Arm64/Nat/StackNatCall.lean; Janus has no amd64
`call_pre`, so the conjuncts are proved directly)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNatX

open FvModexp.Amd64.StackNat (fn names wbA rnd)

/-- `type:big.Word` (growslice's element type) -/
abbrev wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- A data object of the program is readable (adapted from Janus v0.2.0
`Janus/Contracts/PanicWitnessAmd64.lean` `accessible_of_dataRead`, which lives in a witness module). -/
theorem accessible_of_dataRead' {p : Janus.Amd64.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {a n : Nat}
    (hv : (dataRead p a n).isSome = true) : m.accessible a n false = true := by
  unfold dataRead at hv
  cases hd : dataSegAt p a n with
  | none => rw [hd] at hv; cases hv
  | some d =>
    unfold dataSegAt at hd
    have hmem := List.mem_of_find?_eq_some hd
    have hp := List.find?_some hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hreg, _⟩ := h d hmem
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
    obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, hw⟩, _⟩⟩ := hreg
    exact Janus.Arm64.Memory.accessible_of_mem m hr (by omega) (by omega) hw

theorem wT_facts {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE wT 8 = 8 ∧ m.readLE (wT + 8) 8 = 0 ∧ m.accessible wT 16 false = true :=
  ⟨Janus.Amd64.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Amd64.Tactic.readLE_of_dataRead hd (by decide +kernel), accessible_of_dataRead' hd (by decide +kernel)⟩

set_option maxRecDepth 20000 in
/-- the `growslice(w, len + nr, cap, len + nr - cap, Word)` call from `(*stack).nat`'s frame (`RSP' = RSP - 0x60`
at the callee's entry) -/
theorem gcall_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State}
    (hpre : PreX R b L 4192 24 st n s) (hk : stCap s.mem st < stLen s.mem st + rnd n) (S : State)
    (hF : MemFrame s.mem S.mem [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)])
    (hsp : (S.regs 4).toNat + 96 = (s.regs 4).toNat) (h14 : S.regs 14 = s.regs 14)
    (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (h0 : (S.regs 0).toNat = stW s.mem st) (h3 : (S.regs 3).toNat = stLen s.mem st + rnd n)
    (h1 : (S.regs 1).toNat = stCap s.mem st) (h7 : (S.regs 7).toNat = stLen s.mem st + rnd n - stCap s.mem st)
    (h6 : (S.regs 6).toNat = wT) :
    GrowslicePre64 4096 S ∧ StackRoom64 S 4096 5 ∧
      LiveAt R (cA "runtime.growslice") (growsliceArgs64 S) L b (growsliceRound64 S) (S.regs 14).toNat S.mem
        (liveWin64 S 4096 5) := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n ≤ n + 3 := by simp only [rnd]; omega
  simp only [stLen, stCap, stW] at hk hln h0 h3 h1 h7 hlc hcb hcost
  have hwT : Apart wT 16 ((s.regs 4).toNat - 4192) (4192 + 24) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hga hwT
  obtain ⟨ht1, ht2, ht3⟩ := wT_facts hd
  have hwTv : wT = 7233184 := rfl
  rw [hwTv] at ht1 ht2 ht3 hwT h6
  have hwin : LiveSep [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)] R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only
    rw [show (s.regs 4).toNat + 24 - ((s.regs 4).toNat - 4192) = 4192 + 24 by omega]; exact hout
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨⟨⟨hra, by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hp => ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [h6]; exact ⟨by omega, by rw [hF.accessible]; exact ht3⟩
  · simp only [typSize, h6]; rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact ht1
  · simp only [typPtrBytes, h6]; rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact ht2
  · omega
  · omega
  · omega
  · omega
  · -- v0.3.1: the type descriptor (rodata) is outside the callee's window
    rw [h6]; simp only [calleeStack64, outside_cons, outside_nil, and_true]; omega
  · have e : (S.regs 3).toNat - (S.regs 7).toNat = s.mem.readLE (st + 16) 8 := by omega
    unfold GrowsliceOld64
    rw [e] at hp ⊢
    obtain ⟨-, -, a3, a4⟩ := hnl hp
    have ha5 := (harr hp).1
    simp only [win, outside_cons, outside_nil, and_true, stW, stCap] at ha5
    rw [h0]
    refine ⟨a4, by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ a3, ?_⟩
    -- v0.3.1: the old array is outside the callee's window (it is outside the caller's window)
    simp only [stW, calleeStack64, outside_cons, outside_nil, and_true]; omega
  · rw [h14]; omega
  · rw [h14, hF.accessible]; exact hg2
  · rw [h14, hgS]; omega
  · rw [h14]; simp only [calleeStack64, outside_cons, outside_nil, and_true]; omega
  · simp only [growsliceArgs64, h0, h3, h1, h7, h6]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega)
  · rw [h14]; exact RtInv.inv_frame hF hwin hinv0
  · simp only [growsliceRound64, h3, h1]; exact hcost hk
  · intro r hr
    have := hLs r hr
    simp only [win, liveWin64, calleeStack64, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro r hr
    simp only [liveWin64, calleeStack64, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)

set_option maxRecDepth 20000 in
/-- the `memclrNoHeapPointers(p + 8·cap, 8·(len + nr - cap))` call after `growslice` returned the block `(p, 8·gc)` -/
theorem mcall_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State}
    (hpre : PreX R b L 4192 24 st n s) (hk : stCap s.mem st < stLen s.mem st + rnd n) {L1 : List (Nat × Nat)}
    {b1 p gc : Nat} (S : State)
    (hF : MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)]))
    (hsp : (S.regs 4).toNat + 96 = (s.regs 4).toNat) (h14 : S.regs 14 = s.regs 14)
    (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) (hx15 : S.xmm 15 = 0#128) (hdf : S.df = false)
    (hL1 : L1 = L ++ [(p, p + 8 * gc)]) (hgc : stLen s.mem st + rnd n ≤ gc)
    (hpin : InRanges p (8 * gc) R.rt) (hp48 : p + 8 * gc ≤ 2 ^ 48) (hpacc : S.mem.accessible p (8 * gc) true = true)
    (hinv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S.mem))
    (h0 : (S.regs 0).toNat = p + 8 * stCap s.mem st)
    (h3 : (S.regs 3).toNat = 8 * (stLen s.mem st + rnd n - stCap s.mem st)) :
    MemPre64 4096 2 S ∧
      LiveMemAt64 R (cA "runtime.memclrNoHeapPointers") [(S.regs 0).toNat, (S.regs 3).toNat] L1 b1 S
        (liveWin64 S 4096 2) ∧
      LiveDest64 R L1 S 4096 2 (S.regs 0).toNat (S.regs 3).toNat := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n ≤ n + 3 := by simp only [rnd]; omega
  simp only [stLen, stCap] at hk hgc hlc hln h3 h0
  unfold Apart at hga
  have hpw := hpin.apart hout
  unfold Apart at hpw
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hF.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, by omega, ?_, hx15, hdf, hra⟩, ?_⟩, ⟨?_, by rw [h14]; exact hinv, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stackguard0Offset, regG, h14]; omega
  · simp only [stackguard0Offset, regG, h14]; rw [hF.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP, h14]; rw [hgS]; omega
  · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
  · rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, h14, outside_cons, outside_nil, and_true]; omega
  · exact hsv.2.2.1 _ _ (by rw [h3]; omega)
  · rw [hL1]; intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr
      simp only [win, liveWin64, calleeStack64, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true] at this ⊢
      omega
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [liveWin64, calleeStack64, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
      omega
  · intro r hr
    simp only [liveWin64, calleeStack64, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  · rw [h0, h3]; omega
  · rw [h0, h3]
    exact Janus.Arm64.Memory.accessible_mono _ hpacc (by omega) (by omega)
  · simp only [calleeStack64, outside_cons, outside_nil, and_true]; rw [h0, h3]; omega
  · left; rw [hL1, h0, h3]
    exact ⟨(p, p + 8 * gc), List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
      by simp only; omega⟩
  · simp only [outside_cons, outside_nil, and_true]; rw [h0, h3]; omega

end FvModexp.Amd64.StackNatX
