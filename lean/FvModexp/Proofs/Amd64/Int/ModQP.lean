import FvModexp.Proofs.Amd64.Int.QRLem
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `(*Int).Mod` (amd64): `QRPre` at `QuoRem`'s entry from `Mod`'s precondition (pure)

`intPre_shift`: `IntPre` moves to a callee entry state whose `RSP` is `f` bytes lower and whose window lies inside the
caller's, the memory changing only inside the caller's window (adapted from top's `intPre_move`, Amd64/Top/RunC2Lem3).
`qrPre_of`: `QRPre R b L stkQ 128 (t - 72) z y SQ` at `QuoRem`'s entry (`RSP = t - 168`), from `ModSpec`'s precondition
at `Mod`'s entry (`RSP = t`), `hasADX` readable, and segment A's frame and `q` stores.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntOK IntPre IntPost IntV IntLenLe maxW ModBudget lenW PoolG ModX arrW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `IntPre` at a callee entry `S1` (`RSP` lower by `f`, window inside the caller's, memory changed only in the
caller's window) -/
theorem intPre_shift {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {xs : List Nat} {s S1 : State}
    {f stk1 above1 : Nat} (h : IntPre R b B L stk above xs s)
    (hF : MemFrame s.mem S1.mem (win s stk above))
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hreg : S1.mem.regions = s.mem.regions) (hk : f + stk1 ≤ stk) (ha : above1 ≤ f + above) (hf8 : f % 8 = 0) :
    IntPre R b B L stk1 above1 xs S1 := by
  obtain ⟨hce, hsv, hgl, hB, hinv, hints, hpw⟩ := h
  have hce0 := hce
  obtain ⟨-, ⟨hst, -, -⟩, -, -, hrt, -, -, hLs, -⟩ := hce
  simp only [regSP] at hst
  have hF' : MemFrame s.mem S1.mem (R.rt ++ win s stk above) := hF.mono fun a k h => by
    simp only [outside_append] at h; exact h.2
  have hsub : ∀ a n, Outside a n (win s stk above) → Outside a n (win S1 stk1 above1) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hrd : ∀ a n, Outside a n (win s stk above) → S1.mem.readLE a n = s.mem.readLE a n := fun a n h => hF.readLE a n h
  have hacc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  have hhd : ∀ a ∈ xs, ∀ o, o + 8 ≤ 32 → S1.mem.readLE (a + o) 8 = s.mem.readLE (a + o) 8 := fun a ha o ho =>
    hrd _ _ ((hints a ha).2.1.of_sub (by omega) (by omega))
  unfold IntPre
  rw [hg, hfs]
  refine ⟨callEnv_shift hce0 hLs hF' hsp hg hfs hreg hk ha hf8, hsv,
    globals_win hgl hF (hgl.2.2.2.2.2.2.2.2.2.1) hsub, hB,
    Expmc.inv_frame hF (fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))) hinv, fun a ha => ?_, ?_⟩
  · obtain ⟨⟨hneg, hal, h48, hacc32, hheld, hlive, hlc, hnorm, harr, hc40⟩, hzw, harw, hzg, harg, hzf, harf⟩ :=
      hints a ha
    have q8 := hhd a ha 8 (by omega)
    have q16 := hhd a ha 16 (by omega)
    have q24 := hhd a ha 24 (by omega)
    have q0 : S1.mem.readLE a 1 = s.mem.readLE a 1 := hrd _ _ (hzw.of_sub (by omega) (by omega))
    unfold IntOK; rw [q8, q16, q24]
    refine ⟨⟨by rw [q0]; exact hneg, hal, h48, by rw [hacc]; exact hacc32, hheld,
      fun hc => by obtain ⟨n1, n2, n3, n4⟩ := hlive hc; exact ⟨n1, n2, by rw [hacc]; exact n3, n4⟩, hlc, ?_, harr,
      hc40⟩, hsub _ _ hzw, fun hc => hsub _ _ (harw hc), hzg, harg, hzf, harf⟩
    by_cases h0 : s.mem.readLE (a + 16) 8 = 0
    · exact Or.inl h0
    · right
      have hn := hnorm.resolve_left h0
      have hc : 0 < s.mem.readLE (a + 24) 8 := by omega
      rw [hrd _ _ ((harw hc).of_sub (by omega) (by omega))]; exact hn
  · refine hpw.imp_of_mem fun {a a'} ha ha' hp => ?_
    rw [hhd a ha 8 (by omega), hhd a ha 24 (by omega), hhd a' ha' 8 (by omega), hhd a' ha' 24 (by omega)]
    exact hp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`QRPre`** at `QuoRem`'s entry (`RSP = t - 168`, `q = t - 72`) from `Mod`'s precondition (`RSP = t`) -/
theorem qrPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA : Nat}
    (hIP : IntPre R b (ModBudget (max (lenW s.mem zA) (lenW s.mem yA))) L stk above [zA, yA] s)
    (hyv : 0 < IntV s.mem yA) (hlz : IntLenLe s.mem zA maxW) (hly : IntLenLe s.mem yA maxW)
    (hpool : PoolG R s.mem (win s stk above)) (hX : ModX s.mem zA)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true)
    {stkQ : Nat} (hstkQ : stkQ + 168 ≤ stk) (hab : 16 ≤ above)
    {SQ : State} (hsp : (SQ.regs 4).toNat = (s.regs 4).toNat - 168) (h14 : SQ.regs 14 = s.regs 14)
    (hfs : SQ.fsBase = s.fsBase) (hrg : SQ.mem.regions = s.mem.regions)
    (hF : MemFrame s.mem SQ.mem [((s.regs 4).toNat - 168, (s.regs 4).toNat - 160),
      ((s.regs 4).toNat - 88, (s.regs 4).toNat - 40), ((s.regs 4).toNat - 8, (s.regs 4).toNat),
      ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)])
    (q8 : SQ.mem.readLE ((s.regs 4).toNat - 72 + 8) 8 = 0) (q16 : SQ.mem.readLE ((s.regs 4).toNat - 72 + 16) 8 = 0)
    (q24 : SQ.mem.readLE ((s.regs 4).toNat - 72 + 24) 8 = 0) :
    QRPre R b L stkQ 128 ((s.regs 4).toNat - 72) zA yA SQ := by
  have hIP0 := hIP
  obtain ⟨⟨-, ⟨hst, -, -⟩, -, -, -, -, -, -, -⟩, -, -, -, -, hops, -⟩ := hIP0
  simp only [regSP] at hst
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  clear hops
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -⟩, hzw, -, -, -, -, -⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, -, hylc, -, -, -⟩, hyw, hyO, -, -, -, -⟩ := hoy
  have hFw : MemFrame s.mem SQ.mem (win s stk above) := hF.mono fun a k h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hrd : ∀ a n, Outside a n (win s stk above) → SQ.mem.readLE a n = s.mem.readLE a n := fun a n h => hFw.readLE a n h
  have hz : ∀ o, o + 8 ≤ 32 → SQ.mem.readLE (zA + o) 8 = s.mem.readLE (zA + o) 8 := fun o ho =>
    hrd _ _ (hzw.of_sub (by omega) (by omega))
  have hy : ∀ o, o + 8 ≤ 32 → SQ.mem.readLE (yA + o) 8 = s.mem.readLE (yA + o) 8 := fun o ho =>
    hrd _ _ (hyw.of_sub (by omega) (by omega))
  have hlen : lenW SQ.mem zA = lenW s.mem zA ∧ lenW SQ.mem yA = lenW s.mem yA := by
    simp only [lenW]; exact ⟨hz 16 (by omega), hy 16 (by omega)⟩
  have hsub : ∀ a n, Outside a n (win s stk above) → Outside a n (win SQ stkQ 128) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [hsp]; omega, q8, q16, q24, ?_⟩
  · rw [hlen.1, hlen.2]
    exact intPre_shift hIP hFw hsp h14 hfs hrg (by omega) (by omega) (by decide)
  · have e : IntV SQ.mem yA = IntV s.mem yA := by
      simp only [IntV]; rw [hy 8 (by omega), hy 16 (by omega)]
      refine natVal_frame' hFw fun h => ?_
      exact (hyO (by omega)).of_sub (Nat.le_refl _) (by omega)
    rw [e]; exact hyv
  · simp only [IntLenLe] at hlz ⊢; rw [hz 16 (by omega)]; exact hlz
  · simp only [IntLenLe] at hly ⊢; rw [hy 16 (by omega)]; exact hly
  · obtain ⟨h0, hrdp, hprt, hpw'⟩ := hpool
    exact ⟨h0, by rw [hrd _ _ hpw']; exact hrdp, hprt, hsub _ _ hpw'⟩
  · simp only [ModX] at hX ⊢; rw [hz 8 (by omega), hz 24 (by omega)]; exact hX
  · rw [hFw.accessible]; exact hadx

set_option maxRecDepth 20000 in
/-- a callee's `IntPost` (callee entry `sQ`, window inside the caller's, memory between `s` and `sQ` changed only in the
caller's window) is the caller's `IntPost` -/
theorem intPost_lift {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above stkQ aboveQ z v : Nat} {s sQ s' : State}
    (hP : IntPost R b B L stkQ aboveQ z v sQ s') (hF : MemFrame s.mem sQ.mem (win s stk above))
    (hLs : LiveSep L (win s stk above)) (hzw : Outside z 32 (win s stk above))
    (hsub : ∀ a n, Outside a n (win s stk above) → Outside a n (win sQ stkQ aboveQ))
    (h14 : sQ.regs 14 = s.regs 14) :
    IntPost R b B L stk above z v s s' := by
  obtain ⟨hv, L', b', hx, hb, hinv, hok, horf, hMF, hLF⟩ := hP
  have hz : ∀ o, o + 8 ≤ 32 → sQ.mem.readLE (z + o) 8 = s.mem.readLE (z + o) 8 := fun o ho =>
    hF.readLE _ _ (hzw.of_sub (by omega) (by omega))
  have harr : arrW sQ.mem z = arrW s.mem z := by simp only [arrW]; rw [hz 8 (by omega), hz 24 (by omega)]
  rw [harr] at hMF hLF
  refine ⟨hv, L', b', hx, hb, by rw [← h14]; exact hinv, hok, by rw [← hz 8 (by omega), ← hz 24 (by omega)]; exact horf,
    MemFrame.trans hF hMF fun a n h => ?_, LiveFrame.trans (LiveFrame.of_win hF hLs) hLF fun a n h => h⟩
  rw [outside_append, outside_append] at h ⊢
  exact ⟨h.1.2, ⟨h.1.1, hsub _ _ h.1.2⟩, h.2⟩

end FvModexp.Amd64.IMod
