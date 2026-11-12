import FvModexp.Proofs.Amd64.Top.RunC2Lem2

/-!
# `Run` (amd64): `IntPre` survives the `CALL`'s return-address push

On amd64 a callee's entry memory is the caller's memory with the return address pushed at the callee's `RSP`, inside the
callee window. `IntPre` only reads outside the window (the `*Int` headers and arrays, the guard / TLS words, the
threshold globals), so it moves from the memory before the push (where `Mod`/`exp` returned) to the one after.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

open RunIface in
theorem intPre_move {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {xs : List Nat} {t t' : State}
    (h : IntPre R b B L stk above xs t)
    (h4 : t'.regs 4 = t.regs 4) (h14 : t'.regs 14 = t.regs 14) (hfs : t'.fsBase = t.fsBase)
    (hrd : ∀ a n, Outside a n (win t stk above) → t'.mem.readLE a n = t.mem.readLE a n)
    (hacc : ∀ a n w, t'.mem.accessible a n w = t.mem.accessible a n w)
    (hd : Extracted.program.DataLoaded t'.mem)
    (hinv : R.inv b L (t.regs 14).toNat (view R.rt L t'.mem)) : IntPre R b B L stk above xs t' := by
  obtain ⟨hce, hsv, hgl, hB, -, hints, hpw⟩ := h
  have hce0 := hce
  obtain ⟨-, -, -, -, -, hga, -, -, -, ⟨-, -, hfw⟩⟩ := hce
  have hgo : Outside ((t.regs 14).toNat + 16) 8 (win t stk above) := by
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; unfold Apart at hga; omega
  have hfo : Outside (t.fsBase.toNat - 8) 8 (win t stk above) := by
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; unfold Apart at hfw; omega
  have hce' := callEnv_frame hce0 h4 h14 hfs hacc (hrd _ _ hgo) (hrd _ _ hfo) hd (LiveExt.refl R L)
  obtain ⟨e0, e1, e2, e3, a1, a2, a3, hgacc, hrt, hwg, hwbA, hwbR, hwbW⟩ := hgl
  have hG : ∀ k, k + 8 ≤ 32 → t'.mem.readLE (gA + k) 8 = t.mem.readLE (gA + k) 8 := fun k hk =>
    hrd _ _ (hwg.of_sub (by omega) (by omega))
  have hW : win t' stk above = win t stk above := by simp only [win, h4]
  -- per object: the header reads are unchanged
  have hhd : ∀ a ∈ xs, ∀ o, o + 8 ≤ 32 → t'.mem.readLE (a + o) 8 = t.mem.readLE (a + o) 8 := fun a ha o ho =>
    hrd _ _ ((hints a ha).2.1.of_sub (by omega) (by omega))
  unfold IntPre
  rw [h14, hfs, hW]
  refine ⟨hce', hsv, ⟨?g1, ?g2, ?g3, ?g4, a1, a2, a3, by rw [hacc]; exact hgacc, hrt, hwg, by rw [hacc]; exact hwbA,
    hwbR, hwbW⟩, hB, hinv, fun a ha => ?_, ?_⟩
  case g1 => rw [a1, hG 8 (by omega), ← a1]; exact e0
  case g2 => rw [a2, hG 16 (by omega), ← a2]; exact e1
  case g3 => rw [a3, hG 24 (by omega), ← a3]; exact e2
  case g4 => exact (hG 0 (by omega)).trans e3
  · obtain ⟨⟨hneg, hal, h48, hacc32, hheld, hlive, hlc, hnorm, harr⟩, hzw, harw, hzg, harg, hzf, harf⟩ := hints a ha
    have q8 := hhd a ha 8 (by omega)
    have q16 := hhd a ha 16 (by omega)
    have q24 := hhd a ha 24 (by omega)
    have q0 : t'.mem.readLE a 1 = t.mem.readLE a 1 := hrd _ _ (hzw.of_sub (by omega) (by omega))
    unfold IntOK; rw [q8, q16, q24]
    refine ⟨⟨by rw [q0]; exact hneg, hal, h48, by rw [hacc]; exact hacc32, hheld,
      fun hc => by obtain ⟨n1, n2, n3, n4⟩ := hlive hc; exact ⟨n1, n2, by rw [hacc]; exact n3, n4⟩, hlc, ?_, harr⟩,
      hzw, harw, hzg, harg, hzf, harf⟩
    by_cases h0 : t.mem.readLE (a + 16) 8 = 0
    · exact Or.inl h0
    · right
      have hn := hnorm.resolve_left h0
      have hc : 0 < t.mem.readLE (a + 24) 8 := by omega
      rw [hrd _ _ ((harw hc).of_sub (by omega) (by omega))]; exact hn
  · refine hpw.imp_of_mem fun {a a'} ha ha' hp => ?_
    rw [hhd a ha 8 (by omega), hhd a ha 24 (by omega), hhd a' ha' 8 (by omega), hhd a' ha' 24 (by omega)]
    exact hp

open RunIface in
/-- `IntPre` at the callee entry after the `CALL` pushed `v` at `RSP` (inside the callee window, `above ≥ 8`). -/
theorem intPre_push {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {xs : List Nat} {t t' : State}
    (h : IntPre R b B L stk above xs t) (ha8 : 8 ≤ above) (v : Nat)
    (h4 : t'.regs 4 = t.regs 4) (h14 : t'.regs 14 = t.regs 14) (hfs : t'.fsBase = t.fsBase)
    (hm : t'.mem = t.mem.writeLE (t.regs 4).toNat 8 v) : IntPre R b B L stk above xs t' := by
  have h0 := h
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, hd, hout, -, -, -, hro, -⟩, -, -, -, hinv, -, -⟩ := h
  simp only [regSP] at hb' ha hw hout
  have ho : Outside (t.regs 4).toNat 8 R.rt := hout.of_sub (by omega) (by omega)
  have hMF : MemFrame t.mem t'.mem (R.rt ++ win t stk above) := by
    rw [hm]; simp only [win]; janus_frame
  refine intPre_move h0 h4 h14 hfs (fun a n hh => ?_) (fun a n w => by rw [hm]; simp)
    (dataLoaded_frame64 hd (by rw [hm]; simp) hro hMF fun r hr _ => ?_) (by rw [hm, view_writeLE_out ho]; exact hinv)
  · rw [hm]
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hh
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by dsimp only; omega)

end FvModexp.Amd64.Run
