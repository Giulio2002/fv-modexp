import FvModexp.Proofs.Amd64.Exp.ModInvSeg2
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the allocating `z.make(numWords + 1)` (nat.go:68) (agent infra s54;
twin of `Arm64/Exp/ModInvAlloc`)

From `JA` (`+0x154`): the spills `0x88(SP) = numWords + 1` (`RSP - 88`), `0x60(SP) = numWords + 5` (`RSP - 128`),
`makeslice(Word, numWords + 1, numWords + 5)` (CALL at `+0x16f`, callee `RSP = RSP_entry - 232`), the reloads, up to
`JM` (`+0x1b6`). `zalloc` hands the raw facts (`AllocPost`) to a continuation; `ModInvRt` turns them into `JM`'s.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-- the facts after the allocating `make` (`M` = memory at `JA`, `sp` = the entry `RSP`) -/
@[reducible] def AllocPost (R : RtInv) (L : List (Nat × Nat)) (b g sp nw : Nat) (M m : Memory) (p r : Nat) : Prop :=
  MemFrame M m (R.rt ++ [(sp - 232 - 4096, sp - 200), (sp - 128, sp - 120), (sp - 88, sp - 80)]) ∧
  LiveFrame M m L [] ∧ m.regions = M.regions ∧ InRanges p r R.rt ∧ ApartAll p r L ∧ p + r ≤ 2 ^ 48 ∧
  m.accessible p (8 * (nw + 5)) true = true ∧ p % 8 = 0 ∧ 8 * (nw + 5) ≤ r ∧ r ≤ makeCost (nw + 1) ∧
  R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem zalloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4096 ≤ kc)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x154))
    (h4 : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224)) (h5 : S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (hab : Abi s S) (h2 : S.regs 2 = BitVec.ofNat 64 (NW n + 1)) (h3 : S.regs 3 = BitVec.ofNat 64 (NW n))
    (hF : MemFrame s.mem S.mem (win s (K kc) A)) (Q : State → Prop)
    (KZ : ∀ (S' : State) (m : Memory) (p r : Nat),
      S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x1b6) → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → Abi s S' →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 1 = BitVec.ofNat 64 (NW n + 5) → S'.regs 2 = BitVec.ofNat 64 (NW n + 1) →
      S'.regs 3 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 120) 8) →
      S'.regs 6 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 264) 8) →
      S'.regs 7 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 256) 8) →
      S'.regs 8 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 272) 8) →
      S'.regs 9 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 280) 8) →
      S'.regs 10 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 288) 8) →
      S'.regs 12 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 144) 8) → S'.mem = m →
      AllocPost R L (b + stkR H s.mem st) (s.regs 14).toNat (s.regs 4).toNat (NW n) S.mem m p r →
      ReachesRet (LibW.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S Q := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgrt, hLs, -, -⟩, hsv, -, hn1, hn2, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, ⟨-, hcost⟩, hinv, hty, -, -, hra⟩ := hpre'
  obtain ⟨a14, afs, ax15, adf⟩ := hab
  simp only [stackguard0, stackguard0Offset, regG, regSP, K, A] at hg1 hg2 hg3 hb' ha hw hga hgrt hout
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, NW n + 1, NW n + 5] := hsv.1 _ _ _ (by simp only [NW]; omega)
  have hmc : makeCost (NW n + 1) = allocCost (8 * (NW n + 5)) := by
    unfold makeCost makeCap; rw [if_neg (show ¬ (NW n + 1 = 1) by simp only [NW]; omega)]
  have hbl := blockSize_le_allocCost (8 * (NW n + 5)) true
  have hcb : makeCost (NW n + 1) ≤ b := by simp only [cost] at hcost; omega
  have hbs : blockSize (8 * (NW n + 5)) true ≤ b + stkR H s.mem st := by omega
  have hwt : Apart NatAdd.wordT 16 ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) :=
    apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  obtain ⟨_hwa, _hws, _hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt
  have hinvS : R.inv (b + stkR H s.mem st) L (s.regs 14).toNat (view R.rt L S.mem) :=
    Expmc.inv_frame hF (fun r hr => Or.inr (by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      dsimp only
      simp only [K, A]; exact hout.of_sub (by omega) (by omega))) hinv
  have hLs0 : LiveSep L [((s.regs 4).toNat - (232 + kc), (s.regs 4).toNat + 72)] := hLs
  simp only [LiveSep, win] at hLs
  have hLs' : ∀ r ∈ L, Outside r.1 (r.2 - r.1)
      ([((s.regs 4).toNat - 224 - 8 - 4096, (s.regs 4).toNat - 224 - 8),
        ((s.regs 4).toNat - 224 - 8 + 8, (s.regs 4).toNat - 224 - 8 + 8 + 24)] ++
        [((s.regs 4).toNat - 224 - 8, (s.regs 4).toNat - 224 - 8 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [K, A, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hwin : ∀ a k, a + k ≤ (s.regs 4).toNat - (232 + kc) ∨ (s.regs 4).toNat + 72 ≤ a →
      S.mem.readLE a k = s.mem.readLE a k := fun a k h =>
    hF.readLE _ _ (by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega)
  have t8 : S.mem.readLE 7233184 8 = 8 := by rw [hwin _ _ (by omega)]; exact _hws
  have t0 : S.mem.readLE 7233192 8 = 0 := by rw [hwin _ _ (by omega)]; exact _hwp
  have tg : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hwin _ _ (by omega)
  clear hinv hcost hsv hLs hpre
  have m1 : NW n % 18446744073709551616 = NW n := Nat.mod_eq_of_lt (by simp only [NW]; omega)
  have m2 : (NW n + 1) % 18446744073709551616 = NW n + 1 := Nat.mod_eq_of_lt (by simp only [NW]; omega)
  have m3 : (NW n + 5) % 18446744073709551616 = NW n + 5 := Nat.mod_eq_of_lt (by simp only [NW]; omega)
  have m4 : NW n + 5 < 9223372036854775808 := by simp only [NW]; omega
  have m5 : 8 * (NW n + 5) ≤ 281474976710656 := by simp only [NW]; omega
  janus64_run [BitVec.msb_eq_decide, t8, t0, tg, m1, m2, m3] until [0x5ea8c0 + 0x1b6] calls [hmk.pos L (b + stkR H s.mem st)]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv'
  have hsz : 8 * (NW n + 5) ≤ blockSize (8 * (NW n + 5)) true := by
    exact Janus.Contracts.AllocSat.le_blockSize _ _
  refine KZ _ m ptr.toNat (blockSize (8 * (NW n + 5)) true) ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    ⟨?mf, ?lf, hrg1, hIn, hAp, hle, ?acc, h8 (Or.inr (by omega)), hsz, by omega, hinv'⟩
  case mf =>
    have hw1 : MemFrame S.mem (((S.mem.writeLE ((s.regs 4).toNat - 224 + 136) 8 (NW n + 1)).writeLE
        ((s.regs 4).toNat - 224 + 96) 8 (NW n + 5)).writeLE ((s.regs 4).toNat - 224 - 8) 8 6203956)
        [((s.regs 4).toNat - 88, (s.regs 4).toNat - 80), ((s.regs 4).toNat - 128, (s.regs 4).toNat - 120),
          ((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)] :=
      (((MemFrame.refl S.mem _).writeLE_inRanges _ ⟨((s.regs 4).toNat - 88, (s.regs 4).toNat - 80), by simp,
        by simp only; omega, by simp only; omega⟩).writeLE_inRanges _ ⟨((s.regs 4).toNat - 128, (s.regs 4).toNat - 120),
        by simp, by simp only; omega, by simp only; omega⟩).writeLE_inRanges _ ⟨((s.regs 4).toNat - 232,
        (s.regs 4).toNat - 224), by simp, by simp only; omega, by simp only; omega⟩
    refine hw1.trans hMF (fun a k ho => ⟨?_, ?_⟩)
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
  case lf =>
    have hLw : LiveFrame S.mem (((S.mem.writeLE ((s.regs 4).toNat - 224 + 136) 8 (NW n + 1)).writeLE
        ((s.regs 4).toNat - 224 + 96) 8 (NW n + 5)).writeLE ((s.regs 4).toNat - 224 - 8) 8 6203956) L [] :=
      (((LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))
    exact hLw.trans hLF (fun _ _ h => h)
  case acc =>
    rw [hMF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hF.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  all_goals janus64_simp
  all_goals first | exact afs | exact a14 | exact ax15 | exact adf

end FvModexp.Amd64.ModInv
