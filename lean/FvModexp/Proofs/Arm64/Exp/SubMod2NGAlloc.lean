import FvModexp.Proofs.Arm64.Exp.SubMod2NGC
import FvModexp.Proofs.Common.StackNatMath

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: the `growslice` of `z = append(z, 0)` (nat.go:1749) — budget, call
precondition, runtime facts after the call (pure lemmas; agent infra)

`growslice(R0 = p, R1 = l + 1, R2 = c, R3 = 1, R4 = type:big.Word)` at `SP' = SP - 144` when `c = l < ⌈n/64⌉`; its block
(`8 · growCap8 (l + 1) c`) is at most `gA n`, at most `W n` of them (`bud_grow`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-- `type:big.Word` (growslice's element type; `ADRP 835584 + 3264` at `+0x278`) -/
abbrev wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

theorem wT_eq : wT = 2641088 := rfl

theorem wT_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE wT 8 = 8 ∧ m.readLE (wT + 8) 8 = 0 ∧ m.accessible wT 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

/-- one growth's block fits `gA n` -/
theorem growRoundG {N c n : Nat} (hc : c < N) (hN : N ≤ W n) : 8 * growCap8 N c ≤ gA n := by
  unfold growCap8 gA allocCost
  have h1 := roundupsize_le (nextslicecap N c * 8) true
  have h2 := nextslicecap_le2 _ _ hc
  omega

theorem growCapG_lt {N c n : Nat} (hc : c < N) (hN : N ≤ W n) (hn : n ≤ 2 ^ 15) : growCap8 N c < 2 ^ 40 := by
  have := growRoundG hc hN
  unfold gA allocCost W at this; omega

/-- the budget of one growth (`g + 1 ≤ W n` growths in all) -/
theorem bud_grow {b g n b3 r : Nat} (hcG : costG n ≤ b) (hg1 : g + 1 ≤ W n)
    (hb : b - g * gA n - 3 * wCost n ≤ b3) (hr : r ≤ gA n) :
    r ≤ b3 ∧ b - (g + 1) * gA n - 3 * wCost n ≤ b3 - r := by
  have h1 : (g + 1) * gA n ≤ W n * gA n := Nat.mul_le_mul_right _ hg1
  rw [Nat.add_mul, Nat.one_mul] at h1 ⊢
  simp only [costG, cost] at hcG
  constructor <;> omega

set_option maxRecDepth 20000 in
/-- the `growslice` call's precondition at `SP' = SP - 144` -/
theorem gcallG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R bb L s zp zc n k M L1 b1) {p l c : Nat} (hlv : NatLive M R L1 p c) (hcl : c = l)
    (hlW : l + 1 ≤ W n) (hcost : 8 * growCap8 (l + 1) c ≤ b1)
    (T : State) (hm : T.mem = M) (hsp : T.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : T.regs 28 = s.regs 28)
    (h0 : (T.regs 0).toNat = p) (h1 : (T.regs 1).toNat = l + 1) (h2 : (T.regs 2).toNat = c)
    (h3 : (T.regs 3).toNat = 1) (h4 : (T.regs 4).toNat = wT) (h30 : T.regs 30 = BitVec.ofNat 64 1806228) :
    GrowslicePre 4096 T ∧ StackRoom T 4096 5 ∧
      LiveAt R (cA "runtime.growslice") (growsliceArgs T) L1 b1 (growsliceRound T) (T.regs 28).toNat T.mem
        (calleeStack T 4096 5) := by
  have hd := dlG_of hpre hrt
  have hce := cenvG_of hpre hrt hd
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrtw, hga, hgrt, hLs, -, -⟩ := hce
  have hsv := hpre.2.1
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have esp : T.sp.toNat = s.sp.toNat - 144 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (T.regs 28).toNat = (s.regs 28).toNat := by rw [h28]
  have hround : growsliceRound T = 8 * growCap8 (l + 1) c := by simp only [growsliceRound, h1, h2]
  have hgr := growRoundG (N := l + 1) (c := c) (n := n) (by omega) hlW
  simp only [W] at hlW
  obtain ⟨-, -, -, -, -, hinv, -⟩ := hrt
  subst hm
  unfold Apart at hga
  have hwT : Apart wT 16 (s.sp.toNat - 144 - 4464) (4464 + 88) := apart_of_data hd 1 (by decide) (by decide) hacc
  rw [wT_eq] at hwT h4
  obtain ⟨ht1, ht2, ht3⟩ := wT_facts hd
  rw [wT_eq] at ht1 ht2 ht3
  unfold Apart at hwT
  have hc := call_pre R L1 b1 (growsliceRound T) (cA "runtime.growslice") (growsliceArgs T) (s := T) (S := T)
    (lo := s.sp.toNat - 144 - 4464) (hi := s.sp.toNat - 144 + 88) (stack := 4096) (nargs := 5) (fr := 0)
    (by rw [eg]; exact hg1) (by rw [eg]; exact hg2) (by rw [eg, esp]; omega)
    (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl (by omega)
    (by rw [esp]; exact hal) (by rw [h30]; decide) (by rw [h30]; decide) (by decide) (by omega) (by omega) (by omega)
    (by omega) (by rw [show s.sp.toNat - 144 + 88 - (s.sp.toNat - 144 - 4464) = 4464 + 88 by omega]; exact hacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show s.sp.toNat - 144 + 88 - (s.sp.toNat - 144 - 4464) = 4464 + 88 by omega]; exact hrtw) hLs
    (by simp only [growsliceArgs, h0, h1, h2, h3, h4]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega))
    (by rw [eg]; exact hinv) (by rw [hround]; exact hcost)
  refine ⟨⟨⟨hc.1, ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩, fun hp => ?_⟩, hc.2⟩
  · rw [h4]; exact ⟨by omega, ht3⟩
  · simp only [typSize, h4]; exact ht1
  · simp only [typPtrBytes, h4]; exact ht2
  · have e : (T.regs 1).toNat - (T.regs 3).toNat = c := by omega
    unfold GrowsliceOld
    rw [e] at hp ⊢
    obtain ⟨-, -, a3, a4⟩ := hlv hp
    rw [h0]
    exact ⟨a4, Memory.accessible_weaken _ a3⟩

set_option maxRecDepth 20000 in
/-- the runtime facts after the `growslice` call (callee window inside `winA`, new block fresh in `R.rt`, apart
from the live set), with the budget base `B'` -/
theorem rt_alloc {R : RtInv} {B B' : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M0 m : Memory}
    {L1 : List (Nat × Nat)} {b1 r : Nat} {ptr round : Nat} (hrt : Rt R B L s zp zc n k M0 L1 b1)
    (hal : 4608 ≤ s.sp.toNat) (hreg : m.regions = M0.regions)
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 8 * 5)]))
    (hLF : LiveFrame M0 m L1 []) (hin : InRanges ptr round R.rt) (hap : ApartAll ptr round L1)
    (hb : B' - k * wCost n ≤ b1 - r)
    (hinv : R.inv (b1 - r) (L1 ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L1 ++ [(ptr, ptr + round)]) m)) :
    Rt R B' L s zp zc n k m (L1 ++ [(ptr, ptr + round)]) (b1 - r) := by
  obtain ⟨hreg0, hF0, hLF0, hLE0, -, -, hlv⟩ := hrt
  refine ⟨hreg.trans hreg0, hF0.trans hMF fun a q h => ?_, hLF0.trans (LiveFrame.of_nil' hLF _)
    fun a q h => hLE0.inRanges_old h, hLE0.trans (LiveExt.single (by simpa using hin) (by simpa using hap)), hb, hinv,
    fun hc => ?_⟩
  · simp only [outside_append, winA, K, A, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h, h.1.1, by omega, by omega⟩
  · obtain ⟨c1, c2, c3, c4⟩ := hlv hc
    exact ⟨c1, (LiveExt.single (by simpa using hin) (by simpa using hap)).held c2, by rw [hMF.accessible]; exact c3, c4⟩

/-- the frame words survive the `growslice` call -/
theorem fw_alloc {s : State} {M m : Memory} {rt : List (Nat × Nat)} {zp zl zc yp n : Nat} (hs : 4608 ≤ s.sp.toNat)
    (hout : Outside (s.sp.toNat - 4608) (4608 + 88) rt) (h : Fw s M zp zl zc yp n)
    (hMF : MemFrame M m (rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 8 * 5)])) : Fw s m zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 88 → (a + 8 ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 96 ≤ a) →
      m.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    refine hMF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  exact ⟨(r _ (by omega) (by omega) (by omega)).trans f1, (r _ (by omega) (by omega) (by omega)).trans f2,
    (r _ (by omega) (by omega) (by omega)).trans f3, (r _ (by omega) (by omega) (by omega)).trans f4,
    (r _ (by omega) (by omega) (by omega)).trans f5, (r _ (by omega) (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega) (by omega)).trans f7⟩

/-- a store into a fresh array (outside the function's window) keeps the frame words -/
theorem fw_fstore {s : State} {M : Memory} {zp zl zc yp n : Nat} (h : Fw s M zp zl zc yp n) {a v : Nat}
    (hw : a + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ a) (hs : 4608 ≤ s.sp.toNat) :
    Fw s (M.writeLE a 8 v) zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ b, s.sp.toNat - 152 ≤ b → b + 8 ≤ s.sp.toNat + 88 → (M.writeLE a 8 v).readLE b 8 = M.readLE b 8 :=
    fun b h1 h2 => Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  exact ⟨(r _ (by omega) (by omega)).trans f1, (r _ (by omega) (by omega)).trans f2, (r _ (by omega) (by omega)).trans f3,
    (r _ (by omega) (by omega)).trans f4, (r _ (by omega) (by omega)).trans f5, (r _ (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega)).trans f7⟩

theorem readLE_shift {m m' : Memory} : ∀ (n a a' : Nat), (∀ i, i < n → m.bytes (a + i) = m'.bytes (a' + i)) →
    m.readLE a n = m'.readLE a' n
  | 0, _, _, _ => rfl
  | n + 1, a, a', h => by
    simp only [Memory.readLE]
    rw [show a = a + 0 from rfl, show a' = a' + 0 from rfl, h 0 (by omega),
      readLE_shift n (a + 0 + 1) (a' + 0 + 1) (fun i hi => by
        have := h (i + 1) (by omega); rwa [show a + 0 + 1 + i = a + (i + 1) by omega,
          show a' + 0 + 1 + i = a' + (i + 1) by omega])]

/-- the copied value: the first `l` words of the new block are the old array's -/
theorem natVal_copy {M m : Memory} {p ptr l : Nat}
    (h : ∀ i, i < 8 * l → m.bytes (ptr + i) = M.bytes (p + i)) : natVal m ptr l = natVal M p l := by
  unfold natVal
  exact readLE_shift _ _ _ h

end FvModexp.Arm64.SubMod2N
