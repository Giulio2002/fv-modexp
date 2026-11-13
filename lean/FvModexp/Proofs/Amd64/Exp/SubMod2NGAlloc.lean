import FvModexp.Proofs.Amd64.Exp.SubMod2NGC
import FvModexp.Proofs.Common.StackNatMath

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: the `growslice` of `z = append(z, 0)` (nat.go:1749) — budget, call
precondition, runtime facts after the call (pure lemmas; agent infra s48; twin of Arm64/Exp/SubMod2NGAlloc.lean)

`growslice(RAX = p, RBX = l + 1, RCX = c, RDI = 1, RSI = type:big.Word)` at `RSP_c = e - 136` (return address
`+0x326`) when `c = l < ⌈n/64⌉`; its block (`8 · growCap8 (l + 1) c`) is at most `gA n`, at most `W n` of them.
The call-precondition proof follows agent divmc's amd64 `StackNat.gcall_pre` (Amd64/Nat/StackNatCall.lean).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
  FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-- `type:big.Word` (growslice's element type; `LEAQ 0xf82df(IP), SI` at `+0x31a`) -/
abbrev wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

theorem wT_eq : wT = 7233184 := rfl

/-- A data object of the program is readable (copied from agent divmc's `StackNat.accessible_of_dataRead'`, itself
adapted from Janus v0.2.0 `Janus/Contracts/PanicWitnessAmd64.lean`). -/
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
/-- the `growslice` call's precondition at `RSP_c = e - 136` -/
theorem gcallG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R bb L s zp zc n k M L1 b1) {p l c : Nat} (hlv : NatLive M R L1 p c) (hcur : CurA R L zp zc p c)
    (hcl : c = l) (hlW : l + 1 ≤ W n) (hcost : 8 * growCap8 (l + 1) c ≤ b1)
    (T : State) (hm : T.mem = M) (hsp : (T.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : T.regs 14 = s.regs 14)
    (hra : T.mem.readLE (T.regs 4).toNat 8 < 2 ^ 47)
    (h0 : (T.regs 0).toNat = p) (h3 : (T.regs 3).toNat = l + 1) (h1 : (T.regs 1).toNat = c)
    (h7 : (T.regs 7).toNat = 1) (h6 : (T.regs 6).toNat = wT) :
    GrowslicePre64 4096 T ∧ StackRoom64 T 4096 5 ∧
      LiveAt R (cA "runtime.growslice") (growsliceArgs64 T) L1 b1 (growsliceRound64 T) (T.regs 14).toNat T.mem
        (liveWin64 T 4096 5) := by
  have hd := dlG_of hpre hrt
  have hce := cenvG_of hpre hrt hd
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrtw, hga, hgrt, hLs, -, -, -⟩ := hce
  have hsv := hpre.2.1
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have eg : (T.regs 14).toNat = (s.regs 14).toNat := by rw [h14]
  have hgr := growRoundG (N := l + 1) (c := c) (n := n) (by omega) hlW
  simp only [W] at hlW
  obtain ⟨-, -, -, -, -, hinv, -⟩ := hrt
  subst hm
  unfold Apart at hga
  have hwT : Apart wT 16 ((s.regs 4).toNat - 136 - 4440) (4440 + 80) := apart_of_data hd 1 (by decide) (by decide) hacc
  unfold Apart at hwT
  obtain ⟨ht1, ht2, ht3⟩ := wT_facts hd
  rw [wT_eq] at ht1 ht2 ht3 hwT h6
  refine ⟨⟨⟨⟨hra, by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hp => ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [h6]; exact ⟨by omega, ht3⟩
  · simp only [typSize, h6]; exact ht1
  · simp only [typPtrBytes, h6]; exact ht2
  · omega
  · omega
  · omega
  · omega
  · -- v0.3.1: the type descriptor (rodata) is outside the callee's window
    rw [h6]; simp only [calleeStack64, hsp, outside_cons, outside_nil, and_true]; omega
  · have e : (T.regs 3).toNat - (T.regs 7).toNat = c := by omega
    unfold GrowsliceOld64
    rw [e] at hp ⊢
    obtain ⟨-, -, a3, a4⟩ := hlv hp
    rw [h0]
    refine ⟨a4, Janus.Arm64.Memory.accessible_weaken _ a3, ?_⟩
    -- v0.3.1: the old array is outside the callee's window (it is z's, or fresh in the runtime ranges)
    have hw := (curA_win hpre hcur).1
    simp only [calleeStack64, hsp, outside_cons, outside_nil, and_true]; omega
  · rw [eg]; omega
  · rw [eg]; exact hg2
  · rw [eg, hsp]; omega
  · rw [eg]; simp only [calleeStack64, hsp, outside_cons, outside_nil, and_true]; omega
  · simp only [growsliceArgs64, h0, h3, h1, h7, h6]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega)
  · rw [eg]; exact hinv
  · simp only [growsliceRound64, h3, h1]; exact hcost
  · intro r hr
    have := hLs r hr
    simp only [liveWin64, calleeStack64, hsp, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro r hr
    simp only [liveWin64, calleeStack64, hsp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hrtw.of_sub (by simp only; omega) (by simp only; omega)

set_option maxRecDepth 20000 in
/-- the runtime facts after the `growslice` call (callee window inside `win`, new block fresh in `R.rt`, apart
from the live set), with the budget base `B'` -/
theorem rt_alloc {R : RtInv} {B B' : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M0 m : Memory}
    {L1 : List (Nat × Nat)} {b1 r : Nat} {ptr round : Nat} (hrt : Rt R B L s zp zc n k M0 L1 b1)
    (hs : 4576 ≤ (s.regs 4).toNat) (hreg : m.regions = M0.regions)
    (hMF : MemFrame M0 m (R.rt ++ [((s.regs 4).toNat - 136 - 4096, (s.regs 4).toNat - 136),
      ((s.regs 4).toNat - 136 + 8, (s.regs 4).toNat - 136 + 8 + 8 * 5)]))
    (hLF : LiveFrame M0 m L1 []) (hin : InRanges ptr round R.rt) (hap : ApartAll ptr round L1)
    (hb : B' - k * wCost n ≤ b1 - r)
    (hinv : R.inv (b1 - r) (L1 ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L1 ++ [(ptr, ptr + round)]) m)) :
    Rt R B' L s zp zc n k m (L1 ++ [(ptr, ptr + round)]) (b1 - r) := by
  obtain ⟨hreg0, hF0, hLF0, hLE0, -, -, hlv⟩ := hrt
  refine ⟨hreg.trans hreg0, hF0.trans hMF fun a q h => ?_, hLF0.trans (LiveFrame.of_nil' hLF _)
    fun a q h => hLE0.inRanges_old h, hLE0.trans (LiveExt.single (by simpa using hin) (by simpa using hap)), hb, hinv,
    fun hc => ?_⟩
  · simp only [outside_append, win, K, A, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h, h.1.1, by omega, by omega⟩
  · obtain ⟨c1, c2, c3, c4⟩ := hlv hc
    exact ⟨c1, (LiveExt.single (by simpa using hin) (by simpa using hap)).held c2, by rw [hMF.accessible]; exact c3, c4⟩

/-- the frame words survive the `growslice` call -/
theorem fw_alloc {s : State} {M m : Memory} {rt : List (Nat × Nat)} {zp zl zc yp n : Nat}
    (hs : 4576 ≤ (s.regs 4).toNat) (hout : Outside ((s.regs 4).toNat - 4576) (4576 + 88) rt)
    (h : Fw s M zp zl zc yp n)
    (hMF : MemFrame M m (rt ++ [((s.regs 4).toNat - 136 - 4096, (s.regs 4).toNat - 136),
      ((s.regs 4).toNat - 136 + 8, (s.regs 4).toNat - 136 + 8 + 8 * 5)])) : Fw s m zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (s.regs 4).toNat - 8 ≤ a → a + 8 ≤ (s.regs 4).toNat + 88 → m.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hMF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  exact ⟨(r _ (by omega) (by omega)).trans f1, (r _ (by omega) (by omega)).trans f2,
    (r _ (by omega) (by omega)).trans f3, (r _ (by omega) (by omega)).trans f4,
    (r _ (by omega) (by omega)).trans f5, (r _ (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega)).trans f7⟩

/-- a store into the current array (outside the function's window) keeps the frame words -/
theorem fw_cstore {s : State} {M : Memory} {zp zl zc yp n : Nat} (h : Fw s M zp zl zc yp n) {a v : Nat}
    (hw : a + 8 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ a) (hs : 4576 ≤ (s.regs 4).toNat) :
    Fw s (M.writeLE a 8 v) zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ b, (s.regs 4).toNat - 8 ≤ b → b + 8 ≤ (s.regs 4).toNat + 88 →
      (M.writeLE a 8 v).readLE b 8 = M.readLE b 8 :=
    fun b h1 h2 => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  exact ⟨(r _ (by omega) (by omega)).trans f1, (r _ (by omega) (by omega)).trans f2, (r _ (by omega) (by omega)).trans f3,
    (r _ (by omega) (by omega)).trans f4, (r _ (by omega) (by omega)).trans f5, (r _ (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega)).trans f7⟩

theorem readLE_shift {m m' : Memory} : ∀ (n a a' : Nat), (∀ i, i < n → m.bytes (a + i) = m'.bytes (a' + i)) →
    m.readLE a n = m'.readLE a' n
  | 0, _, _, _ => rfl
  | n + 1, a, a', h => by
    simp only [Janus.Arm64.Memory.readLE]
    rw [show a = a + 0 from rfl, show a' = a' + 0 from rfl, h 0 (by omega),
      readLE_shift n (a + 0 + 1) (a' + 0 + 1) (fun i hi => by
        have := h (i + 1) (by omega); rwa [show a + 0 + 1 + i = a + (i + 1) by omega,
          show a' + 0 + 1 + i = a' + (i + 1) by omega])]

/-- the copied value: the first `l` words of the new block are the old array's -/
theorem natVal_copy {M m : Memory} {p ptr l : Nat}
    (h : ∀ i, i < 8 * l → m.bytes (ptr + i) = M.bytes (p + i)) : natVal m ptr l = natVal M p l := by
  unfold natVal
  exact readLE_shift _ _ _ h

end FvModexp.Amd64.SubMod2N
