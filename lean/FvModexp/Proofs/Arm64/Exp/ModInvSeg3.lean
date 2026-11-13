import FvModexp.Proofs.Arm64.Exp.ModInvRt
import FvModexp.Proofs.Common.ModInvRound

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the Hensel loop head `J2` (agent infra)

`J2` (`+0x3c0` = `0x1b6fb0`, nat.go:1325 `i < numWords` test, before the stores of `z` to `SP+192/184/224`):
`X0 = i = 2^j`, `z = (X14, X1, X2)` (`p, l, c`), `zz = (X13, X12, X11)` (`q, ql, qc`), `X3 … X9 = stk, x, n, n + 63,
numWords`. Invariant: `X · Z ≡ 1 (mod 2^(2^j · 32))` (`Exp.round_inv`; at `j = 1` from `Z mod 2^64 = k0`), both
arrays owned (caller's `z` or fresh), apart; `cap z ≥ numWords + 1`; budget after the two
`make`s and `j - 1` rounds.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- the saved LR / FP and the spills the loop reloads (`stk`, `x`, `n`, `n + 63`, `numWords`) -/
@[reducible] def Fw2 (s : State) (M : Memory) (st xp xl xc n : Nat) : Prop :=
  Fw0 s M ∧ M.readLE (s.sp.toNat + 32) 8 = st ∧ M.readLE (s.sp.toNat + 40) 8 = xp ∧
    M.readLE (s.sp.toNat + 48) 8 = xl ∧ M.readLE (s.sp.toNat + 56) 8 = xc ∧ M.readLE (s.sp.toNat + 64) 8 = n ∧
    M.readLE (s.sp.toNat - 40) 8 = n + 63 ∧ M.readLE (s.sp.toNat - 112) 8 = NW n

/-- the budget spent before round `j` -/
@[reducible] def spent (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j : Nat) : Nat :=
  makeCost (NW n + 1) + makeCost (2 * NW n) + sumR sqrC mulC xl n (j - 1)

/-- **J2** at round `j`: the loop head (see the module doc) -/
def J2j (impl : List Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (j : Nat) : Prop :=
  ∀ (S : State) (p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n →
    S.pc = BitVec.ofNat 64 1798064 → S.sp = BitVec.ofNat 64 (s.sp.toNat - 240) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 (2 ^ j) → S.regs 1 = BitVec.ofNat 64 l → S.regs 2 = BitVec.ofNat 64 c →
    S.regs 14 = BitVec.ofNat 64 p → S.regs 11 = BitVec.ofNat 64 qc → S.regs 12 = BitVec.ofNat 64 ql →
    S.regs 13 = BitVec.ofNat 64 q →
    S.regs 3 = BitVec.ofNat 64 st → S.regs 4 = BitVec.ofNat 64 xp → S.regs 5 = BitVec.ofNat 64 xl →
    S.regs 6 = BitVec.ofNat 64 xc → S.regs 7 = BitVec.ofNat 64 n → S.regs 8 = BitVec.ofNat 64 (n + 63) →
    S.regs 9 = BitVec.ofNat 64 (NW n) →
    Fw2 s S.mem st xp xl xc n → RtM R kc L s zp zc st S.mem L1 b1 → b - spent sqrC mulC xl n j + stkR H S.mem st ≤ b1 →
    Own R kc L L1 s zp zc st xp xl S.mem p c → Own R kc L L1 s zp zc st xp xl S.mem q qc →
    NW n + 1 ≤ c → l ≤ zB n j → l ≤ c → ql ≤ qc → 0 < qc → 1 ≤ j → 2 ^ (j - 1) < NW n →
    Apart p (8 * c) q (8 * qc) →
    natVal s.mem xp xl * natVal S.mem p l % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32) →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- **J2**: the loop head at every round -/
def J2 (impl : List Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ j, J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s j

/-- a frame read byte by byte (an empty range in the frame never matters for a single byte) -/
theorem frame_bytes {m m' : Memory} {rs : List (Nat × Nat)} (hF : MemFrame m m' rs) {a n : Nat}
    (h : ∀ i, i < n → Outside (a + i) 1 rs) : m'.readLE a n = m.readLE a n := by
  apply Memory.readLE_congr
  intro i hi
  have := hF.readLE (a + i) 1 (h i hi)
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

set_option maxRecDepth 20000 in
/-- the frame environment at any memory the runtime facts describe -/
theorem env_rt {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) : Env R L1 (s.regs 28).toNat (s.sp.toNat - 240) kc M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, hLs, -⟩, -, -, -, -, -, -, hzc0,
    ⟨-, -, hzw⟩, -, -, -, -, -, -, -, -, ⟨⟨-, -, -, -, -, hlc, -⟩, -, hstg, hsta⟩, -⟩ := hpre
  obtain ⟨-, hF, -, hLE, -, -, -, -⟩ := hrt
  obtain ⟨-, hzg⟩ := hzw hzc0
  simp only [K, A] at hw hout hb' ha hga hg3 hLs
  unfold Apart at hga hzg hstg
  have hgr : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine frame_bytes hF fun i hi => ?_
    simp only [outside_append, ExpHyp.stWs, stkWs, winA, K, A, outside_cons, outside_nil, and_true]
    refine ⟨⟨⟨(hgrt.of_sub (by omega) (by omega)), by omega, by omega⟩, by omega⟩, by omega, ?_⟩
    rcases Nat.lt_or_ge (stLen s.mem st) (stCap s.mem st) with h | h
    · have := (hsta (by omega)).2; unfold Apart at this; omega
    · omega
  refine ⟨by omega, by omega, by omega, ?_, hg1, by rw [hF.accessible]; exact hg2, by rw [hgr]; omega, ?_, ?_, hgrt, ?_⟩
  · rw [hF.accessible]; rw [show s.sp.toNat - 240 - kc = s.sp.toNat - (240 + kc) by omega,
      show kc + 312 = 240 + kc + 72 by omega]; exact hw
  · rw [show s.sp.toNat - 240 - kc = s.sp.toNat - (240 + kc) by omega, show kc + 312 = 240 + kc + 72 by omega]
    exact hout
  · unfold Apart; omega
  · refine hLE.liveSep (fun q hq => ?_) (fun r hr => ?_)
    · have := hLs q hq
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [show s.sp.toNat - 240 - kc = s.sp.toNat - (240 + kc) by omega]
      exact hout.of_sub (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- stack-slot stores (inside `winA`) keep the runtime facts -/
theorem rtM_stk {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) (hF : MemFrame M M' (winA s (K kc) A)) (hreg : M'.regions = M.regions) :
    RtM R kc L s zp zc st M' L1 b1 := by
  have he := env_rt hpre hrt
  obtain ⟨⟨-, ⟨-, hal, -, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, hstw, -, -⟩, -⟩ := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hLs1⟩ := he
  simp only [K, A] at hal hout hstw
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hrt
  have hst' : Outside st 24 (winA s (240 + kc) 72) := by
    simp only [win, winA, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  obtain ⟨hstk, e0, e1, e2⟩ := stkOK_frame a6 hF hst' (LiveExt.refl R L1)
  refine ⟨hreg.trans a1, a2.trans hF fun x m hx => ⟨hx, ?_⟩,
    ⟨fun x m hin hout' => (hF.readLE x m ?_).trans (a3.readLE x m hin hout')⟩, a4, ?_, hstk, e1.trans a7, ?_⟩
  · simp only [outside_append] at hx; exact hx.1.1.2
  · obtain ⟨q, hq, h1, h2⟩ := a4.inRanges_old hin
    have := hLs1 q hq
    simp only [winA, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega
  · refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) a5
    simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp only; simp only [K, A]; exact hout.of_sub (by omega) (by omega))
  · exact ⟨by rw [e0, e2]; exact a8.1, ArrIn.congr a8.2 e0 e2 fun _ h => h⟩

theorem outside_of_apartAll {p n a k : Nat} {L : List (Nat × Nat)} (h : ApartAll p n L) (h1 : p ≤ a)
    (h2 : a + k ≤ p + n) : Outside a k L := by
  induction L with
  | nil => trivial
  | cons r L ih =>
    have hr := h r (List.mem_cons_self ..)
    unfold Apart at hr
    exact ⟨by omega, ih fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- an owned array stays owned across a memory change that keeps accessibility and the stack header, and a live-set
extension -/
theorem own_mono {R : RtInv} {kc : Nat} {L L1 L2 : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat} {M M' : Memory}
    {p c : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c) (hLE : LiveExt R L1 L2)
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st) (e2 : stCap M' st = stCap M st) :
    Own R kc L L2 s zp zc st xp xl M' p c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨a1, a2, fun hc => ?_, a4, a5, a6, a7, ?_, ?_⟩
  · obtain ⟨c1, c2, c3, c4⟩ := a3 hc
    exact ⟨c1, hLE.held c2, by rw [hacc]; exact c3, c4⟩
  · unfold StkApart; rw [e0, e1, e2]; exact a8
  · unfold WA; rw [e0, e2]; exact a9

set_option maxRecDepth 20000 in
/-- a word store into an owned array keeps the runtime facts -/
theorem rtM_store {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p c : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    (hown : Own R kc L L1 s zp zc st xp xl M p c) {a v : Nat} (h1 : p ≤ a) (h2 : a + 8 ≤ p + 8 * c) :
    RtM R kc L s zp zc st (M.writeLE a 8 v) L1 b1 := by
  obtain ⟨r0, F0, LF0, LE0, inv0, stk0, len0, arr0, ain0⟩ := hrt
  obtain ⟨-, -, live, own, -, -, -, sa, -⟩ := hown
  obtain ⟨-, hheld, -, -⟩ := live (by omega)
  obtain ⟨sa1, -⟩ := sa (by omega)
  unfold Apart at sa1
  have hst : Outside st 24 [(a, a + 8)] := by simp only [outside_cons, outside_nil, and_true]; omega
  have hF1 : MemFrame M (M.writeLE a 8 v) [(a, a + 8)] :=
    (MemFrame.refl M _).writeLE_inRanges _ ⟨(a, a + 8), by simp, by simp only; omega, by simp only; omega⟩
  obtain ⟨hstk, e0, e1, e2⟩ := stkOK_frame stk0 hF1 hst (LiveExt.refl R L1)
  have hlen : stLen (M.writeLE a 8 v) st = stLen M st := e1
  refine ⟨by rw [Memory.regions_writeLE]; exact r0, ?_, ?_, LE0, inv_store_held inv0 (hheld.sub h1 h2), hstk,
    hlen.trans len0, by rw [e0, e2]; exact arr0, ArrIn.congr ain0 e0 e2 fun _ h => h⟩
  · refine F0.writeLE_inRanges v ?_
    rcases own with ⟨rfl, rfl⟩ | ⟨hIn, -⟩
    · exact ⟨(p, p + 8 * c), List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)),
        by simp only; omega, by simp only; omega⟩
    · exact ((hIn.sub h1 h2).append_left _).append_left _ |>.append_left _
  · rcases own with ⟨rfl, rfl⟩ | ⟨-, hAp⟩
    · exact FvModexp.LiveFrame.writeLE_ws LF0 v ⟨(p, p + 8 * c), List.mem_append_left _ (List.mem_singleton_self _),
        by simp only; omega, by simp only; omega⟩
    · exact LF0.writeLE v (outside_of_apartAll hAp h1 h2)

end FvModexp.Arm64.ModInv
