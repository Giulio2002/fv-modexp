import FvModexp.Proofs.Arm64.Exp.SubMod2NDefs
import FvModexp.Proofs.Arm64.Nat.TruncDefs
import FvModexp.Proofs.Common.BitLenA64

/-!
# `nat.subMod2N` (arm64): the join-point statements and the call helpers (agent infra)

The function is proved as a chain of segment lemmas over the entry state `s` (precondition `Pre`), each ending in the
statement of the next join as a hypothesis (`J1`, `J2`, `J3`), so the segment modules compile in parallel:
* entry (`+0`) → `J1` (`+0xfc`): `x = x.trunc(x, n)` when `x.bitLen() > n` (in place: `x = z`, `cap z ≥ ⌈n/64⌉`);
* `J1` → `J2` (`+0x1c8`): `y = nat(nil).trunc(y, n)` when `y.bitLen() > n`;
* `J2` → return (`x.cmp(y) ≥ 0`: `z.sub(x, y)`) or → `J3` (`+0x21c`, after `z = z.sub(y, x)`);
* `J3` → return: the `append` loop, the complement loop, `z.trunc(z, n)`, `z.add(z, natOne)`.

Frame (`SP' = SP - 144`): saved LR at `SP - 144`, FP at `SP - 152`; spills z `SP + 8 … SP + 24`, x `SP + 32`,
y `SP + 56 … SP + 72`, n `SP + 80`; locals x' `SP - 16` (ptr) / `SP - 40` (len) / `SP - 32` (cap),
y' `SP - 24` / `SP - 56` / `SP - 48`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-! ## Budget -/

theorem makeCost_le_w {k n : Nat} (h : k ≤ W n + 1) : makeCost k ≤ wCost n := by
  unfold makeCost makeCap wCost allocCost; split <;> omega

theorem truncNeed_le_w (xl n : Nat) : makeCost (truncNeed xl n) ≤ wCost n :=
  makeCost_le_w (by unfold truncNeed W; omega)

/-! ## The goal from inside the frame -/

/-- what the function promises, from a state `S` inside its frame (entry state `s`) -/
@[reducible] def Goal (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat)
    (s S : State) : Prop :=
  ReachesRet (LibExp.program.link impl) (s.regs 30) S (fun s' =>
    (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
      Post R b L zp zl zc yp yl n s s')

/-- the saved LR / FP and the argument spills that later code reloads -/
@[reducible] def Fw (s : State) (M : Memory) (zp zl zc yp n : Nat) : Prop :=
  M.readLE (s.sp.toNat - 144) 8 = (s.regs 30).toNat ∧ M.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat ∧
    M.readLE (s.sp.toNat + 8) 8 = zp ∧ M.readLE (s.sp.toNat + 16) 8 = zl ∧ M.readLE (s.sp.toNat + 24) 8 = zc ∧
    M.readLE (s.sp.toNat + 56) 8 = yp ∧ M.readLE (s.sp.toNat + 80) 8 = n

/-- the runtime-side facts at memory `M` after `k` budgeted calls: live set `L1 ⊇ L`, budget `b1`, `z` live -/
@[reducible] def Rt (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (zp zc n k : Nat) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop :=
  M.regions = s.mem.regions ∧ MemFrame s.mem M (R.rt ++ winA s K A ++ [(zp, zp + 8 * zc)]) ∧
    LiveFrame s.mem M L [(zp, zp + 8 * zc)] ∧ LiveExt R L L1 ∧ b - k * wCost n ≤ b1 ∧
    R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧ NatLive M R L1 zp zc

/-- **J1** (`+0xfc`): `x' = x mod 2^n` in `z`'s array (`X0..X2 = z`, `X3..X5 = x'`, `X6..X8 = y`, `X9 = n`) -/
def J1 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0xfc) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 zl → S.regs 2 = BitVec.ofNat 64 zc →
    S.regs 3 = BitVec.ofNat 64 zp → S.regs 4 = BitVec.ofNat 64 l1 → S.regs 5 = BitVec.ofNat 64 zc →
    S.regs 6 = BitVec.ofNat 64 yp → S.regs 7 = BitVec.ofNat 64 yl → S.regs 8 = BitVec.ofNat 64 yc →
    S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 1 S.mem L1 b1 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ zc →
    Goal impl R b L zp zl zc yp yl n s S


/-! ## Composing the runtime-side facts -/

theorem inRanges_outside_win {L : List (Nat × Nat)} {s : State} (hLs : LiveSep L (win s K A)) {a k : Nat}
    (h : InRanges a k L) : Outside a k (winA s K A) := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := hLs r hr
  simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢
  omega

set_option maxRecDepth 20000 in
/-- after stack-only stores (`MemFrame` over `winA`): the runtime facts hold with the entry live set and budget -/
theorem rt_stack {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} (k : Nat) (hF : MemFrame s.mem M (winA s K A))
    (hreg : M.regions = s.mem.regions) : Rt R b L s zp zc n k M L b := by
  obtain ⟨⟨-, ⟨-, -, -, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzl, -, -, -, -, -, -, -, -, -,
    -, hinv, -⟩ := hpre
  refine ⟨hreg, hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    Expmc.liveFrame_of_frame hF fun a k hin _ => inRanges_outside_win hLs hin, LiveExt.refl R L, Nat.sub_le _ _,
    Expmc.inv_frame hF (fun r hr => Or.inr ?_) ?_, fun hc => ?_⟩
  · simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only [K]; omega) (by simp only [K, A]; omega)
  · exact hinv
  · obtain ⟨h1, h2, h3, h4⟩ := hzl hc
    exact ⟨h1, h2, by rw [hF.accessible]; exact h3, h4⟩

/-- the callee window of a call at `SP - 144` (`stk ≤ 4464`, `above ≤ 136`) lies inside the function's `winA` -/
theorem cw_sub {s : State} {stk above : Nat} (hal : 4608 ≤ s.sp.toNat) (hk : stk ≤ 4464) (ha : above ≤ 136) {a n : Nat}
    (h : Outside a n (winA s K A)) :
    Outside a n [(s.sp.toNat - 144 - stk, s.sp.toNat - 144 - 8), (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + above)] := by
  simp only [winA, outside_cons, outside_nil, and_true, K, A] at h ⊢
  omega

/-- after a callee at `SP - 144` that writes its window, the runtime ranges and the range `zr` (`z`'s array or an
empty range) -/
theorem rt_call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M0 M1 : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 c stk above : Nat} {zr : Nat × Nat}
    (hrt : Rt R b L s zp zc n k M0 L1 b1) (hal : 4608 ≤ s.sp.toNat) (hk : stk ≤ 4464) (ha : above ≤ 136)
    (hzr : zr = (zp, zp + 8 * zc) ∨ zr.2 = 0)
    (hreg : M1.regions = M0.regions)
    (hF : MemFrame M0 M1 (R.rt ++ [(s.sp.toNat - 144 - stk, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + above)] ++ [zr]))
    (hLF : LiveFrame M0 M1 L1 [zr]) (hLE : LiveExt R L1 L2) (hb : b1 - c ≤ b2) (hc : c ≤ wCost n)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M1)) (hlive : NatLive M1 R L2 zp zc) :
    Rt R b L s zp zc n (k + 1) M1 L2 b2 := by
  obtain ⟨hreg0, hF0, hLF0, hLE0, hb0, -, -⟩ := hrt
  have hz : ∀ a m, Outside a m [(zp, zp + 8 * zc)] → Outside a m [zr] := by
    intro a m h
    rcases hzr with rfl | h2
    · exact h
    · obtain ⟨z1, z2⟩ := zr
      simp only [outside_cons, outside_nil, and_true] at h ⊢ h2
      omega
  refine ⟨hreg.trans hreg0, hF0.trans hF fun a m h => ?_, hLF0.trans (FvModexp.LiveFrame.mono_ws hLF hz) fun a m h => hLE0.inRanges_old h,
    hLE0.trans hLE, ?_, hinv, hlive⟩
  · simp only [outside_append] at h ⊢
    exact ⟨h, ⟨⟨h.1.1, cw_sub hal hk ha h.1.2⟩, hz a m h.2⟩⟩
  · rw [Nat.add_mul, Nat.one_mul]; omega

theorem natNorm_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p n : Nat}
    (ho : Outside p (8 * n) rs) (hn : NatNorm m p n) : NatNorm m' p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · exact Or.inl h0
  rcases hn with hn | hn
  · exact Or.inl hn
  · refine Or.inr ?_
    rw [h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn

/-- **J2** (`+0x1c8`): `x'` as at `J1` (`X3..X5`), `y' = y mod 2^n` (`X6..X8`: `y`'s or a fresh array); the locals
`x'` at `SP - 16 / - 40 / - 32` stored -/
def J2 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 p2 l2 c2 : Nat) (L2 : List (Nat × Nat)) (b2 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x1c8) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 3 = BitVec.ofNat 64 zp → S.regs 4 = BitVec.ofNat 64 l1 → S.regs 5 = BitVec.ofNat 64 zc →
    S.regs 6 = BitVec.ofNat 64 p2 → S.regs 7 = BitVec.ofNat 64 l2 → S.regs 8 = BitVec.ofNat 64 c2 →
    Fw s S.mem zp zl zc yp n → S.mem.readLE (s.sp.toNat - 16) 8 = zp → S.mem.readLE (s.sp.toNat - 40) 8 = l1 →
    S.mem.readLE (s.sp.toNat - 32) 8 = zc → Rt R b L s zp zc n 2 S.mem L2 b2 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ W n →
    natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n → NatNorm S.mem p2 l2 → l2 ≤ W n → l2 ≤ c2 → c2 < 2 ^ 40 →
    S.mem.accessible p2 (8 * l2) false = true → p2 + 8 * l2 ≤ 2 ^ 48 → Held R L2 p2 (8 * l2) →
    (p2 + 8 * l2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p2) → Apart zp (8 * zc) p2 (8 * l2) →
    Goal impl R b L zp zl zc yp yl n s S

/-- a normalised nat below `2^n` has at most `⌈n/64⌉` limbs -/
theorem len_le_W {m : Memory} {p l n : Nat} (hn : NatNorm m p l) (hv : natVal m p l < 2 ^ n) : l ≤ W n := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exact Nat.zero_le _
  have h1 := SubMod2N.natVal_lower m p l hn hl
  have h2 : 2 ^ (64 * (l - 1)) < 2 ^ n := Nat.lt_of_le_of_lt h1 hv
  have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
  unfold W; omega

theorem rt_mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k k' : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (h : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ k') :
    Rt R b L s zp zc n k' M L1 b1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
  have := Nat.mul_le_mul_right (wCost n) hk
  omega

set_option maxRecDepth 20000 in
/-- stack stores (inside `winA`) keep the runtime facts -/
theorem rt_stk {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M M' : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (h : Rt R b L s zp zc n k M L1 b1) (hF : MemFrame M M' (winA s K A)) (hreg : M'.regions = M.regions) :
    Rt R b L s zp zc n k M' L1 b1 := by
  obtain ⟨⟨-, ⟨-, -, -, -⟩, -, hout, -, -, hLs, -⟩, -⟩ := hpre
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  have hwr : ∀ r ∈ winA s K A, Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only [K]; omega) (by simp only [K, A]; omega)
  have hLs1 := LiveExt.liveSep a4 hLs (fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    simp only [K, A] at hout ⊢; exact hout.of_sub (by omega) (by omega))
  refine ⟨hreg.trans a1, a2.trans hF fun x m hx => ?_, a3.trans (Expmc.liveFrame_of_frame hF fun x m hin _ => ?_)
    fun x m h => a4.inRanges_old h, a4, a5, Expmc.inv_frame hF (fun r hr => Or.inr (hwr r hr)) a6, fun hc => ?_⟩
  · refine ⟨hx, ?_⟩; simp only [outside_append] at hx; exact hx.1.2
  · exact inRanges_outside_win hLs1 hin
  · obtain ⟨c1, c2, c3, c4⟩ := a7 hc
    exact ⟨c1, c2, by rw [hF.accessible]; exact c3, c4⟩

/-- a range held by the entry live set, outside the window and apart from `z`, keeps its bytes -/
theorem rd_held {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (h : Rt R b L s zp zc n k M L1 b1) {a m : Nat} (hh : Held R L a m)
    (hw : Outside a m (winA s K A)) (hz : Apart a m zp (8 * zc)) : M.readLE a m = s.mem.readLE a m := by
  refine Expmc.held_readLE hh h.2.1 h.2.2.1 hw ?_
  simp only [outside_cons, outside_nil, and_true]; unfold Apart at hz; omega

theorem apart_fresh {R : RtInv} {L : List (Nat × Nat)} {a n p k : Nat} (h : Held R L a n)
    (hAp : ApartAll p k L) (hIn : InRanges p k R.rt) : Apart a n p k := by
  rcases h with ⟨q, hq, h1, h2⟩ | ho
  · have := hAp q hq; unfold Apart at this ⊢; omega
  · obtain ⟨r, hr, h1, h2⟩ := hIn
    have := MemFrame.outside_mem ho hr; unfold Apart; omega

/-- the frame words survive stores to the locals `[SP - 56, SP - 8)` -/
theorem fw_loc {s : State} {M M' : Memory} {zp zl zc yp n : Nat} (hs : 152 ≤ s.sp.toNat) (h : Fw s M zp zl zc yp n)
    (hF : MemFrame M M' [(s.sp.toNat - 56, s.sp.toNat - 8)]) : Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (a + 8 ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 8 ≤ a) → M'.readLE a 8 = M.readLE a 8 := fun a ha =>
    hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; exact ha)
  refine ⟨(r _ ?_).trans f1, (r _ ?_).trans f2, (r _ ?_).trans f3, (r _ ?_).trans f4, (r _ ?_).trans f5,
    (r _ ?_).trans f6, (r _ ?_).trans f7⟩ <;> omega

/-! ## The call environment of a callee at `SP - 144` -/

theorem liveSep_sub {L : List (Nat × Nat)} {lo hi lo' hi' : Nat} (h : LiveSep L [(lo, hi)]) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : LiveSep L [(lo', hi')] := by
  intro r hr
  have := h r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

set_option maxRecDepth 20000 in
/-- `CEnv` of a callee window `[SP - 144 - 4464, SP - 144 + 88)` from the precondition and the runtime facts -/
theorem cenv_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hd : Extracted.program.DataLoaded M) :
    CallW.CEnv R L1 (s.regs 28).toNat (s.sp.toNat - 144) 4464 88 M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, hro⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hzg, -⟩ := hpre
  obtain ⟨hreg, hF, -, hLE, -⟩ := hrt
  simp only [K, A] at *
  have hgv : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hF.readLE _ _ ?_
    simp only [winA, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hga hzg
    exact ⟨⟨hgr, by omega, by omega⟩, by omega⟩
  refine ⟨by omega, by omega, by omega, ?_, hg1, by rw [hF.accessible]; exact hg2, by rw [hgv]; omega,
    hout.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgr, ?_, hd, hro⟩
  · rw [hF.accessible]; exact Memory.accessible_sub _ hw (Or.inr rfl) (by omega) (by omega)
  · refine LiveExt.liveSep hLE (liveSep_sub (lo := s.sp.toNat - 4608) (hi := s.sp.toNat + 88) ?_ (by omega) (by omega))
      (fun r hr => ?_)
    · exact hLs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only
      exact hout.of_sub (by omega) (by omega)

/-- `DataLoaded` survives the frame -/
theorem dl_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) : Extracted.program.DataLoaded M := by
  obtain ⟨⟨⟨-, -, -⟩, ⟨-, -, -, hw⟩, hd, -, -, -, -, hro⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzl, -⟩ := hpre
  obtain ⟨hreg, hF, -⟩ := hrt
  refine dataLoaded_frame hd hreg hro (by simpa only [List.append_assoc] using hF) fun r hr hlt => ?_
  simp only [winA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Memory.accessible_sub _ hw (Or.inr rfl) (by simp only at hlt ⊢; omega) (by simp only at hlt ⊢; omega)
  · exact Memory.accessible_sub _ hw (Or.inr rfl) (by simp only at hlt ⊢; omega) (by simp only at hlt ⊢; omega)
  · simp only at hlt ⊢
    have := (hzl (by omega)).2.2.1
    rwa [show zp + 8 * zc - zp = 8 * zc by omega]

end FvModexp.Arm64.SubMod2N

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.EvenHyp

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
/-- a return address inside `subMod2N`'s own segment (`seg40`, base `1805584`) is a return address of every callee
program that does not contain `subMod2N` -/
theorem ra_of {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 200) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (1805584 + 4 * i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg40) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x1b8d10 + 4 * i < 2 ^ 48; omega) (by decide)
  simpa only [Extracted.seg40] using this

set_option maxRecDepth 20000 in
/-- a call of `nat.trunc` (asm's `Trunc.Hyp2`) at its entry, continuation form, Nat-level arguments -/
theorem truncCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat}
    (htr : Trunc.Hyp2 impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 1786000) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64) (bn : n < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : TruncPre R b L stk above zp zl zc x xl n S) (hnorm : NatNorm S.mem x xl ∨ (n + 63) / 64 ≤ xl)
    (hcp : zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → TruncPost R b L stk above zp zc x xl n S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n))
  rw [show segAddr Extracted.program Trunc.fn = 1786000 by decide] at hS
  have hzl : zl < 2 ^ 64 := by have := hpre.2.2.1; omega
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  · rw [tN bz, tN hzl, tN bzc, tN bx, tN bxl, tN bn]; exact ⟨hpre, hnorm, hcp⟩
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bn] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

/-- `bitLen` of a word -/
theorem bitLen_le64 (v : Nat) (h : v < 2 ^ 64) : Aux.bitLen v ≤ 64 := by
  by_cases hv : v = 0
  · subst hv; decide
  · have h1 := (Util.bitLen_bounds v hv).1
    have h2 : 2 ^ (Aux.bitLen v - 1) < 2 ^ 64 := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega

end FvModexp.Arm64.SubMod2N

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- the precondition of a `trunc` call at `SP - 144` (`z' = z` or nil, `x` readable and below `SP - 56`) -/
theorem truncPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State} (hS : S.mem = M)
    (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {stk above : Nat} (hkT : stk ≤ 4464) (haT : above ≤ 88)
    {zp' zl' zc' : Nat} (hz' : (zp' = zp ∧ zc' = zc) ∨ zc' = 0) (hzl' : zl' ≤ zc')
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ x) (hxl : xl ≤ 2 ^ 16)
    (halias : zp' = x ∨ (0 < zc' → 0 < xl → Apart zp' (8 * zc') x (8 * xl))) :
    TruncPre R b1 L1 stk above zp' zl' zc' x xl n S := by
  have hce := CallW.callEnv_of (cenv_of hpre hrt (dl_of hpre hrt)) hsp (h28.trans (Expmc.bv_ofNat_toNat _).symm) hS
    hkT haT
  have hsp4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hb := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, hlive⟩ := hrt
  refine ⟨hce, hpre.2.1, hzl', ⟨?_, ?_, fun hc => ?_⟩, ⟨hx40, by rw [hS]; exact hxa, hx48, hxh, ?_⟩, hxl,
    by have := hpre.2.2.2.2.2.2.2.1; omega, halias, ?_, by rw [hS, h28]; exact hinv⟩
  · rcases hz' with ⟨-, rfl⟩ | rfl
    · have := hpre.2.2.2.2.2.2.2.2.2.2.1; omega
    · omega
  · rcases hz' with ⟨rfl, rfl⟩ | rfl
    · rw [hS]; exact hlive
    · simp
  · rcases hz' with ⟨rfl, rfl⟩ | rfl
    · have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [win, K, A, hspT, h28, outside_cons, outside_nil, and_true] at hzw ⊢
      exact ⟨by omega, hzg⟩
    · omega
  · simp only [win, hspT, outside_cons, outside_nil, and_true]; omega
  · have h1 := truncNeed_le_w xl n
    simp only [cost] at hb
    rw [Nat.mul_comm] at hbud
    have h2 : wCost n * k ≤ wCost n * 4 := Nat.mul_le_mul_left _ hk
    omega

end FvModexp.Arm64.SubMod2N

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-! ## `nat.sub` / `nat.add` with the reuse conjunct (NOTES-divmc [infra s5] request)

Exactly the types of divmc's `NatSub.ensR` / `NatAdd.ensR` (`z` reused when `cap z ≥ need`; result capacity below
`2^40` when the operands are below `2^39` words); discharged by `subHypR_of` / `addHypR_of` (SubMod2NCall). -/

def SubHypR (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatSub.names).link impl) (segAddr Extracted.program NatSub.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (NatSub.Pre R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatSub.Post R b L zp zc xp xl yp yl s s' ∧
        (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
        (xl.toNat < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40))

def AddHypR (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatAdd.names).link impl) (segAddr Extracted.program NatAdd.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (NatAdd.Pre R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatAdd.Post R b L zp zc xp xl yp yl s s' ∧
        (NatAdd.need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
        (NatAdd.mx xl yl < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40))

/-- **J3** (`+0x21c`, after `z = z.sub(y', x')` with `x' < y'`): `z = (zp, l3, zc)` (`X0..X2`) holds `y' - x'` -/
def J3 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l3 : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x21c) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 l3 → S.regs 2 = BitVec.ofNat 64 zc →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem zp l3 = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l3 → l3 ≤ W n →
    Goal impl R b L zp zl zc yp yl n s S

/-- the postcondition from the runtime facts after the last call and the result -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n k : Nat} {s s' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat} (hrt : Rt R b L s zp zc n k s'.mem L2 b2) (hk : k ≤ 5)
    {p' l' c' : Nat} (e0 : (s'.regs 0).toNat = p') (e1 : (s'.regs 1).toNat = l') (e2 : (s'.regs 2).toNat = c')
    (hv : natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n) (hnorm : NatNorm s'.mem p' l')
    (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40) (hlive : NatLive s'.mem R L2 p' c')
    (hor : (p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hre : W n + 1 ≤ zc → p' = zp ∧ c' = zc) :
    Post R b L zp zl zc yp yl n s s' := by
  obtain ⟨-, hF, hLF, hLE, hb, hinv, -⟩ := hrt
  have : k * wCost n ≤ 5 * wCost n := Nat.mul_le_mul_right _ hk
  exact ⟨p', l', c', e0, e1, e2, hv, hnorm, hlc, hc40, L2, b2, hLE, by simp only [cost]; omega, hinv, hlive, hor, hF, hLF,
    hre⟩

theorem fresh_of {R : RtInv} {L L1 : List (Nat × Nat)} (hLE : LiveExt R L L1) {p c : Nat}
    (h : ApartAll p c L1) : ApartAll p c L := fun r hr => h r (hLE.mem_old hr)

end FvModexp.Arm64.SubMod2N
