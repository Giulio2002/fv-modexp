import FvModexp.Proofs.Arm64.Exp.CallWW
import FvModexp.Proofs.Arm64.Exp.SubMod2NDefs
import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.CmpW
import FvModexp.Proofs.Arm64.Nat.TruncDefs
import FvModexp.Proofs.Common.BitLenA64

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64): the precondition-independent helpers (agent infra)

Frame / runtime-fact (`Rt`, `Fw`) helpers, budget bounds and the `trunc` / `nat.add` / `nat.cmp` call helpers used by
the general summary (`SubMod2NG*`). (The old `Pre`-based segment chain SubMod2NS1..S4C was retired in infra s33:
`SubMod2N.ens` is now derived from `ensG`.)

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

/-! ## Composing the runtime-side facts -/

theorem inRanges_outside_win {L : List (Nat × Nat)} {s : State} (hLs : LiveSep L (win s K A)) {a k : Nat}
    (h : InRanges a k L) : Outside a k (winA s K A) := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := hLs r hr
  simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢
  omega

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
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
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
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
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

theorem fresh_of {R : RtInv} {L L1 : List (Nat × Nat)} (hLE : LiveExt R L L1) {p c : Nat}
    (h : ApartAll p c L1) : ApartAll p c L := fun r hr => h r (hLE.mem_old hr)

end FvModexp.Arm64.SubMod2N

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem sub_names : ∀ x, NatSub.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)

theorem add_names : ∀ x, NatAdd.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (premise `AddHypR`) at its entry `1781184` with `SP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem addCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} (hadd : AddHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat} {M : Memory}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatAdd.names).link impl) ra) (bra : ra < 2 ^ 64)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' < 2 ^ 64) (bx39 : xl < 2 ^ 39) (by39 : yl < 2 ^ 39)
    (hpc : S.pc = BitVec.ofNat 64 1781184) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 xp) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 sp') (h28 : (S.regs 28).toNat = g)
    (hpre : NatAdd.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.pc = BitVec.ofNat 64 ra →
      s'.sp = BitVec.ofNat 64 sp' → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 → s'.regs 18 = S.regs 18 →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl + natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ max xl yl + 1 → LiveExt R L L' →
      b - makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4464, sp' - 8), (sp' + 8, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] →
      ((if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 →
      p' < 2 ^ 64 ∧ n' < 2 ^ 64 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS' := CallWW.hypSum hap add_names (hadd b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatAdd.fn = 1781184 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  · obtain ⟨p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    have hspT : S.sp.toNat = sp' := by rw [hsp]; exact tN bsp
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [winA, hspT, h28] at hF hinv
    simp only [NatAdd.mx, NatAdd.need, tN bxl, tN byl] at hln hb hr1 hr2
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (hr.trans h30) (e1.trans hsp) e2 e3 e4 hrg (by rw [← q0, Expmc.bv_ofNat_toNat])
      (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat]) hv hn hlc hln hLE hb hinv hlive hor
      hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 (by omega)) ⟨by rw [← q0]; exact BitVec.isLt _, by rw [← q1]; exact BitVec.isLt _⟩
    obtain ⟨a1, a2⟩ := hr1 h
    exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

/-- a call of `nat.cmp` (asm's `cmp_summary`) at its entry, `ReachesRet` continuation form -/
theorem cmpCall {impl : List Segment} {S : State} {ret : BitVec 64} {Q : State → Prop}
    (hpc : S.pc = BitVec.ofNat 64 1782608) (hpre : CmpSum.Pre S)
    (K : ∀ S' : State, S'.pc = S.regs 30 → S'.sp = S.sp →
      S'.regs 0 = CmpSum.cmpRes (S.regs 1).toNat (S.regs 4).toNat (S.mem.readLE (S.regs 0).toNat (8 * (S.regs 1).toNat))
        (S.mem.readLE (S.regs 3).toNat (8 * (S.regs 4).toNat)) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      MemFrame S.mem S'.mem [(S.sp.toNat - 24, S.sp.toNat - 8), (S.sp.toNat + 8, S.sp.toNat + 16),
        (S.sp.toNat + 32, S.sp.toNat + 40)] → S'.mem.regions = S.mem.regions →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  refine ReachesRet.call_regions (LibWC.cmpSum impl) hpc hpre fun s' hr hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  exact K _ hr rfl (by simp [setReg]; rfl) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) hf hrg

/-- the frame words survive a callee at `SP - 144` -/
theorem fw_call {R : RtInv} {s : State} {M M' : Memory} {zp zl zc yp n stk above : Nat} {zr : Nat × Nat}
    (hs : 4608 ≤ s.sp.toNat) (hout : Outside (s.sp.toNat - 4608) (4608 + 88) R.rt)
    (hzw : zp + 8 * zc ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zp) (hzr : zr = (zp, zp + 8 * zc) ∨ zr.2 = 0)
    (hk : stk ≤ 4464) (ha : above ≤ 88) (h : Fw s M zp zl zc yp n)
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 144 - stk, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + above)] ++ [zr])) : Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 88 → (a + 8 ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 56 ≤ a) →
      M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
    rcases hzr with rfl | h0
    · simp only [outside_cons, outside_nil, and_true]; omega
    · obtain ⟨z1, z2⟩ := zr
      simp only at h0; subst h0
      simp only [outside_cons, outside_nil, and_true]; omega
  exact ⟨(r _ (by omega) (by omega) (by omega)).trans f1, (r _ (by omega) (by omega) (by omega)).trans f2,
    (r _ (by omega) (by omega) (by omega)).trans f3, (r _ (by omega) (by omega) (by omega)).trans f4,
    (r _ (by omega) (by omega) (by omega)).trans f5, (r _ (by omega) (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega) (by omega)).trans f7⟩

/-- `nat.cmp`'s frame at `SP - 144` lies in the function's `winA` and in the generic callee frame -/
theorem cmp_frame {R : RtInv} {s S : State} {M M' : Memory} (hs : 4608 ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - 144)
    (hF : MemFrame M M' [(S.sp.toNat - 24, S.sp.toNat - 8), (S.sp.toNat + 8, S.sp.toNat + 16),
        (S.sp.toNat + 32, S.sp.toNat + 40)]) :
    MemFrame M M' (winA s K A) ∧ MemFrame M M' (R.rt ++ [(s.sp.toNat - 144 - 24, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 40)] ++ [((0 : Nat), (0 : Nat))]) := by
  rw [hsp] at hF
  refine ⟨hF.mono fun a n h => ?_, hF.mono fun a n h => ?_⟩
  · simp only [winA, K, A, outside_cons, outside_nil, and_true] at h ⊢; omega
  · simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega

end FvModexp.Arm64.SubMod2N

