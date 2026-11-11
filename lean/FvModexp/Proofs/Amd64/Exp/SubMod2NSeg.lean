import FvModexp.Proofs.Amd64.Exp.SubMod2NDefs

/-!
# `nat.subMod2N` (amd64): the join-point statements and the call helpers (agent infra; twin of the arm64 module)

Segments over the entry state `s` (`e = RSP` at entry):
* entry → `J1` (`+0x157`): `x = x.trunc(x, n)` when `x.bitLen() > n` (`x = z`, in place);
* `J1` → `J2` (`+0x246`): `y = nat(nil).trunc(y, n)` when `y.bitLen() > n`;
* `J2` → return (`x.cmp(y) ≥ 0`: `z.sub(x, y)`) or → `J3` (`+0x2ac`, after `z = z.sub(y, x)`);
* `J3` → return: `append` loop, complement loop, `z.trunc(z, n)`, `z.add(z, natOne)`.
Frame words: return address `[e]`, saved `BP` `[e - 8]`, `n` `[e + 8]`, spills `zp [e + 16]`, `zl [e + 24]`, `zc [e + 32]`,
`yp [e + 64]`; locals `x'` at `e - 16 / - 40 / - 32` (ptr/len/cap), `y'` at `e - 24 / - 56 / - 48`.
Callees run with `RSP_c = e - 136`, window `[e - 136 - stk, e - 136 + above)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-! ## Budget -/

theorem makeCost_le_w {k n : Nat} (h : k ≤ W n + 1) : makeCost k ≤ wCost n := by
  unfold makeCost makeCap wCost allocCost; split <;> omega

theorem truncNeed_le_w (xl n : Nat) : makeCost (truncNeed xl n) ≤ wCost n :=
  makeCost_le_w (by unfold truncNeed W; omega)

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## The goal from inside the frame -/

/-- what the function promises, from a state `S` inside its frame (entry state `s`) -/
@[reducible] def Goal (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat)
    (s S : State) : Prop :=
  ReachesRet (LibExp.program.link impl) (retAddrOf s) S (fun s' =>
    (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
      Post R b L zp zl zc yp yl n s s')

/-- the return address, saved `BP` and the argument words that later code reloads -/
@[reducible] def Fw (s : State) (M : Memory) (zp zl zc yp n : Nat) : Prop :=
  M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
    M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    M.readLE ((s.regs 4).toNat + 16) 8 = zp ∧ M.readLE ((s.regs 4).toNat + 24) 8 = zl ∧
    M.readLE ((s.regs 4).toNat + 32) 8 = zc ∧ M.readLE ((s.regs 4).toNat + 64) 8 = yp ∧
    M.readLE ((s.regs 4).toNat + 8) 8 = n

/-- the runtime-side facts at memory `M` after `k` budgeted calls: live set `L1 ⊇ L`, budget `b1`, `z` live -/
@[reducible] def Rt (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (zp zc n k : Nat) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop :=
  M.regions = s.mem.regions ∧ MemFrame s.mem M (R.rt ++ win s K A ++ [(zp, zp + 8 * zc)]) ∧
    LiveFrame s.mem M L [(zp, zp + 8 * zc)] ∧ LiveExt R L L1 ∧ b - k * wCost n ≤ b1 ∧
    R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧ NatLive M R L1 zp zc

/-- the ABIInternal state facts every segment carries (`g`, TLS base, `X15`, `DF`) -/
@[reducible] def Abi (s S : State) : Prop :=
  S.regs 14 = s.regs 14 ∧ S.fsBase = s.fsBase ∧ S.xmm 15 = s.xmm 15 ∧ S.df = false

/-- **J1** (`+0x157`): `x' = x mod 2^n` in `z`'s array (`RAX..RCX = z`, `RDI, RSI, R8 = x'`, `R9..R11 = y`, `R12 = n`) -/
def J1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216183 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 3 = BitVec.ofNat 64 zl → S.regs 1 = BitVec.ofNat 64 zc →
    S.regs 7 = BitVec.ofNat 64 zp → S.regs 6 = BitVec.ofNat 64 l1 → S.regs 8 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 yp → S.regs 10 = BitVec.ofNat 64 yl → S.regs 11 = BitVec.ofNat 64 yc →
    S.regs 12 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 1 S.mem L1 b1 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ zc →
    Goal impl R b L zp zl zc yp yl n s S

/-! ## Composing the runtime-side facts -/

theorem inRanges_outside_win {L : List (Nat × Nat)} {s : State} (hLs : LiveSep L (win s K A)) {a k : Nat}
    (h : InRanges a k L) : Outside a k (win s K A) := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := hLs r hr
  simp only [win, outside_cons, outside_nil, and_true] at this ⊢
  omega

theorem win_rt {R : RtInv} {s : State} (hK : K ≤ (s.regs 4).toNat)
    (hout : Outside ((s.regs 4).toNat - K) (K + A) R.rt) : ∀ r ∈ win s K A, Outside r.1 (r.2 - r.1) R.rt := by
  intro r hr
  simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact hout.of_sub (by omega) (by simp only; omega)

set_option maxRecDepth 20000 in
/-- after stack-only stores (`MemFrame` over `win`): the runtime facts hold with the entry live set and budget -/
theorem rt_stack {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} (k : Nat) (hF : MemFrame s.mem M (win s K A))
    (hreg : M.regions = s.mem.regions) : Rt R b L s zp zc n k M L b := by
  obtain ⟨⟨-, ⟨hK, -, -⟩, -, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzl, -, -, -, -, -, -, -,
    -, -, -, hinv, -⟩ := hpre
  refine ⟨hreg, hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    Expmc.liveFrame_of_frame hF fun a k hin _ => inRanges_outside_win hLs hin, LiveExt.refl R L, Nat.sub_le _ _,
    Expmc.inv_frame hF (fun r hr => Or.inr (win_rt hK hout r hr)) hinv, fun hc => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hzl hc
  exact ⟨h1, h2, by rw [hF.accessible]; exact h3, h4⟩

/-- the callee window of a call with `RSP_c = e - 136` (`stk ≤ 4440`, `above ≤ 224`) lies inside the function's `win` -/
theorem cw_sub {s : State} {stk above : Nat} (hs : 4576 ≤ (s.regs 4).toNat) (hk : stk ≤ 4440) (ha : above ≤ 224) {a n : Nat}
    (h : Outside a n (win s K A)) :
    Outside a n [((s.regs 4).toNat - 136 - stk, (s.regs 4).toNat - 136 + above)] := by
  simp only [win, outside_cons, outside_nil, and_true, K, A] at h ⊢
  omega

/-- after a callee at `RSP_c = e - 136` that writes its window, the runtime ranges and the range `zr` (`z`'s array or
an empty range) -/
theorem rt_call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M0 M1 : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 c stk above : Nat} {zr : Nat × Nat}
    (hrt : Rt R b L s zp zc n k M0 L1 b1) (hs : 4576 ≤ (s.regs 4).toNat) (hk : stk ≤ 4440) (ha : above ≤ 224)
    (hzr : zr = (zp, zp + 8 * zc) ∨ zr.2 = 0)
    (hreg : M1.regions = M0.regions)
    (hF : MemFrame M0 M1 (R.rt ++ [((s.regs 4).toNat - 136 - stk, (s.regs 4).toNat - 136 + above)] ++ [zr]))
    (hLF : LiveFrame M0 M1 L1 [zr]) (hLE : LiveExt R L1 L2) (hb : b1 - c ≤ b2) (hc : c ≤ wCost n)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 M1)) (hlive : NatLive M1 R L2 zp zc) :
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
    exact ⟨h, ⟨⟨h.1.1, cw_sub hs hk ha h.1.2⟩, hz a m h.2⟩⟩
  · rw [Nat.add_mul, Nat.one_mul]; omega

theorem natNorm_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p n : Nat}
    (ho : Outside p (8 * n) rs) (hn : NatNorm m p n) : NatNorm m' p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · exact Or.inl h0
  rcases hn with hn | hn
  · exact Or.inl hn
  · refine Or.inr ?_
    rw [h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn

/-- **J2** (`+0x246`): `x'` as at `J1` (`RDI, RSI, R8`), `y' = y mod 2^n` (`R9..R11`: `y`'s or a fresh array); the
locals `x'` at `e - 16 / - 40 / - 32` stored -/
def J2 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 p2 l2 c2 : Nat) (L2 : List (Nat × Nat)) (b2 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216422 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 7 = BitVec.ofNat 64 zp → S.regs 6 = BitVec.ofNat 64 l1 → S.regs 8 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 p2 → S.regs 10 = BitVec.ofNat 64 l2 → S.regs 11 = BitVec.ofNat 64 c2 →
    Fw s S.mem zp zl zc yp n → S.mem.readLE ((s.regs 4).toNat - 16) 8 = zp →
    S.mem.readLE ((s.regs 4).toNat - 40) 8 = l1 → S.mem.readLE ((s.regs 4).toNat - 32) 8 = zc →
    Rt R b L s zp zc n 2 S.mem L2 b2 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ W n →
    natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n → NatNorm S.mem p2 l2 → l2 ≤ W n → l2 ≤ c2 → c2 < 2 ^ 40 →
    S.mem.accessible p2 (8 * l2) false = true → p2 + 8 * l2 ≤ 2 ^ 48 → Held R L2 p2 (8 * l2) →
    (p2 + 8 * l2 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ p2) → Apart zp (8 * zc) p2 (8 * l2) →
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
/-- stack stores (inside `win`) keep the runtime facts -/
theorem rt_stk {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M M' : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (h : Rt R b L s zp zc n k M L1 b1) (hF : MemFrame M M' (win s K A)) (hreg : M'.regions = M.regions) :
    Rt R b L s zp zc n k M' L1 b1 := by
  obtain ⟨⟨-, ⟨hK, -, -⟩, -, -, hout, -, -, hLs, -⟩, -⟩ := hpre
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  have hLs1 := LiveExt.liveSep a4 hLs (fun r hr => win_rt hK hout r hr)
  refine ⟨hreg.trans a1, a2.trans hF fun x m hx => ?_, a3.trans (Expmc.liveFrame_of_frame hF fun x m hin _ => ?_)
    fun x m h => a4.inRanges_old h, a4, a5, Expmc.inv_frame hF (fun r hr => Or.inr (win_rt hK hout r hr)) a6,
    fun hc => ?_⟩
  · refine ⟨hx, ?_⟩; simp only [outside_append] at hx; exact hx.1.2
  · exact inRanges_outside_win hLs1 hin
  · obtain ⟨c1, c2, c3, c4⟩ := a7 hc
    exact ⟨c1, c2, by rw [hF.accessible]; exact c3, c4⟩

/-- a range held by the entry live set, outside the window and apart from `z`, keeps its bytes -/
theorem rd_held {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {zp zc n k : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (h : Rt R b L s zp zc n k M L1 b1) {a m : Nat} (hh : Held R L a m)
    (hw : Outside a m (win s K A)) (hz : Apart a m zp (8 * zc)) : M.readLE a m = s.mem.readLE a m := by
  refine Expmc.held_readLE hh h.2.1 h.2.2.1 hw ?_
  simp only [outside_cons, outside_nil, and_true]; unfold Apart at hz; omega

theorem apart_fresh {R : RtInv} {L : List (Nat × Nat)} {a n p k : Nat} (h : Held R L a n)
    (hAp : ApartAll p k L) (hIn : InRanges p k R.rt) : Apart a n p k := by
  rcases h with ⟨q, hq, h1, h2⟩ | ho
  · have := hAp q hq; unfold Apart at this ⊢; omega
  · obtain ⟨r, hr, h1, h2⟩ := hIn
    have := MemFrame.outside_mem ho hr; unfold Apart; omega

/-- the frame words survive stores to the locals `[e - 56, e - 8)` -/
theorem fw_loc {s : State} {M M' : Memory} {zp zl zc yp n : Nat} (hs : 152 ≤ (s.regs 4).toNat)
    (h : Fw s M zp zl zc yp n) (hF : MemFrame M M' [((s.regs 4).toNat - 56, (s.regs 4).toNat - 8)]) :
    Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 56 ∨ (s.regs 4).toNat - 8 ≤ a) → M'.readLE a 8 = M.readLE a 8 :=
    fun a ha => hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; exact ha)
  refine ⟨(r _ ?_).trans f1, (r _ ?_).trans f2, (r _ ?_).trans f3, (r _ ?_).trans f4, (r _ ?_).trans f5,
    (r _ ?_).trans f6, (r _ ?_).trans f7⟩ <;> omega

/-! ## The call environment of a callee at `RSP_c = e - 136` -/

theorem liveSep_sub {L : List (Nat × Nat)} {lo hi lo' hi' : Nat} (h : LiveSep L [(lo, hi)]) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : LiveSep L [(lo', hi')] := by
  intro r hr
  have := h r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

set_option maxRecDepth 20000 in
/-- `CEnv` of a callee window `[e - 136 - 4440, e - 136 + 80)` from the precondition and the runtime facts -/
theorem cenv_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hd : Extracted.program.DataLoaded M) :
    CallW.CEnv R L1 (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 136) 4440 80 M := by
  obtain ⟨⟨⟨hgN, hgR, hgB⟩, ⟨hK, hA, hw⟩, hal, -, hout, hga, hgr, hLs, hro, ⟨⟨f1, f2, f3⟩, f4, f5⟩⟩, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hzg, -, -, -, -, -, -, -, -, -, ⟨hzf, -⟩⟩ := hpre
  obtain ⟨hreg, hF, -, hLE, -⟩ := hrt
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at *
  have hgv : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    refine hF.readLE _ _ ?_
    simp only [win, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hga hzg
    exact ⟨⟨hgr, by omega⟩, by omega⟩
  have hfv : M.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    refine hF.readLE _ _ ?_
    simp only [win, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at f5 hzf
    exact ⟨⟨f4, by omega⟩, by omega⟩
  refine ⟨by omega, by omega, by omega, ?_, hgN, by rw [hF.accessible]; exact hgR, by rw [hgv]; omega,
    hout.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgr, ?_, hd, hro, by omega, by omega,
    by rw [hF.accessible]; exact f2, by rw [hfv]; exact f3, f4, by unfold Apart at f5 ⊢; omega⟩
  · rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hw (Or.inr rfl) (by omega) (by omega)
  · refine LiveExt.liveSep hLE (liveSep_sub (lo := (s.regs 4).toNat - 4576) (hi := (s.regs 4).toNat + 88) ?_
      (by omega) (by omega)) (fun r hr => ?_)
    · exact hLs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only
      exact hout.of_sub (by omega) (by omega)

/-- `DataLoaded` survives the frame -/
theorem dl_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) : Extracted.program.DataLoaded M := by
  obtain ⟨⟨-, ⟨hK, -, hw⟩, -, hd, -, -, -, -, hro, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzl, -⟩ := hpre
  obtain ⟨hreg, hF, -⟩ := hrt
  refine dataLoaded_frame64 hd hreg hro (by simpa only [List.append_assoc] using hF) fun r hr hlt => ?_
  simp only [win, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [regSP, K, A] at hw hK hlt ⊢
    exact Janus.Arm64.Memory.accessible_sub _ hw (Or.inr rfl) (by omega) (by omega)
  · simp only at hlt ⊢
    have := (hzl (by omega)).2.2.1
    rwa [show zp + 8 * zc - zp = 8 * zc by omega]

end FvModexp.Amd64.SubMod2N

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
/-- a return address inside `subMod2N`'s own segment (`seg40`, base `6215840`) is a return address of every callee
program that does not contain `subMod2N` -/
theorem ra_of {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x380) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (6215840 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg40) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5ed8a0 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg40] using this

set_option maxRecDepth 20000 in
/-- a call of `nat.trunc` (premise `TruncHyp`) at its entry `6188320`, continuation form, Nat-level arguments -/
theorem truncCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat}
    (htr : TruncHyp impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6188320) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64) (bn : n < 2 ^ 64)
    (hpre : TruncPre R b L stk above zp zl zc x xl n S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 14 = S.regs 14 →
      s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions → TruncPost R b L stk above zp zc x xl n S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (by simp [numIntRegs]) (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n))
  rw [show segAddr Extracted.program fnTrunc = 6188320 by decide] at hS
  have hzl : zl < 2 ^ 64 := by have := hpre.2.2.1; omega
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, _, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN hzl, tN bzc, tN bx, tN bxl, tN bn]; exact hpre
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bn] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e3 e4 hrg hq

end FvModexp.Amd64.SubMod2N

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
/-- the precondition of a `trunc` call at `RSP_c = e - 136` (`z' = z` or nil, `x` readable and outside the callee window) -/
theorem truncPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State} (hS : S.mem = M)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    {stk above : Nat} (hkT : stk ≤ 4440) (haT : above ≤ 80)
    {zp' zl' zc' : Nat} (hz' : (zp' = zp ∧ zc' = zc) ∨ zc' = 0) (hzl' : zl' ≤ zc')
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ x)
    (hxl : xl ≤ 2 ^ 16)
    (halias : zp' = x ∨ (0 < zc' → 0 < xl → Apart zp' (8 * zc') x (8 * xl))) :
    TruncPre R b1 L1 stk above zp' zl' zc' x xl n S := by
  have hsp4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hce := CallW.callEnv_of (cenv_of hpre hrt (dl_of hpre hrt)) hsp (by rw [h14]) (by rw [hfs]) hS hkT haT
    (by omega)
  have hb := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, hlive⟩ := hrt
  refine ⟨hce, hpre.2.1, hzl', ⟨?_, ?_, fun hc => ?_⟩, ⟨hx40, by rw [hS]; exact hxa, hx48, hxh, ?_⟩, hxl,
    by have := hpre.2.2.2.2.2.2.2.1; omega, halias, ?_, by rw [hS, h14]; exact hinv⟩
  · rcases hz' with ⟨-, rfl⟩ | rfl
    · have := hpre.2.2.2.2.2.2.2.2.2.2.1; omega
    · omega
  · rcases hz' with ⟨rfl, rfl⟩ | rfl
    · rw [hS]; exact hlive
    · simp
  · rcases hz' with ⟨rfl, rfl⟩ | rfl
    · have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hzf := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [win, K, A, hsp, h14, hfs, outside_cons, outside_nil, and_true] at hzw ⊢
      exact ⟨by omega, hzg, hzf⟩
    · omega
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; omega
  · have h1 := truncNeed_le_w xl n
    simp only [cost] at hb
    rw [Nat.mul_comm] at hbud
    have h2 : wCost n * k ≤ wCost n * 4 := Nat.mul_le_mul_left _ hk
    omega

end FvModexp.Amd64.SubMod2N

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-! ## `nat.sub` / `nat.add` with the reuse conjunct (NOTES-divmc [infra s5] request) and `DF` kept

divmc's `NatSub.ens` / `NatAdd.ens` posts with conjuncts that every path of theirs has: `z` is reused when `cap z ≥ need`,
the result capacity is below `2^40`, and `DF` is unchanged (needed for the next callee's `CallSetup`). Premises of `ens`
until divmc's posts carry them. -/

def SubHypR (impl : List Amd64.Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatSub.names).link impl) (segAddr Extracted.program NatSub.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (NatSub.Pre R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatSub.Post R b L zp zc xp xl yp yl s s' ∧
        (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
        (s'.regs 1).toNat < 2 ^ 40 ∧ s'.df = s.df)

def AddHypR (impl : List Amd64.Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatAdd.names).link impl) (segAddr Extracted.program NatAdd.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (NatAdd.Pre R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatAdd.Post R b L zp zc xp xl yp yl s s' ∧
        (NatAdd.need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
        (s'.regs 1).toNat < 2 ^ 40 ∧ s'.df = s.df)

/-- **J3** (`+0x2ac`, after `z = z.sub(y', x')` with `x' < y'`): `z = (zp, l3, zc)` (`RAX, RBX, RCX`) holds `y' - x'` -/
def J3 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l3 : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216524 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 3 = BitVec.ofNat 64 l3 → S.regs 1 = BitVec.ofNat 64 zc →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem zp l3 = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l3 → l3 ≤ W n →
    Goal impl R b L zp zl zc yp yl n s S

/-- the postcondition from the runtime facts after the last call and the result -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n k : Nat} {s s' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat} (hrt : Rt R b L s zp zc n k s'.mem L2 b2) (hk : k ≤ 5)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    {p' l' c' : Nat} (e0 : (s'.regs 0).toNat = p') (e1 : (s'.regs 3).toNat = l') (e2 : (s'.regs 1).toNat = c')
    (hv : natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n) (hnorm : NatNorm s'.mem p' l')
    (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40) (hlive : NatLive s'.mem R L2 p' c')
    (hor : (p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) :
    Post R b L zp zl zc yp yl n s s' := by
  obtain ⟨-, hF, hLF, hLE, hb, hinv, -⟩ := hrt
  have : k * wCost n ≤ 5 * wCost n := Nat.mul_le_mul_right _ hk
  exact ⟨hfs, hdf, p', l', c', e0, e1, e2, hv, hnorm, hlc, hc40, L2, b2, hLE, by simp only [cost]; omega, hinv, hlive,
    hor, hF, hLF⟩

theorem fresh_of {R : RtInv} {L L1 : List (Nat × Nat)} (hLE : LiveExt R L L1) {p c : Nat}
    (h : ApartAll p c L1) : ApartAll p c L := fun r hr => h r (hLE.mem_old hr)

end FvModexp.Amd64.SubMod2N
