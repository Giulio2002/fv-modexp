import FvModexp.Proofs.Arm64.Nat.NatAddMid

/-!
# `nat.add` (arm64): the self-call `z.add(y, x)` for `len x < len y` — the callee's precondition and the postcondition

At the self-call the callee state `S1` has `SP' = SP - 160`, the frame push and the spills of the caller in its memory
(inside `winA s 4464 80`). `preS_swap`: the caller's `PreS 4464` (with `x`, `y`) gives the callee's `PreS 4304`
(with `y`, `x`). `postS_swap`: the callee's `PostS 4304` gives the caller's `PostS 4464`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatAdd

theorem need_comm (xl yl : BitVec 64) : need yl xl = need xl yl := by
  unfold need mx; rw [Nat.min_comm, Nat.max_comm]

theorem mx_comm (xl yl : BitVec 64) : mx yl xl = mx xl yl := by unfold mx; rw [Nat.max_comm]

set_option maxRecDepth 20000 in
theorem preS_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s S1 : State}
    (hpre : PreS 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64) (h28 : S1.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S1.mem (winA s 4464 80)) (hreg : S1.mem.regions = s.mem.regions) :
    PreS 4304 R b L zp zc yp yl yc xp xl xc S1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, hyn, hxw, hyacc, hy48, hyh, hyw, hinv, hok, hmv⟩ := hpre
  have e160 : S1.sp.toNat = s.sp.toNat - 160 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold Apart at hga
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4464 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hnorm : ∀ p n, (p + 8 * n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 80 ≤ p) → NatNorm s.mem p n →
      NatNorm S1.mem p n := by
    intro p n ho hn
    rcases hn with h0 | h0
    · exact Or.inl h0
    · by_cases hn0 : n = 0
      · exact Or.inl hn0
      · right; rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact h0
  refine ⟨⟨⟨by rw [h28]; exact hg1, by rw [h28, hF.accessible]; exact hg2, ?_⟩,
      ⟨by rw [e160]; omega, by rw [e160]; omega, by rw [e160]; omega,
        by rw [e160, hF.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩,
      dataLoaded_win hd hreg hro (hF.widen R.rt) hw (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega),
      by rw [e160]; exact hout.of_sub (by omega) (by omega), by rw [e160, h28]; unfold Apart; omega,
      by rw [h28]; exact hgr, fun r hr => ?_, hro⟩, hty, hyc, hxc, hyc40, hxc40, hy40, hx40, hz40,
    fun hc => ?_, by simp only [win, outside_cons, outside_nil, and_true] at hzw' ⊢; rw [e160]; omega,
    fun hc => ?_, by rw [hF.accessible]; exact hyacc, hy48, hyh, hnorm _ _ (by omega) hyn,
    hnorm _ _ (by omega) hxn, by simp only [win, outside_cons, outside_nil, and_true]; rw [e160]; omega,
    by rw [hF.accessible]; exact hxacc, hx48, hxh, by simp only [win, outside_cons, outside_nil, and_true]; rw [e160]; omega,
    by rw [h28]; exact inv_frame_winA hF hout hb' (by omega) hinv, by rw [need_comm]; exact hok,
    by rw [mx_comm]; exact hmv⟩
  · rw [h28, hF.readLE _ _ (hFo _ _ (by omega)), e160]; omega
  · have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [e160]; omega
  · obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  · obtain ⟨hzg, hzx, hzy⟩ := hzw hc
    exact ⟨by rw [h28]; exact hzg, hzy, hzx⟩

set_option maxRecDepth 20000 in
/-- The callee's postcondition (about `S1`, operands swapped) is the caller's (about `s`); `s'` the return state. -/
theorem postS_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64)
    (h28 : S1.regs 28 = s.regs 28) (hF : MemFrame s.mem S1.mem (winA s 4464 80))
    (hq : PostS 4304 R b L zp zc yp yl xp xl S1 s') :
    PostS 4464 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := hpre.1.2.1.2.1
  have hLs := hpre.1.2.2.2.2.2.2.1
  have hxw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have e160 : S1.sp.toNat = s.sp.toNat - 160 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4464 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  obtain ⟨p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor, hmf, hlf⟩ := hq
  rw [h28] at hinv
  rw [need_comm] at hb
  refine ⟨p', n', c', h0, h1, h2, ?_, hn, hnc, by rw [mx_comm] at hnm; exact hnm, L', b', hext, hb, hinv, hl, hor,
    hF.trans hmf fun a n ho => ⟨?_, ?_⟩, ⟨fun a n hin hz => ?_⟩⟩
  · rw [hv, natVal_frame hF (hFo _ _ (by omega)), natVal_frame hF (hFo _ _ (by omega)), Nat.add_comm]
  · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho.1.2.1, ho.1.2.2⟩
  · simp only [outside_append, winA, outside_cons, outside_nil, and_true, e160] at ho ⊢
    obtain ⟨⟨hr, hw1, hw2⟩, hz⟩ := ho
    exact ⟨⟨hr, by omega, by omega⟩, hz⟩
  · rw [hlf.readLE a n hin hz]
    refine hF.readLE a n ?_
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
    simp only [winA, outside_cons, outside_nil, and_true]; omega

/-- `PostS` reads only the result registers and the memory of the final state. -/
theorem postS_congr {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64}
    {s s2 s3 : State} (h : PostS stk R b L zp zc xp xl yp yl s s2) (h0 : s3.regs 0 = s2.regs 0)
    (h1 : s3.regs 1 = s2.regs 1) (h2 : s3.regs 2 = s2.regs 2) (hm : s3.mem = s2.mem) :
    PostS stk R b L zp zc xp xl yp yl s s3 := by
  unfold PostS; rw [h0, h1, h2, hm]; exact h

theorem postR_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64)
    (h28 : S1.regs 28 = s.regs 28) (hF : MemFrame s.mem S1.mem (winA s 4464 80))
    (hq : PostR 4304 R b L zp zc yp yl xp xl S1 s') :
    PostR 4464 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hq, hr, hc⟩ := hq
  exact ⟨postS_swap hpre hsp h28 hF hq, fun h => hr (by rw [need_comm]; exact h),
    fun h => hc (by rw [mx_comm]; exact h)⟩

theorem postR_congr {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64}
    {s s2 s3 : State} (h : PostR stk R b L zp zc xp xl yp yl s s2) (h0 : s3.regs 0 = s2.regs 0)
    (h1 : s3.regs 1 = s2.regs 1) (h2 : s3.regs 2 = s2.regs 2) (hm : s3.mem = s2.mem) :
    PostR stk R b L zp zc xp xl yp yl s s3 := by
  unfold PostR PostS; rw [h0, h1, h2, hm]; exact h

theorem postR_mono {stk stk' : Nat} (hk : stk ≤ stk') {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl yp yl : BitVec 64} {s s' : State} (hsp : stk' ≤ s.sp.toNat)
    (h : PostR stk R b L zp zc xp xl yp yl s s') : PostR stk' R b L zp zc xp xl yp yl s s' :=
  ⟨postS_mono hk hsp h.1, h.2⟩

end FvModexp.Arm64.NatAdd
