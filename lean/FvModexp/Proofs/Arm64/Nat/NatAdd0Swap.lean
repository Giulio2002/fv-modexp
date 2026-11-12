import FvModexp.Proofs.Arm64.Nat.NatAddSwap
import FvModexp.Proofs.Arm64.Nat.NatAdd0Defs

set_option autoImplicit false

/-!
# `nat.add` (arm64), empty-tolerant: the self-call `z.add(y, x)` (`len x < len y`) under `PreS0`

`preS0_swap`, `postS_swap0`, `postR_swap0`, `postX_swap0`: the `NatAddSwap` lemmas with `PreS0` (an empty `x`
carries no location fact; its value is `0` in every memory).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatAdd

set_option maxRecDepth 20000 in
theorem preS0_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s S1 : State}
    (hpre : PreS0 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64) (h28 : S1.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S1.mem (winA s 4464 80)) (hreg : S1.mem.regions = s.mem.regions) :
    PreS0 4304 R b L zp zc yp yl yc xp xl xc S1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, hyn, hxw, hyacc, hy48, hyh, hyw, hinv, hok, hmv⟩ := hpre
  have e160 : S1.sp.toNat = s.sp.toNat - 160 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold Apart at hga
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4464 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hnorm : ∀ p n, (0 < n → (p + 8 * n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 80 ≤ p)) → NatNorm s.mem p n →
      NatNorm S1.mem p n := by
    intro p n ho hn
    rcases hn with h0 | h0
    · exact Or.inl h0
    · by_cases hn0 : n = 0
      · exact Or.inl hn0
      · right; rw [hF.readLE _ _ (hFo _ _ (by have := ho (by omega); omega))]; exact h0
  refine ⟨?ce, hty, hyc, hxc, hyc40, hxc40, hy40, hx40, hz40, ?nl, ?zo, ?za, ?ya, hy48, hyh, ?yn, ?xn, ?yw, ?xa, hx48,
    hxh, ?xw, ?inv, ?ok, ?mv⟩
  case ce =>
    clear hyacc hxacc hy48 hx48 hyh hxh hyw hxw hzw' hzw hzl hnorm hok hmv hinv hyn hxn
    refine ⟨⟨by rw [h28]; exact hg1, by rw [h28, hF.accessible]; exact hg2, ?_⟩,
      ⟨by rw [e160]; omega, by rw [e160]; omega, by rw [e160]; omega,
        by rw [e160, hF.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩,
      dataLoaded_win hd hreg hro (hF.widen R.rt) hw (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega),
      by rw [e160]; exact hout.of_sub (by omega) (by omega), by rw [e160, h28]; unfold Apart; omega,
      by rw [h28]; exact hgr, fun r hr => ?_, hro⟩
    · rw [h28, hF.readLE _ _ (hFo _ _ (by omega)), e160]; omega
    · have := hLs r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [e160]; omega
  case nl =>
    intro hc
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  case zo =>
    simp only [win, outside_cons, outside_nil, and_true] at hzw' ⊢; rw [e160]; omega
  case za =>
    intro hc
    obtain ⟨hzg, hzx, hzy⟩ := hzw hc
    exact ⟨by rw [h28]; exact hzg, hzy, hzx⟩
  case ya => intro h; rw [hF.accessible]; exact hyacc h
  case yn => exact hnorm _ _ (fun h => by have := hyw h; omega) hyn
  case xn => exact hnorm _ _ (fun h => by have := hxw h; omega) hxn
  case yw =>
    intro h; have := hyw h; simp only [win, outside_cons, outside_nil, and_true]; rw [e160]; omega
  case xa => intro h; rw [hF.accessible]; exact hxacc h
  case xw =>
    intro h; have := hxw h; simp only [win, outside_cons, outside_nil, and_true]; rw [e160]; omega
  case inv => rw [h28]; exact inv_frame_winA hF hout hb' (by omega) hinv
  case ok => rw [need_comm]; exact hok
  case mv => rw [mx_comm]; exact hmv

/-- an operand's value survives the frame of the self-call (empty: `0` everywhere) -/
theorem natVal_swap0 {s : State} {M : Memory} {p n : Nat} (hF : MemFrame s.mem M (winA s 4464 80))
    (ho : 0 < n → (p + 8 * n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 80 ≤ p)) : natVal M p n = natVal s.mem p n := by
  by_cases hn : n = 0
  · subst hn; rfl
  · refine natVal_frame hF ?_
    have := ho (by omega)
    simp only [winA, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- The callee's postcondition (about `S1`, operands swapped) is the caller's (about `s`); `s'` the return state. -/
theorem postS_swap0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS0 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64)
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
  obtain ⟨p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor, hmf, hlf⟩ := hq
  rw [h28] at hinv
  rw [need_comm] at hb
  refine ⟨p', n', c', h0, h1, h2, ?_, hn, hnc, by rw [mx_comm] at hnm; exact hnm, L', b', hext, hb, hinv, hl, hor,
    hF.trans hmf fun a n ho => ⟨?_, ?_⟩, ⟨fun a n hin hz => ?_⟩⟩
  · rw [hv, natVal_swap0 hF (fun h => by have := hyw h; omega), natVal_swap0 hF (fun h => by have := hxw h; omega),
      Nat.add_comm]
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

theorem postR_swap0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS0 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64)
    (h28 : S1.regs 28 = s.regs 28) (hF : MemFrame s.mem S1.mem (winA s 4464 80))
    (hq : PostR 4304 R b L zp zc yp yl xp xl S1 s') :
    PostR 4464 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hq, hr, hc⟩ := hq
  exact ⟨postS_swap0 hpre hsp h28 hF hq, fun h => hr (by rw [need_comm]; exact h),
    fun h => hc (by rw [mx_comm]; exact h)⟩

set_option maxRecDepth 20000 in
theorem postX_swap0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS0 4464 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.sp = s.sp - 160#64)
    (h28 : S1.regs 28 = s.regs 28) (hF : MemFrame s.mem S1.mem (winA s 4464 80))
    (hq : PostX 4304 R b L zp zc yp yl xp xl S1 s') :
    PostX 4464 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hq, hmf, hlf⟩ := hq
  have hsp0 := hpre.1.2.1.2.1
  have hLs := hpre.1.2.2.2.2.2.2.1
  have e160 : S1.sp.toNat = s.sp.toNat - 160 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have em : max yl.toNat xl.toNat = max xl.toNat yl.toNat := Nat.max_comm _ _
  rw [em] at hmf hlf
  refine ⟨postR_swap0 hpre hsp h28 hF hq, hF.trans hmf fun a n ho => ⟨?_, ?_⟩, ⟨fun a n hin hz => ?_⟩⟩
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

end FvModexp.Arm64.NatAdd
