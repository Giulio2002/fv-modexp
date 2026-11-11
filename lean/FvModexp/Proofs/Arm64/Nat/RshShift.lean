import FvModexp.Proofs.Arm64.Nat.RshFin
import FvModexp.Proofs.Arm64.Nat.Callees2
import FvModexp.Proofs.Arm64.Nat.LshShiftF

/-!
# `nat.rsh` (arm64): the `s % 64 ≠ 0` path from the join (`+0x1ac`) to the norm head

Spills `SP - 64 = c`, `SP - 72 = n`, `SP - 24 = p`; `CBNZ R6` (taken, `R6 = s % 64`); frame arguments
`8 … 56(RSP')` = `(p, n, c, x + 8 (s/64), n, cap x - s/64, s % 64)`; `CALL rshVU.abi0` (`+0x238`); reloads; to `hNorm`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

abbrev callRsh : Nat := segAddr Extracted.program fn + 0x238

set_option maxRecDepth 20000 in
/-- memory facts after `rshVU` (pure) -/
theorem shift_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M C w : Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M C [(s.sp.toNat - 136, s.sp.toNat - 80), (s.sp.toNat - 72, s.sp.toNat - 56),
      (s.sp.toNat - 24, s.sp.toNat - 16)])
    (hQ1 : natVal w p (xl - sh / 64) = natVal C (x + sh / 64 * 8) (xl - sh / 64) / 2 ^ (sh % 64))
    (hQ3 : MemFrame C w [(p, p + 8 * (xl - sh / 64)), (s.sp.toNat - 80, s.sp.toNat - 72)]) :
    MemFrame M w (R.rt ++ ws s p c) ∧ LiveFrame M w L' [(p, p + 8 * c)] ∧
    natVal w p (need xl sh) = natVal s.mem x xl / 2 ^ sh := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt; have hn0 := h.xl0
  simp only [need] at hcap hn0
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  refine ⟨hF.trans hQ3 fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2', h3'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hQ3.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · simp only [need]
    rw [hQ1, show x + sh / 64 * 8 = x + 8 * (sh / 64) by omega, val_hi, show sh / 64 + (xl - sh / 64) = xl by omega]
    have e : natVal C x xl = natVal s.mem x xl := by
      simp only [natVal]
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact h.xr _ _ (Nat.le_refl _) (Nat.le_refl _)
    rw [e, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * (sh / 64) + sh % 64 = sh by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `CALL rshVU.abi0` (state `C`) to the norm head, then `fromNorm` -/
theorem shiftC (impl : List Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0)
    (C : State) (hpc : C.pc = BitVec.ofNat 64 callRsh) (hsp : C.sp = s.sp - 144#64) (h28 : C.regs 28 = s.regs 28)
    (h29 : C.regs 29 = s.sp - 152#64) (h18 : C.regs 18 = s.regs 18)
    (hF : MemFrame M C.mem [(s.sp.toNat - 136, s.sp.toNat - 80), (s.sp.toNat - 72, s.sp.toNat - 56),
      (s.sp.toNat - 24, s.sp.toNat - 16)])
    (k1 : C.mem.readLE (s.sp.toNat - 144 + 8) 8 = p)
    (k2 : C.mem.readLE (s.sp.toNat - 144 + 16) 8 = xl - sh / 64)
    (k3 : C.mem.readLE (s.sp.toNat - 144 + 32) 8 = x + sh / 64 * 8)
    (k4 : C.mem.readLE (s.sp.toNat - 144 + 56) 8 = sh % 64)
    (k5 : C.mem.readLE (s.sp.toNat - 24) 8 = p) (k6 : C.mem.readLE (s.sp.toNat - 64) 8 = c)
    (k7 : C.mem.readLE (s.sp.toNat - 72) 8 = xl - sh / 64)
    (hinvC : R.inv b' L' (s.regs 28).toNat (view R.rt L' C.mem)) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) C fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hn0 := h.xl0; have hal := h.al; have hx48 := h.x48
  have hwrt := h.wrt; have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpx := h.px
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  simp only [need] at hcap hn0
  unfold Apart at hpw hgw hpg hpx
  have hzacc : C.mem.accessible p (8 * (xl - sh / 64)) true = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : C.mem.accessible (x + sh / 64 * 8) (8 * (xl - sh / 64)) false = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ h.xacc (by omega) (by omega)
  have hsacc : C.mem.accessible (s.sp.toNat - 4240) (4240 + 64) true = true := by rw [hF.accessible]; exact h.sacc
  have hzH : Held R L' p (8 * (xl - sh / 64)) := h.pheld.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 144 + 64) 8 R.rt := hwrt.of_sub (by omega) (by omega)
  have hzg : Apart p (8 * (xl - sh / 64)) ((s.regs 28).toNat + 16) 8 := by unfold Apart; omega
  have hrg : Apart (s.sp.toNat - 144 + 64) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart; omega
  have hzr : Apart p (8 * (xl - sh / 64)) (s.sp.toNat - 144 + 64) 8 := by unfold Apart; omega
  have hxr : Apart (x + sh / 64 * 8) (8 * (xl - sh / 64)) (s.sp.toNat - 144 + 64) 8 := by unfold Apart; omega
  have halx : p ≤ x + sh / 64 * 8 ∨ Apart p (8 * (xl - sh / 64)) (x + sh / 64 * 8) (8 * (xl - sh / 64)) := by
    right; unfold Apart; omega
  have hr1 : 1 ≤ sh % 64 := by omega
  have hr63 : sh % 64 ≤ 63 := by omega
  janus_run [k1, k2, k3, k4] until [callRsh + 4] calls [hRsh b' L']
  rename_i w hq hinvw _
  have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold RshVUSum.Q at hq
  rw [e144, k1, k2, k3, k4] at hq
  obtain ⟨q1, -, q3⟩ := hq
  dsimp only at q1 q3
  have e80 : s.sp.toNat - 144 + 64 = s.sp.toNat - 80 := by omega
  have e72 : s.sp.toNat - 144 + 72 = s.sp.toNat - 72 := by omega
  try rw [e80] at q3
  try rw [e72] at q3
  obtain ⟨hF1, hLF1, hval⟩ := shift_facts h hF q1 q3
  have rw' : ∀ a, (s.sp.toNat - 72 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → w.readLE a 8 = C.mem.readLE a 8 := fun a ha =>
    q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have w5 := (rw' _ (by omega)).trans k5
  have w6 := (rw' _ (by omega)).trans k6
  have w7 := (rw' _ (by omega)).trans k7
  have hsacc' : w.accessible (s.sp.toNat - 4240) (4240 + 64) true = true := by rw [q3.accessible]; exact hsacc
  janus_run [w5, w6, w7] until [hNorm]
  refine fromNorm impl b R L zp zc x xl sh s p c L' b' M h w hF1 hLF1 hinvw hval _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem shiftA (impl : List Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh) (h7 : S.regs 7 = BitVec.ofNat 64 (need xl sh))
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48; have hn0 := h.xl0; have hal := h.al; have hsacc := h.sacc
  simp only [need] at hcap hn0 h1 h7
  have hsh : sh < 2 ^ 64 := by omega
  have hr := Lsh.and63 sh hsh
  have hr' : (BitVec.ofNat 64 (sh % 64) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hq : sh / 64 < xl := by omega
  have hmk := xmask xl xc (sh / 64) hq hxc hxc'
  have hxq : (x + 8 * (sh / 64)) % 18446744073709551616 = x + 8 * (sh / 64) := Nat.mod_eq_of_lt (by omega)
  have hwrt := h.wrt
  have hsa := sub_add_sub xl (xl - sh / 64) (by omega) (by omega)
  janus_run [hm, hr, hr', hmk, hxq, hsa] until [callRsh]
  refine shiftC impl R hRsh b L zp zc x xl sh s p c L' b' M h hr0 _ ?_ ?_ ?_ ?_ ?_ ?F ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?inv
  case F => janus_frame
  case inv =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 136, s.sp.toNat - 80), (s.sp.toNat - 72, s.sp.toNat - 56),
      (s.sp.toNat - 24, s.sp.toNat - 16)]) (by janus_frame) (fun r hr => ?_) h.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (left; exact hwrt.of_sub (by omega) (by omega))
  all_goals janus_simp

end FvModexp.Arm64.Rsh
