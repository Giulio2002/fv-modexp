import FvModexp.Proofs.Arm64.Nat.TruncNorm
import FvModexp.Proofs.Common.TruncMath

/-!
# `nat.trunc` (arm64): main path from `TST $63, R6` (`+0xd8`) to the return

`if n % 64 != 0 { z[w-1] &= 1<<(n%64) - 1 }` (`+0xe0 … +0x100`), `JMP norm`; the norm loop (`norm`) and the
postcondition (`Mid.post`). `fromTst` takes the memory `M2` after the copy with its frame facts relative to `Mid`'s `M`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Trunc

abbrev hTst : Nat := segAddr Extracted.program fn + 0xd8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `TST $63, R6`; the top-word mask when `n % 64 ≠ 0`; to the norm loop head -/
theorem maskT (impl : List Segment) (s : State) (M2 : Memory) (p c n : Nat) (Q : State → Prop)
    (k : ∀ S' : State, S'.pc = BitVec.ofNat 64 hNorm → S'.regs 0 = BitVec.ofNat 64 p →
      S'.regs 1 = BitVec.ofNat 64 (wOf n) → S'.regs 2 = BitVec.ofNat 64 c → S'.sp = s.sp - 112#64 →
      S'.regs 28 = s.regs 28 → S'.regs 29 = s.sp - 120#64 → S'.regs 18 = s.regs 18 →
      MemFrame M2 S'.mem [(p + 8 * (wOf n - 1), p + 8 * wOf n)] →
      natVal S'.mem p (wOf n) = natVal M2 p (wOf n) % 2 ^ n →
      ReachesRet (LibTrunc.program.link impl) (s.regs 30) S' Q)
    (hn : n ≤ 2 ^ 20) (hc : wOf n ≤ c) (hc40 : c < 2 ^ 40) (hp : p + 8 * c ≤ 2 ^ 48)
    (hacc : M2.accessible p (8 * c) true = true)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hTst) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (wOf n)) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M2) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) S Q := by
  by_cases h64 : n % 64 = 0
  · have hlt : natVal M2 p (wOf n) < 2 ^ n := by
      have := natVal_lt M2 p (wOf n); rwa [show 64 * wOf n = n by unfold wOf; omega] at this
    janus_run [hm] until [hNorm]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?v
    case v => exact (Nat.mod_eq_of_lt hlt).symm
    all_goals janus_simp
  · have hw1 : 1 ≤ wOf n := by unfold wOf; omega
    have hpacc : M2.accessible p (8 * wOf n) true = true := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    janus_run [hm] until [hNorm]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?fr ?v
    case fr => janus_frame
    case v =>
      dsimp only
      rw [TruncMath.mask_val _ _ _ _ hw1 (by omega) (by omega), show 64 * (wOf n - 1) + n % 64 = n by
        unfold wOf; omega]
    all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `TST` (memory `M2` after the copy) to the return, with the postcondition -/
theorem fromTst (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl n s (wOf n) p c L' b' M) (hk : wOf n = EvenHyp.truncNeed xl n) (hn : n ≤ 2 ^ 20)
    (M2 : Memory) (hF1 : MemFrame M M2 (R.rt ++ ws s p c)) (hLF1 : LiveFrame M M2 L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 28).toNat (view R.rt L' M2))
    (hval : natVal M2 p (wOf n) = natVal s.mem x xl % 2 ^ (64 * wOf n))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hTst) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (wOf n)) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M2) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hsp0 := h.sp0; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48; have hpw := h.pw
  unfold Apart at hpw
  have hws : ∀ a n, (s.sp.toNat - 120 ≤ a ∧ a + n ≤ s.sp.toNat - 104) → Outside a n (R.rt ++ ws s p c) := by
    intro a n ha
    simp only [ws, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h.wrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
  refine maskT impl s M2 p c n _ (fun S' hpc' h0' h1' h2' hsp' h28' h29' h18' hF3 hv3 => ?_) hn hcap hc40 hp48
    (by rw [hF1.accessible]; exact h.pacc) S hpc h0 h1 h2 h6 hsp h28 h29 h18 hm
  have hF : MemFrame M S'.mem (R.rt ++ ws s p c) := hF1.trans hF3 fun a n ho => ⟨ho, by
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
  have hc41 : c < 2 ^ 41 := by omega
  have hpw' : p + 8 * wOf n ≤ 2 ^ 48 := by omega
  have hpa : S'.mem.accessible p (8 * wOf n) false = true := by
    rw [hF.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega))
  refine norm impl s S'.mem p c (wOf n) (natVal s.mem x xl % 2 ^ n) _ ?fin hcap hc41 hpw'
    hpa
    (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.lr) (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.fp)
    h.al h.sp0 h.sp1 (by rw [hF.accessible]; exact h.sacc) h.lr4 h.lr48 (wOf n) S' (Nat.le_refl _) hpc' h1' h0' h2'
    hsp' h28' h29' h18' rfl ?v
  case v =>
    rw [hv3, hval, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by unfold wOf; omega))]
  case fin =>
    intro s' n' hm' h0'' h1'' h2'' hn' hv' hN
    refine h.post hk hF ?_ ?_ s' n' hm' h0'' h1'' h2'' (by omega) hv' hN
    · refine hLF1.trans ⟨fun a k hin hout => hF3.readLE a k ?_⟩ fun _ _ hh => hh
      simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
    · refine RtInv.inv_frame' hF3 (fun r hr => ?_) hinv2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      have hsub : Held R L' (p + 8 * (wOf n - 1)) (p + 8 * wOf n - (p + 8 * (wOf n - 1))) :=
        h.pheld.sub (by omega) (by omega)
      dsimp only
      rcases hsub with hin | hout
      · exact Or.inr hin
      · exact Or.inl hout

end FvModexp.Arm64.Trunc
