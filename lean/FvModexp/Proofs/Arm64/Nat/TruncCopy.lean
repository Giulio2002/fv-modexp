import FvModexp.Proofs.Arm64.Nat.TruncMask
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.trunc` (arm64): main path from the join of `z.make(w)` (`+0xa0`) to `TST` (`+0xd8`), then `fromTst`

`CMP R1, R4; CSEL LT, R4, R1, R4` (`min(len x, w) = w`); `CMP R0, R3; BEQ` (Go's `copy` skips `memmove` when the
pointers agree); spills `SP - 24, -72, -64`; `memmove(p, x, 8 w)`; reloads.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Trunc

abbrev hJoin : Nat := segAddr Extracted.program fn + 0xa0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyM (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl n s (wOf n) p c L' b' M) (hw : wOf n ≤ xl)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (wOf n)) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = BitVec.ofNat 64 x)
    (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) (hk : wOf n = EvenHyp.truncNeed xl n) (hn : n ≤ 2 ^ 20) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48; have hc0 := h.c0
  have r1 := h.lr; have r2 := h.fp; have rn := h.sn rfl; have hsacc := h.sacc; have hal := h.al
  have hpacc : M.accessible p (8 * wOf n) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc : M.accessible x (8 * wOf n) false = true := Memory.accessible_mono _ h.xacc (Nat.le_refl _) (by omega)
  have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw
  have hph : Held R L' p (8 * wOf n) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hph' : InRanges p (8 * wOf n) L' ∨ Outside p (8 * wOf n) R.rt := hph
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * wOf n] := fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc
  have hgok : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 112 := by rw [h.grd]; have := h.gok; omega
  have hmin : (if (xl : Int) < (wOf n : Int) then BitVec.ofNat 64 xl else BitVec.ofNat 64 (wOf n)) =
      BitVec.ofNat 64 (wOf n) := by rw [if_neg (by omega)]
  have hw8 : 8 * (BitVec.ofNat 64 (wOf n)).toNat % 18446744073709551616 = 8 * wOf n := by
    simp only [BitVec.toNat_ofNat]; omega
  have hinvW : R.inv b' L' (s.regs 28).toNat (view R.rt L' (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE
      (s.sp.toNat - 72) 8 (wOf n)).writeLE (s.sp.toNat - 64) 8 c)) :=
    inv_store_out (inv_store_out (inv_store_out h.inv (hwrt.of_sub (by omega) (by omega)))
      (hwrt.of_sub (by omega) (by omega))) (hwrt.of_sub (by omega) (by omega))
  have hLs2 : ∀ r ∈ L', (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 112 - 4096 ∨ s.sp.toNat - 112 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 112 + 8 ∨ s.sp.toNat - 112 + 8 + 24 ≤ r.1) := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  have hxpre : M.readLE x (8 * wOf n) = natVal s.mem x xl % 2 ^ (64 * wOf n) := by
    rw [← Memory.readLE_mod M x (8 * xl) (8 * wOf n) (by omega), h.xr _ _ (Nat.le_refl _) (Nat.le_refl _),
      show (256 : Nat) ^ (8 * wOf n) = 2 ^ (64 * wOf n) by
        rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega]
  janus_run [hm, r1, r2, rn, hmin, hw8, Nat.mod_eq_of_lt (by omega : c < 18446744073709551616)] until [hTst] calls [hmv]
  · refine fromTst impl R b L zp zc x xl n s p c L' b' M h hk hn M (MemFrame.refl _ _) (LiveFrame.refl _ _ _) h.inv
      ?val _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case val => rw [← hbr]; exact hxpre
    all_goals janus_simp
  · rename_i _ _ _ m _ _ hF2 hLF2 hinv2 hcp
    have hcp' := Asm.readLE_of_copied hcp
    have hW : MemFrame M (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 72) 8 (wOf n)).writeLE
        (s.sp.toNat - 64) 8 c) [(s.sp.toNat - 72, s.sp.toNat - 56), (s.sp.toNat - 24, s.sp.toNat - 16)] := by
      janus_frame
    have rdW : ∀ a k, (a + k ≤ s.sp.toNat - 72 ∨ s.sp.toNat - 16 ≤ a) →
        (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 72) 8 (wOf n)).writeLE
          (s.sp.toNat - 64) 8 c).readLE a k = M.readLE a k := fun a k h' =>
      hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
    refine fromTst impl R b L zp zc x xl n s p c L' b' M h hk hn m (hW.trans hF2 fun a k ho => ?_)
      ⟨fun a k hin ho => ?_⟩ hinv2 ?val _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case val => show m.readLE p (8 * wOf n) = _; rw [hcp', rdW _ _ (by omega)]; exact hxpre
    · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2', h3'⟩ := ho
      and_intros <;> first | exact hr | omega
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this ho
      rw [hLF2.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
        rdW a k (by omega)]
    all_goals janus_simp

end FvModexp.Arm64.Trunc
