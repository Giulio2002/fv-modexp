import FvModexp.Proofs.Arm64.Nat.RshMid
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.rsh` (arm64): `s = 0` with `cap z = 0`: `z.set(x)` = `makeslice` + `memmove(p, x, 8 len x)` + `RET`

From the join of `z.make(len x)` (`+0xd4`): `CMP R4, R1; CSEL LT` (`min = len x`), `CMP R0, R3; BEQ` (fresh `p ≠ x`),
spills `SP - 40 = c`, `SP - 48 = len x`, `SP - 16 = p`; `memmove`; reloads; `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

abbrev hJoinS : Nat := segAddr Extracted.program fn + 0xd4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyS (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl 0 s p c L' b' M) (hN : NatNorm s.mem x xl)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoinS) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 xl) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = BitVec.ofNat 64 x)
    (h4 : S.regs 4 = BitVec.ofNat 64 xl)
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl 0 s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hpx := h.px
  simp only [need, Nat.zero_div, Nat.sub_zero] at hcap
  unfold Apart at hpx
  have hxl0 := h.xl0; simp only [need, Nat.zero_div, Nat.sub_zero] at hxl0
  have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48
  have r1 := h.lr; have r2 := h.fp; have hsacc := h.sacc; have hal := h.al
  have hpacc : M.accessible p (8 * xl) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc := h.xacc
  have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw
  have hph : Held R L' p (8 * xl) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hph' : InRanges p (8 * xl) L' ∨ Outside p (8 * xl) R.rt := hph
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * xl] := fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc
  have hgok : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 144 := by rw [h.grd]; have := h.gok; omega
  have hw8 : 8 * (BitVec.ofNat 64 xl).toNat % 18446744073709551616 = 8 * xl := by
    simp only [BitVec.toNat_ofNat]; omega
  have hinvW : R.inv b' L' (s.regs 28).toNat (view R.rt L' (((M.writeLE (s.sp.toNat - 16) 8 p).writeLE
      (s.sp.toNat - 48) 8 xl).writeLE (s.sp.toNat - 40) 8 c)) :=
    inv_store_out (inv_store_out (inv_store_out h.inv (hwrt.of_sub (by omega) (by omega)))
      (hwrt.of_sub (by omega) (by omega))) (hwrt.of_sub (by omega) (by omega))
  have hLs2 : ∀ r ∈ L', (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 144 - 4096 ∨ s.sp.toNat - 144 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 144 + 8 ∨ s.sp.toNat - 144 + 8 + 24 ≤ r.1) := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  have hc' : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hl' : xl % 18446744073709551616 = xl := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, r1, r2, hw8, hc', hl'] calls [hmv]
  rename_i _ _ _ m _ _ hF2 hLF2 hinv2 hcp _
  have hW : MemFrame M (((M.writeLE (s.sp.toNat - 16) 8 p).writeLE (s.sp.toNat - 48) 8 xl).writeLE
      (s.sp.toNat - 40) 8 c) [(s.sp.toNat - 48, s.sp.toNat - 32), (s.sp.toNat - 16, s.sp.toNat - 8)] := by
    janus_frame
  have rdW : ∀ a k, (a + k ≤ s.sp.toNat - 48 ∨ s.sp.toNat - 8 ≤ a) →
      (((M.writeLE (s.sp.toNat - 16) 8 p).writeLE (s.sp.toNat - 48) 8 xl).writeLE
        (s.sp.toNat - 40) 8 c).readLE a k = M.readLE a k := fun a k h' =>
    hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hrd : ∀ a k, p ≤ a → a + k ≤ p + 8 * xl → m.readLE a k = s.mem.readLE (a - p + x) k := fun a k h1 h2 => by
    have hsub : Janus.Contracts.Mem.Copied _ m a (a - p + x) k := fun i hi => by
      have := hcp (a - p + i) (by omega)
      rw [show p + (a - p + i) = a + i by omega, show x + (a - p + i) = a - p + x + i by omega] at this
      exact this
    rw [Asm.readLE_of_copied hsub, rdW _ _ (by omega)]; exact h.xr _ _ (by omega) (by omega)
  have hv : natVal m p xl = natVal s.mem x xl / 2 ^ 0 := by
    simp only [natVal, Nat.pow_zero, Nat.div_one]; rw [hrd _ _ (Nat.le_refl _) (Nat.le_refl _)]; simp
  have hn : NatNorm m p xl := by
    rcases hN with h0 | h0
    · exact Or.inl h0
    · right; rw [hrd _ _ (by omega) (by omega), show p + 8 * (xl - 1) - p + x = x + 8 * (xl - 1) by omega]
      exact h0
  refine h.post (hW.trans hF2 fun a k ho => ?_) ⟨fun a k hin ho => ?_⟩ hinv2 _ xl ?hm2 ?_ ?_ ?_ hcap hv hn
  case hm2 => rfl
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2', h3'⟩ := ho
    and_intros <;> first | exact hr | omega
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hLF2.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
      rdW a k (by omega)]
  all_goals janus_simp

end FvModexp.Arm64.Rsh
