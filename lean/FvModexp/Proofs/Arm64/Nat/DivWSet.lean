import FvModexp.Proofs.Arm64.Nat.DivWMid
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.divW` (arm64): `case y == 1: q = z.set(x)` (`m > 0`), from `+0x174` (after `z.make(m)`)

`z.set(x)` (nat.go:92) = `z = z.make(len(x)); copy(z, x); return z`. At `+0x174` (the join of the reuse and the two
`makeslice` paths): `R0 = p`, `R1 = m`, `R2 = c`, `R3 = xp`, `R4 = m`. `CMP R4, R1; CSEL LT, R1, R4, R5` (`min`);
`CMP R0, R3; BEQ` (Go's `copy` skips `memmove` when the pointers agree); spills to `112/128/104(RSP')`
(`SP - 32, -16, -40`); `memmove(p, xp, 8 m)`; `return z[:m], 0`. The result is normalised because `x` is.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivW

abbrev hSet : Nat := segAddr Extracted.program fn + 0x174

theorem div_one (n : Nat) : n / (1#64 : BitVec 64).toNat = n := by simp
theorem mod_one (n : Nat) : n % (1#64 : BitVec 64).toNat = 0 := by simp [Nat.mod_one]

/-- **The postcondition of the `z.set(x)` path** from the final memory `M'`: `M` changed by the window and (when
`p ≠ xp`) the copy into `p[:m]`. -/
theorem Mid.setPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hxv : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (hxn : M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0)
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 4240, s.sp.toNat - 8), (p, p + 8 * xl.toNat)]))
    (hLF : LiveFrame M M' L' [(p, p + 8 * xl.toNat)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M'))
    (hcp : M'.readLE p (8 * xl.toNat) = M.readLE xp.toNat (8 * xl.toNat))
    (hnz : M'.readLE (p + 8 * (xl.toNat - 1)) 8 = M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8)
    (s' : State) (hm : s'.mem = M') (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 1).toNat = xl.toNat)
    (h2 : (s'.regs 2).toNat = c) (h3 : (s'.regs 3).toNat = 0) :
    Post R b L zp zc xp xl 1#64 s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  refine ⟨p, xl.toNat, c, h0, h1, h2, by rw [h3, mod_one], ?_, Or.inr ?_, hcap, Nat.le_refl _, L', b', h.ext, h.bud,
    hinv, fun _ => ⟨h.p8, h.pheld, by rw [hF.accessible]; exact h.pacc, h.p48⟩, h.ror, ?_, ?_⟩
  · rw [div_one, show natVal s'.mem p xl.toNat = s'.mem.readLE p (8 * xl.toNat) from rfl, hcp]; exact hxv
  · rw [hnz]; exact hxn
  · refine h.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1, hw2⟩, hz⟩ := ho
    refine ⟨hrt, by omega, ?_⟩
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · omega
    · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n (h.ext.inRanges_old hin) ?_]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      simp only [outside_cons, outside_nil, and_true] at hz ⊢
      rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
      · omega
      · have := hap q hq; unfold Apart at this; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem setTail (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hxv : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (hxn : M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = xl) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = xp) (h4 : S.regs 4 = xl)
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl 1#64 s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hx0 := h.x0; have hx48 := h.x48
  have r1 := h.lr; have r2 := h.fp; have hsacc := h.sacc; have hal := h.al; have hinv := h.inv
  have hpacc : M.accessible p (8 * xl.toNat) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc := h.xacc; have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hxw := h.xw; have hgw := h.gw
  unfold Apart at hpw hxw hgw
  have hph : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * xl.toNat] := fun d src => h.mv d src _ (Nat.le_refl _)
  have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc
  have hgok : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 144 := by rw [h.grd]; have := h.gok; omega
  have hph' : InRanges p (8 * xl.toNat) L' ∨ Outside p (8 * xl.toNat) R.rt := hph
  janus_run [hm, r1, r2, Nat.mod_eq_of_lt (by omega : c < 18446744073709551616)] calls [hmv]
  · -- `p = xp`: no copy
    rename_i hpx _
    refine h.setPost hxv hxn (MemFrame.refl _ _) ⟨fun _ _ _ _ => rfl⟩ h.inv (by rw [hpx]) (by rw [hpx]) _ rfl ?_ ?_ ?_
      ?_
    all_goals janus_simp
  · rename_i _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp _
    have hcp' := Asm.readLE_of_copied hcp
    have hsub : Mem.Copied _ m (p + 8 * (xl.toNat - 1)) (xp.toNat + 8 * (xl.toNat - 1)) 8 := fun i hi => by
      have := hcp (8 * (xl.toNat - 1) + i) (by omega)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at this; exact this
    have hnz' := Asm.readLE_of_copied hsub
    have hW : MemFrame M (((M.writeLE (s.sp.toNat - 32) 8 c).writeLE (s.sp.toNat - 16) 8 p).writeLE
        (s.sp.toNat - 40) 8 xl.toNat) [(s.sp.toNat - 40, s.sp.toNat - 24), (s.sp.toNat - 16, s.sp.toNat - 8)] := by
      janus_frame
    have rdW : ∀ a n, (a + n ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 8 ≤ a) →
        (((M.writeLE (s.sp.toNat - 32) 8 c).writeLE (s.sp.toNat - 16) 8 p).writeLE
          (s.sp.toNat - 40) 8 xl.toNat).readLE a n = M.readLE a n := fun a n h' =>
      hW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
    refine h.setPost hxv hxn (hW.trans hF2 fun a n ho => ?_) ⟨fun a n hin ho => ?_⟩ hinv2 ?_ ?_ _ rfl ?_ ?_ ?_ ?_
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2'⟩ := ho
      and_intros <;> first | exact hr | omega
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this
      rw [hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ ho, rdW a n (by omega)]
    · rw [hcp', rdW _ _ (by omega)]
    · rw [hnz', rdW _ _ (by omega)]
    all_goals janus_simp

end FvModexp.Arm64.DivW
