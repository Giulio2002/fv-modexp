import FvModexp.Proofs.Arm64.Exp.IExpA
import FvModexp.Proofs.Common.DivmcMem
import FvModexp.Proofs.Arm64.Top.RunIface

/-!
# `(*Int).exp` (arm64), segment D: from the return of `nat.expNN` to `RET` (int.go:599-607; fn+0x2dc .. fn+0x398)

`z.abs = (p, l, c)`: the `len, cap` stores at `z + 16`, the write-barrier flag test (barrier on: `gcWriteBarrier2`, its
buffer stores), the `ptr` store at `z + 8`; `z.neg = len > 0 && x.neg && …` with `x = z` and `x.neg = false` (the byte
at `z` is still `0`), so `0` is stored; the epilogue returns `z`. Adapted from divmc's `IntAS.tail` (IntASTail.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IExp

/-- `z`'s header after the `len, cap` stores -/
@[reducible] def hdrW (M : Memory) (zA l c : Nat) : Memory := (M.writeLE (zA + 16) 8 l).writeLE (zA + 24) 8 c

theorem hl0_of {l : Nat} (h : l = 0) : l = 0 := h

theorem wbCallE {p : Program} {R : RtInv} (hwb : WbLiveContract p (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {L1 : List (Nat × Nat)} {b1 : Nat} {S : State} {ret : BitVec 64} {Q : State → Prop}
    (hpc : S.pc = BitVec.ofNat 64 (cA "runtime.gcWriteBarrier2")) (hcall : CallOK S 4096 0)
    (hok : R.ok (cA "runtime.gcWriteBarrier2") [2]) (hinv : R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 S.mem))
    (hLW : LiveSep L1 [(S.sp.toNat - 4096, S.sp.toNat - 8)]) (hWR : LiveSep [(S.sp.toNat - 4096, S.sp.toNat - 8)] R.rt)
    (K : ∀ (buf : BitVec 64) (junk : Nat → BitVec 64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
      (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      MemFrame S.mem m (R.rt ++ [(S.sp.toNat - 4096, S.sp.toNat - 8)]) → LiveFrame S.mem m L1 [] →
      WbSlots R.rt m buf.toNat 2 → ApartAll buf.toNat (8 * 2) L1 →
      ApartAll buf.toNat (8 * 2) [(S.sp.toNat - 4096, S.sp.toNat - 8)] →
      InvSlots R b1 L1 (S.regs 28).toNat R.rt m buf.toNat 2 →
      ReachesRet p ret (wbRetX S junk buf f v m ex ep) Q) :
    ReachesRet p ret S Q := by
  refine ReachesRet.call (hwb L1 b1) hpc ⟨hcall, hok, hinv, hLW, hWR⟩ fun S2 _ hq => ?_
  obtain ⟨buf, junk, f, v, m, ex, ep, rfl, hfr, hlf, hsl, hapL, hapW, hinvS⟩ := hq
  exact K buf junk f v m ex ep hfr hlf hsl hapL hapW hinvS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runD (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibExp.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0) (F : State → Prop)
    (t zA p l c : Nat) (r29 : BitVec 64) (b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (hal : t % 16 = 0) (ht1 : 4448 ≤ t) (ht2 : t + 48 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (t - 4416) (4416 + 48) true = true)
    (hrt : Outside (t - 4416) (4416 + 48) R.rt) (hLs : LiveSep L1 [(t - 4416, t + 48)])
    (hwbA : S.mem.accessible RunIface.wbA 4 false = true) (hwbz : RunIface.wbA + 4 ≤ zA ∨ zA + 32 ≤ RunIface.wbA)
    (hwbs : RunIface.wbA + 4 ≤ t - 4416 ∨ t + 48 ≤ RunIface.wbA)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : S.mem.accessible zA 32 true = true) (hzS : zA + 32 ≤ t - 4416 ∨ t + 48 ≤ zA)
    (hzH : Held R L1 zA 32)
    (hok : R.ok (cA "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 S.mem))
    (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 raN) (hsp : S.sp = BitVec.ofNat 64 (t - 320))
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 l) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h29 : S.regs 29 = BitVec.ofNat 64 (t - 328))
    (hzs : S.mem.readLE (t + 8) 8 = zA) (hxs : S.mem.readLE (t + 16) 8 = zA)
    (hfp : S.mem.readLE (t - 328) 8 = r29.toNat) (hlr : S.mem.readLE (t - 320) 8 = ret0)
    (hng : S.mem.readLE zA 1 = 0)
    (KF : ∀ (s4 : State) (Mw : Memory),
      MemFrame (hdrW S.mem zA l c) Mw (R.rt ++ [(t - 4416, t - 328)]) → LiveFrame (hdrW S.mem zA l c) Mw L1 [] →
      R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 Mw) →
      s4.mem = (Mw.writeLE (zA + 8) 8 p).writeLE zA 1 0 → s4.sp = BitVec.ofNat 64 t →
      s4.regs 0 = BitVec.ofNat 64 zA → s4.regs 18 = S.regs 18 → s4.regs 28 = S.regs 28 → s4.regs 29 = r29 → F s4) :
    Reaches ((LibExp.program.link impl).withExit ret0) S (IsReturn F) := by
  have hr48 := hret.user
  have hspN : S.sp.toNat = t - 320 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have es1 : BitVec.ofNat 64 (t - 320) + 320#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 320) - 8#64 = BitVec.ofNat 64 (t - 328) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hr29 : r29.toNat < 2 ^ 64 := r29.isLt
  have hwbv : RunIface.wbA = 7616064 := rfl
  rw [hwbv] at hwbz hwbs hwbA
  have hinv0 : R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 (hdrW S.mem zA l c)) := by
    simp only [hdrW]
    rw [view_writeLE_held (hzH.sub (by omega) (by omega)), view_writeLE_held (hzH.sub (by omega) (by omega))]
    exact hinv
  have hb : (BitVec.ofNat 64 r29.toNat) = r29 := by simp
  have hzs' : S.mem.readLE (t - 320 + 328) 8 = zA := by rw [show t - 320 + 328 = t + 8 by omega]; exact hzs
  have hxs' : S.mem.readLE (t - 320 + 336) 8 = zA := by rw [show t - 320 + 336 = t + 16 by omega]; exact hxs
  have hlr' : S.mem.readLE (t - 328 + 8) 8 = ret0 := by rw [show t - 328 + 8 = t - 320 by omega]; exact hlr
  have hLW : LiveSep L1 [(t - 320 - 4096, t - 320 - 8)] := fun r hr => by
    have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hWR : LiveSep [(t - 320 - 4096, t - 320 - 8)] R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hrt.of_sub (by omega) (by simp only; omega)
  janus_run [es1, es2, hb, hzs', hxs', hlr'] until [cA "runtime.gcWriteBarrier2"]
  all_goals first
  | exact KF _ _ (MemFrame.refl _ _) (LiveFrame.refl _ _ _) hinv0
      (by first | (simp only [hdrW]; done) | (simp only [hdrW]; rw [hl0_of (by omega : l = 0)])) rfl rfl rfl rfl
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [hfp]; exact hb)
  | skip
  all_goals
    refine Reaches.call_regions ((hwb L1 b1).withExit hret) ?pc ⟨⟨?_, ?_, ?_, ?_, by omega, ?_, ?_⟩, hok, ?_, ?_, ?_⟩
      fun S2 _ hq hrg2 => ?_
    case pc => rfl
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · dsimp only; rw [BitVec.toNat_ofNat]; omega
    · dsimp only; rw [BitVec.toNat_ofNat]; omega
    · dsimp only; rw [BitVec.toNat_ofNat]; omega
    · dsimp only; rw [BitVec.toNat_ofNat, Memory.accessible_writeLE, Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hacc (by omega) (by omega)
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hinv0
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hLW
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hWR
    obtain ⟨buf, junk, f, v, m, ex, ep, rfl, hfr, hlf, hsl, hapL, hapW, hinvS⟩ := hq
    dsimp only at hfr hlf hapW hinvS hsl hapL hrg2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t - 320 < 2 ^ 64 by omega)] at hfr hapW
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hacc16b : m.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hb8a : m.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
    have hb8b : m.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hacc16b (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hbz : buf.toNat + 16 ≤ zA ∨ zA + 32 ≤ buf.toNat := by
      rcases hzH with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hbS : buf.toNat + 16 ≤ t - 4416 ∨ t + 48 ≤ buf.toNat := by
      have := hbufR.apart hrt; unfold Apart at this; omega
    have hrdS : ∀ a n, t - 4416 ≤ a → a + n ≤ t + 48 → t - 328 ≤ a →
        m.readLE a n = (hdrW S.mem zA l c).readLE a n := by
      intro a n h1 h2 h3
      exact hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega⟩)
    have hmx : m.readLE (t - 320 + 336) 8 = zA := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrW]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [show t - 320 + 336 = t + 16 by omega]; exact hxs
    have hmfp : m.readLE (t - 328) 8 = r29.toNat := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrW]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hfp
    have hmlr : m.readLE (t - 328 + 8) 8 = ret0 := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrW]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hlr'
    have hng0 : (hdrW S.mem zA l c).readLE zA 1 = 0 := by
      simp only [hdrW]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hng
    have hmng : m.readLE zA 1 = 0 := by
      rcases hzH with hL | hO
      · rw [hlf.readLE_nil _ _ (hL.sub (by omega) (by omega))]; exact hng0
      · rw [hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hO.of_sub (by omega) (by omega), by omega⟩)]; exact hng0
    have hmz : m.accessible zA 32 true = true := by
      rw [hfr.accessible]; simp only [hdrW, Memory.accessible_writeLE]; exact hza
    have hmS : m.accessible (t - 4416) (4416 + 48) true = true := by
      rw [hfr.accessible]; simp only [hdrW, Memory.accessible_writeLE]; exact hacc
    have hfr' : MemFrame (hdrW S.mem zA l c) m (R.rt ++ [(t - 4416, t - 328)]) := by
      rw [show t - 4416 = t - 320 - 4096 by omega, show t - 328 = t - 320 - 8 by omega]; exact hfr
    janus_run [hb8a, hb8b, hbuf64, hmx, hmfp, hmlr, hmng, hmz, hmS, es1, es2, hb]
    all_goals
      refine KF _ ?Mw ?mf ?lf ?iv ?mem rfl rfl rfl rfl ?r29
      case mem => rfl
      case mf =>
        exact (hfr'.writeLE_inRanges _ ((hbufR.sub (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
          ((hbufR.sub (by omega) (by omega)).append_left _)
      case lf =>
        exact (hlf.writeLE _ (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))).writeLE _
          (Outside.of_sub hapL.outside (by omega) (by omega))
      case iv =>
        rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
          view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
        exact hinvS _ (by janus_frame)
      case r29 =>
        first
          | exact hb
          | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; done)
          | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hb)
          | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [hmfp]; exact hb)

end FvModexp.Arm64.IExp
