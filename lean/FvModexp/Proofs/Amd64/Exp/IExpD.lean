import FvModexp.Proofs.Amd64.Exp.IExpA
import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Common.DivmcMem
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64), segment D: from the return of `nat.expNN` to `RET` (int.go:599-607; fn+0x4a5 .. fn+0x576)
(agent expmc s76; twin of `Arm64.IExp.runD`)

`RSP = t - 0x130`, result `(p, l, c)` in `AX, BX, CX`. `DX = z` (from `t + 8`), the `len, cap` stores at `z + 16`,
the write-barrier flag test (barrier on: `MOVQ 0x8(DX), R12`, `CALL gcWriteBarrier2` at `RSP = t - 0x130`, the buffer
stores `(p, old ptr)` at `R11`), the `ptr` store at `z + 8`; `z.neg = len > 0 && x.neg && …` with `x = z` (from
`t + 0x10`) and `x.neg = false` (the byte at `z` is still `0`): `R12 = 0`, the byte store, `AX = z`, `ADDQ $0x128, SP;
POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.IExp

/-- `z`'s header after the `len, cap` stores -/
@[reducible] def hdrW (M : Janus.Arm64.Memory) (zA l c : Nat) : Janus.Arm64.Memory :=
  (M.writeLE (zA + 16) 8 l).writeLE (zA + 24) 8 c

/-- the return point of the barrier call (fn+0x4c7) -/
abbrev raW : Nat := 0x5e3647

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runD (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibExpI.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (ret0 : Nat) (hret : RetAddr (LibExpI.program.link impl) ret0) (F : State → Prop)
    (t zA p l c bp : Nat) (b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (hal : t % 8 = 0) (ht1 : 0x1140 ≤ t) (ht2 : t + 0x30 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (t - 0x1138) (0x1138 + 0x30) true = true)
    (hrt : Outside (t - 0x1138) (0x1138 + 0x30) R.rt) (hLs : LiveSep L1 [(t - 0x1138, t + 0x30)])
    (hwbA : S.mem.accessible RunIface.wbA 4 false = true) (hwbz : RunIface.wbA + 4 ≤ zA ∨ zA + 32 ≤ RunIface.wbA)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : S.mem.accessible zA 32 true = true)
    (hzS : zA + 32 ≤ t - 0x1138 ∨ t + 0x30 ≤ zA)
    (hzH : Held R L1 zA 32)
    (hok : R.ok (cA "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 S.mem))
    (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 raN) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x130))
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h3 : S.regs 3 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (hzs : S.mem.readLE (t + 8) 8 = zA) (hxs : S.mem.readLE (t + 0x10) 8 = zA)
    (hfp : S.mem.readLE (t - 8) 8 = bp) (hlr : S.mem.readLE t 8 = ret0)
    (hng : S.mem.readLE zA 1 = 0)
    (KF : ∀ (s4 : State) (Mw : Janus.Arm64.Memory),
      MemFrame (hdrW S.mem zA l c) Mw (R.rt ++ [(t - 0x1138, t - 0x130)]) →
      LiveFrame (hdrW S.mem zA l c) Mw L1 [] →
      R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 Mw) →
      s4.mem = (Mw.writeLE (zA + 8) 8 p).writeLE zA 1 0 → s4.regs 4 = BitVec.ofNat 64 (t + 8) →
      s4.regs 0 = BitVec.ofNat 64 zA → s4.regs 5 = BitVec.ofNat 64 bp → s4.regs 14 = S.regs 14 →
      s4.fsBase = S.fsBase → s4.df = S.df → s4.xmm 15 = S.xmm 15 → F s4) :
    Reaches ((LibExpI.program.link impl).withExit ret0) S (IsReturn F) := by
  have es1 : BitVec.ofNat 64 (t - 0x130) - 8#64 = BitVec.ofNat 64 (t - 0x138) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 0x130) + 296#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es4 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es5 : BitVec.ofNat 64 (t - 0x138) + 8#64 = BitVec.ofNat 64 (t - 0x130) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hwbv : RunIface.wbA = 12283968 := rfl
  rw [hwbv] at hwbz hwbA
  have hinv0 : R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 (hdrW S.mem zA l c)) := by
    simp only [hdrW]
    rw [view_writeLE_held (hzH.sub (by omega) (by omega)), view_writeLE_held (hzH.sub (by omega) (by omega))]
    exact hinv
  have hb : BitVec.ofNat 64 bp = BitVec.ofNat 64 (S.mem.readLE (t - 8) 8) := by rw [hfp]
  have hzs' : S.mem.readLE (t - 0x130 + 0x138) 8 = zA := by rw [show t - 0x130 + 0x138 = t + 8 by omega]; exact hzs
  have hxs' : S.mem.readLE (t - 0x130 + 0x140) 8 = zA := by rw [show t - 0x130 + 0x140 = t + 0x10 by omega]; exact hxs
  have hLW : LiveSep L1 [(t - 0x138 - 4096, t - 0x138 + 8)] := fun r hr => by
    have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hWR : LiveSep [(t - 0x138 - 4096, t - 0x138 + 8)] R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hrt.of_sub (by omega) (by simp only; omega)
  have hL1o : Outside (t - 0x138) 8 L1 := Expmc.outside_of_liveSep hLs (by omega) (by omega)
  janus64_run [es1, es2, es3, es4, hzs', hxs', hzs, hxs, hlr, hng] until [cA "runtime.gcWriteBarrier2"]
  all_goals first
  | (refine KF _ _ (MemFrame.refl _ _) (LiveFrame.refl _ _ _) hinv0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
     · first | rfl | (simp only [hdrW]; rw [hbr])
     all_goals first | rfl | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done))
  | skip
  all_goals
    refine Reaches.call_regions ((hwb L1 b1).withExit hret) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hok, ?_, ?_, ?_⟩
      fun S2 _ hq hrg2 => ?_
  all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  · rw [BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_ofNat, Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE,
      Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · exact RtInv.inv_frame' (ws := [(t - 0x138, t - 0x130)]) (by janus_frame)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Or.inl (hrt.of_sub (by simp only; omega) (by simp only; omega))) hinv0
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hLW
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hWR
  obtain ⟨buf, f, x, yh, m, zh, kr, rfl, hfr, hlf, hsl, hapL, hapW, hinvS⟩ := hq
  simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat] at hfr hapW hinvS
  rw [Nat.mod_eq_of_lt (show t - 0x138 < 2 ^ 64 by omega)] at hfr hapW
  obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
  have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
  have hacc16b : m.accessible buf.toNat 16 true = true := by simpa using hsl3
  have hb8a : m.accessible buf.toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
  have hb8b : m.accessible (buf.toNat + 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc16b (by omega) (by omega)
  have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
  have hbz : buf.toNat + 16 ≤ zA ∨ zA + 32 ≤ buf.toNat := by
    rcases hzH with hL | hO
    · have := hapL.apart_of_inRanges hL; omega
    · have := hbufR.apart hO; unfold Apart at this; omega
  have hbS : buf.toNat + 16 ≤ t - 0x1138 ∨ t + 0x30 ≤ buf.toNat := by
    have := hbufR.apart hrt; unfold Apart at this; omega
  have hrdS : ∀ a n, t - 0x1138 ≤ a → a + n ≤ t + 0x30 → t - 0x130 ≤ a →
      m.readLE a n = (hdrW S.mem zA l c).readLE a n := by
    intro a n h1 h2 h3
    rw [hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega⟩),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hdz : ∀ a n, a + n ≤ zA ∨ zA + 32 ≤ a → (hdrW S.mem zA l c).readLE a n = S.mem.readLE a n := by
    intro a n h
    simp only [hdrW]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hmx : m.readLE (t - 0x130 + 0x140) 8 = zA := by
    rw [hrdS _ _ (by omega) (by omega) (by omega), hdz _ _ (by omega), show t - 0x130 + 0x140 = t + 0x10 by omega]
    exact hxs
  have hmfp : m.readLE (t - 8) 8 = bp := by
    rw [hrdS _ _ (by omega) (by omega) (by omega), hdz _ _ (by omega)]; exact hfp
  have hmlr : m.readLE t 8 = ret0 := by
    rw [hrdS _ _ (by omega) (by omega) (by omega), hdz _ _ (by omega)]; exact hlr
  have hng0 : (hdrW S.mem zA l c).readLE zA 1 = 0 := by
    simp only [hdrW]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hng
  have hpush : ∀ a n, a + n ≤ t - 0x138 ∨ t - 0x130 ≤ a →
      (((S.mem.writeLE (zA + 16) 8 l).writeLE (zA + 24) 8 c).writeLE (t - 0x138) 8 raW).readLE a n =
        (hdrW S.mem zA l c).readLE a n := by
    intro a n h; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hmng : m.readLE zA 1 = 0 := by
    rcases hzH with hL | hO
    · rw [hlf.readLE_nil _ _ (hL.sub (by omega) (by omega)), hpush _ _ (by omega)]; exact hng0
    · rw [hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hO.of_sub (by omega) (by omega), by omega⟩), hpush _ _ (by omega)]; exact hng0
  have hmz : m.accessible zA 32 true = true := by
    rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hza
  have hmS : m.accessible (t - 0x1138) (0x1138 + 0x30) true = true := by
    rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  have hfr' : MemFrame (hdrW S.mem zA l c) m (R.rt ++ [(t - 0x1138, t - 0x130)]) := by
    refine ((MemFrame.refl _ [(t - 0x138, t - 0x130)]).writeLE raW (List.mem_singleton_self _) (by simp only; omega)
      (by simp only; omega)).trans hfr (fun a n h => ?_)
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨by omega, h.1, by omega⟩
  have hlf' : LiveFrame (hdrW S.mem zA l c) m L1 [] :=
    ((LiveFrame.refl _ _ _).writeLE raW hL1o).trans hlf (fun _ _ h => h)
  have hes : BitVec.ofNat 64 (t - 0x138) + 8#64 = BitVec.ofNat 64 (t - 0x130) := es5
  janus64_run [hes, es2, es3, es4, hb8a, hb8b, hbuf64, hmx, hmfp, hmlr, hmng, hmz, hmS]
  all_goals
    refine KF _ ?Mw ?mf ?lf ?iv ?mem ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mem => rfl
    case mf =>
      exact (hfr'.writeLE_inRanges _ ((hbufR.sub (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hbufR.sub (by omega) (by omega)).append_left _)
    case lf =>
      exact (hlf'.writeLE _ (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))).writeLE _
        (Outside.of_sub hapL.outside (by omega) (by omega))
    case iv =>
      rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
        view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
      exact hinvS _ (by janus_frame)
    all_goals first | rfl | (simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; done)

end FvModexp.Amd64.IExp
