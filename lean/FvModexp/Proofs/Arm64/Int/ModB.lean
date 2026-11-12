import FvModexp.Proofs.Arm64.Int.ModA
import FvModexp.Proofs.Common.DivmcMem
import FvModexp.Proofs.Arm64.Top.RunIface

/-!
# `(*Int).Mod` (arm64), segment B: `nat.div`'s return → `Mod`'s `RET` (int.go:300-302 in `QuoRem`, int.go:332-339)

`QuoRem` from `raD` (X0..X2 = q, X3..X5 = r): `q.len, q.cap` stored (`q` on Mod's frame), the write-barrier flag test
(barrier on: `gcWriteBarrier4`, its 4 buffer stores), `q.ptr`, `r.cap`, `r.ptr, r.len` stored into `z`'s header (r = z),
`q.neg` (any byte) and `r.neg = len r > 0 && x.neg` with `x = z`, `x.neg = false` (the byte at `z` is still `0`), so `0`;
`RET` to `raQ`; `Mod`: `z.neg = 0` (`TBZ` taken: the `Sub`/`Add` fix-ups are not executed), epilogue, `RET` with X0 = z.
Adapted from expmc's `IExp.runD` (IExpD.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IMod

/-- a store inside the barrier's buffer (runtime-owned, apart from the live set) commutes with `view` -/
theorem view_buf {rt L : List (Nat × Nat)} {buf : Nat} (hR : InRanges buf 32 rt) (hL : ApartAll buf 32 L)
    {a n : Nat} (h1 : buf ≤ a) (h2 : a + n ≤ buf + 32) (M : Memory) (v : Nat) :
    view rt L (M.writeLE a n v) = (view rt L M).writeLE a n v :=
  view_writeLE_vis (hR.sub h1 h2) (Outside.of_sub hL.outside h1 h2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runB (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibMod.program.link impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    (ret0 : Nat) (hret : RetAddr (LibMod.program.link impl) ret0) (F : State → Prop)
    (t zA yA q ql qc r rl rc : Nat) (r29 : BitVec 64) (b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (hal : t % 16 = 0) (ht1 : 4448 ≤ t) (ht2 : t + 32 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (t - 4400) (4400 + 32) true = true)
    (hrt : Outside (t - 4400) (4400 + 32) R.rt) (hLs : LiveSep L1 [(t - 4400, t + 32)])
    (hwbA : S.mem.accessible RunIface.wbA 4 false = true)
    (hwbs : RunIface.wbA + 4 ≤ t - 4400 ∨ t + 32 ≤ RunIface.wbA)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : S.mem.accessible zA 32 true = true) (hzS : zA + 32 ≤ t - 4400 ∨ t + 32 ≤ zA)
    (hzH : Held R L1 zA 32)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : S.mem.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 4400 ∨ t + 32 ≤ yA)
    (hyH : Held R L1 yA 32) (hzy : zA + 32 ≤ yA ∨ yA + 32 ≤ zA)
    (hok : R.ok (cA "runtime.gcWriteBarrier4") [4])
    (hinv : R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 S.mem))
    (hq : q < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64) (hr : r < 2 ^ 64) (hrl : rl < 2 ^ 64) (hrc : rc < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 raD) (hsp : S.sp = BitVec.ofNat 64 (t - 304))
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h1 : S.regs 1 = BitVec.ofNat 64 ql) (h2 : S.regs 2 = BitVec.ofNat 64 qc)
    (h3 : S.regs 3 = BitVec.ofNat 64 r) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h29 : S.regs 29 = BitVec.ofNat 64 (t - 312))
    (s168 : S.mem.readLE (t - 168) 8 = t - 72) (s160 : S.mem.readLE (t - 160) 8 = zA)
    (s152 : S.mem.readLE (t - 152) 8 = yA) (s144 : S.mem.readLE (t - 144) 8 = zA)
    (sfq : S.mem.readLE (t - 312) 8 = t - 184) (slq : S.mem.readLE (t - 304) 8 = raQ)
    (sfp : S.mem.readLE (t - 184) 8 = r29.toNat) (slr : S.mem.readLE (t - 176) 8 = ret0)
    (s8 : S.mem.readLE (t + 8) 8 = zA) (hng : S.mem.readLE zA 1 = 0)
    (KF : ∀ (s4 : State) (Mw : Memory) (qn ql' rl' : Nat),
      s4.mem = finW Mw t zA q r rl' rc qn → ql' = ql → rl' = rl →
      MemFrame (hdrQ S.mem t ql' qc) Mw (R.rt ++ [(t - 4400, t - 312)]) → LiveFrame (hdrQ S.mem t ql' qc) Mw L1 [] →
      R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 Mw) → s4.sp = BitVec.ofNat 64 t →
      s4.regs 0 = BitVec.ofNat 64 zA → s4.regs 18 = S.regs 18 → s4.regs 28 = S.regs 28 → s4.regs 29 = r29 → F s4) :
    Reaches ((LibMod.program.link impl).withExit ret0) S (IsReturn F) := by
  have hr48 := hret.user
  have es1 : BitVec.ofNat 64 (t - 304) + 128#64 = BitVec.ofNat 64 (t - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 176) + 176#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (t - 304) - 8#64 = BitVec.ofNat 64 (t - 312) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es4 : BitVec.ofNat 64 (t - 176) - 8#64 = BitVec.ofNat 64 (t - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hr29 : r29.toNat < 2 ^ 64 := r29.isLt
  have hwbv : RunIface.wbA = 7616064 := rfl
  rw [hwbv] at hwbs hwbA
  have hinv0 : ∀ a c, R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 (hdrQ S.mem t a c)) := by
    intro a c; simp only [hdrQ]
    rw [view_writeLE_held (Or.inr (hrt.of_sub (by omega) (by omega))),
      view_writeLE_held (Or.inr (hrt.of_sub (by omega) (by omega)))]
    exact hinv
  have hb : (BitVec.ofNat 64 r29.toNat) = r29 := by simp
  have s168' : S.mem.readLE (t - 304 + 136) 8 = t - 72 := by rw [show t - 304 + 136 = t - 168 by omega]; exact s168
  have s160' : S.mem.readLE (t - 304 + 144) 8 = zA := by rw [show t - 304 + 144 = t - 160 by omega]; exact s160
  have s152' : S.mem.readLE (t - 304 + 152) 8 = yA := by rw [show t - 304 + 152 = t - 152 by omega]; exact s152
  have s144' : S.mem.readLE (t - 304 + 160) 8 = zA := by rw [show t - 304 + 160 = t - 144 by omega]; exact s144
  have sfq' : S.mem.readLE (t - 304 - 8) 8 = t - 184 := by rw [show t - 304 - 8 = t - 312 by omega]; exact sfq
  have sfp' : S.mem.readLE (t - 176 - 8) 8 = r29.toNat := by rw [show t - 176 - 8 = t - 184 by omega]; exact sfp
  have s8' : S.mem.readLE (t - 176 + 184) 8 = zA := by rw [show t - 176 + 184 = t + 8 by omega]; exact s8
  have slq' : S.mem.readLE (t - 304) 8 = 1773772 := slq
  have hLW : LiveSep L1 [(t - 304 - 4096, t - 304 - 8)] := fun r hr => by
    have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hWR : LiveSep [(t - 304 - 4096, t - 304 - 8)] R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hrt.of_sub (by omega) (by simp only; omega)
  janus_run [es1, es2, es3, es4, hb, s168', s160', s152', s144', sfq', sfp', s8', slq', slr, hng]
    until [cA "runtime.gcWriteBarrier4"]
  all_goals first
  | exact KF _ _ _ _ _ rfl (by omega) (by omega) (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (hinv0 _ _) rfl rfl rfl rfl
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [sfp]; exact hb)
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
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hinv0 _ _
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hLW
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hWR
    obtain ⟨buf, junk, f, v, m, ex, ep, rfl, hfr, hlf, hsl, hapL, hapW, hinvS⟩ := hq
    dsimp only at hfr hlf hapW hinvS hsl hapL hrg2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t - 304 < 2 ^ 64 by omega)] at hfr hapW
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 32 R.rt := by simpa using hsl1
    have hapL' : ApartAll buf.toNat 32 L1 := by simpa using hapL
    have hacc32 : m.accessible buf.toNat 32 true = true := by simpa using hsl3
    have hb8a : m.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hacc32 (Nat.le_refl _) (by omega)
    have hb8b : m.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hacc32 (by omega) (by omega)
    have hb8c : m.accessible (buf.toNat + 16) 8 true = true := Memory.accessible_mono _ hacc32 (by omega) (by omega)
    have hb8d : m.accessible (buf.toNat + 16 + 8) 8 true = true :=
      Memory.accessible_mono _ hacc32 (by omega) (by omega)
    have hbuf64 : buf.toNat + 32 ≤ 2 ^ 48 := by simpa using hsl2
    have hbz : buf.toNat + 32 ≤ zA ∨ zA + 32 ≤ buf.toNat := by
      rcases hzH with hL | hO
      · have := hapL'.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hby : buf.toNat + 32 ≤ yA ∨ yA + 32 ≤ buf.toNat := by
      rcases hyH with hL | hO
      · have := hapL'.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hbS : buf.toNat + 32 ≤ t - 4400 ∨ t + 32 ≤ buf.toNat := by
      have := hbufR.apart hrt; unfold Apart at this; omega
    have hrdS : ∀ a n, t - 4400 ≤ a → a + n ≤ t + 32 → t - 312 ≤ a →
        m.readLE a n = (hdrQ S.mem t ql qc).readLE a n := by
      intro a n h1 h2 h3
      exact hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega⟩)
    have hrdH : ∀ a n, n ≤ 32 → (a = zA ∨ a = yA) → m.readLE a n = S.mem.readLE a n := by
      intro a n hn ha
      have hH : Held R L1 a 32 := by rcases ha with rfl | rfl <;> assumption
      have hS : a + 32 ≤ t - 4400 ∨ t + 32 ≤ a := by rcases ha with rfl | rfl <;> assumption
      have e : (hdrQ S.mem t ql qc).readLE a n = S.mem.readLE a n := by
        simp only [hdrQ]
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [← e]
      rcases hH with hL | hO
      · exact hlf.readLE_nil _ _ (hL.sub (by omega) (by omega))
      · exact hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hO.of_sub (by omega) (by omega), by omega⟩)
    have m1 : m.readLE (t - 72 + 16) 8 = ql := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hql
    have m2 : m.readLE (t - 304 + 144) 8 = zA := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact s160'
    have m3 : m.readLE (t - 304 + 152) 8 = yA := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact s152'
    have m4 : m.readLE (t - 304 - 8) 8 = t - 184 := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact sfq'
    have m5 : m.readLE (t - 304) 8 = 1773772 := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact slq'
    have m6 : m.readLE (t - 176 + 184) 8 = zA := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact s8'
    have m7 : m.readLE (t - 176 - 8) 8 = r29.toNat := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact sfp'
    have m8 : m.readLE (t - 176) 8 = ret0 := by
      rw [hrdS _ _ (by omega) (by omega) (by omega)]; simp only [hdrQ]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact slr
    have m9 : m.readLE zA 1 = 0 := (hrdH zA 1 (by omega) (Or.inl rfl)).trans hng
    have m10 : m.readLE yA 1 = S.mem.readLE yA 1 := hrdH yA 1 (by omega) (Or.inr rfl)
    have hmz : m.accessible zA 32 true = true := by
      rw [hfr.accessible]; simp only [hdrQ, Memory.accessible_writeLE]; exact hza
    have hmy : m.accessible yA 32 false = true := by
      rw [hfr.accessible]; simp only [hdrQ, Memory.accessible_writeLE]; exact hya
    have hmS : m.accessible (t - 4400) (4400 + 32) true = true := by
      rw [hfr.accessible]; simp only [hdrQ, Memory.accessible_writeLE]; exact hacc
    have hfr' : MemFrame (hdrQ S.mem t ql qc) m (R.rt ++ [(t - 4400, t - 312)]) := by
      rw [show t - 4400 = t - 304 - 4096 by omega, show t - 312 = t - 304 - 8 by omega]; exact hfr
    clear hrdS hrdH hfr hsl1 hsl3 hapL
    janus_run [hb8a, hb8b, hb8c, hb8d, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, hmz, hmy, hmS, es1, es2, es3, es4, hb]
    all_goals
      refine KF _ _ _ ql _ rfl rfl (by omega) ?mf ?lf ?iv rfl rfl rfl rfl ?r29
      case mf =>
        repeat (first
          | exact hfr'
          | refine MemFrame.writeLE_inRanges ?_ _ ((hbufR.sub (by omega) (by omega)).append_left _))
      case lf =>
        repeat (first
          | exact hlf
          | refine LiveFrame.writeLE ?_ _ (Outside.of_sub hapL'.outside (by omega) (by omega)))
      case iv =>
        simp (disch := omega) only [view_buf hbufR hapL']
        exact hinvS _ (by janus_frame)
      case r29 =>
        simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        first | (rw [sfp]; exact hb) | exact hb

end FvModexp.Arm64.IMod
