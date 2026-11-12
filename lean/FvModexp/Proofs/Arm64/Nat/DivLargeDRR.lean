import FvModexp.Proofs.Arm64.Nat.DivLargeDRP
import FvModexp.Proofs.Arm64.Nat.DivLargeDB

/-!
# `divLarge` (arm64): `n ≥ divRecursiveThreshold` → `q.divRecursive(stk, u, v)` (natdiv.go:628-629, 740-742):
`clear(q)` (`memclr`, `fn + 0x3c0`) + `q.divRecursiveStep(stk, u, v, 0)` (`fn + 0x418`), `joinQ` → `joinD`

`dr3`: at `divRecursiveStep`'s entry, the call (premise `DrsHyp`), then `JMP joinD`. `dr2`: after `memclr`, the reloads
to the call. `dr`: from `joinQ` to `memclr` (`q` slots + spills stored, threshold loaded, `BLT` not taken).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

theorem tN64r {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
/-- the stack header at a state whose memory is `AtJ`'s up to `scrB` slots and `q` (pure) -/
theorem stk_Y {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {m : Memory}
    (hA : MemFrame S.mem m (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)])) (hAL : LiveFrame S.mem m Lq [(qp, qp + 8 * qc)]) :
    stLen m st = stLen s.mem st + StackNat.rnd vl := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hsth := hE.pre.sti.1.2.1
  have hqs := hS.qa.ps; unfold Apart at hqs
  have hsw := hl.sw
  simp only [stLen]
  rw [← hS.mem.mem.hlen]
  rcases (hS.ext3.held (hE.ext.held hsth)).sub (a := st + 8) (n := 8) (by omega) (by omega) with hi | ho
  · exact hAL.readLE _ 8 hi (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine hA.readLE _ 8 ?_
    rw [outside_append, outside_append]
    exact ⟨⟨ho, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `divRecursiveStep`'s entry: the call, `JMP joinD`, then `AtD` -/
theorem dr3 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (Y : State)
    (hpc : Y.pc = BitVec.ofNat 64 (segAddr Extracted.program drsFn)) (hsp : Y.sp = s.sp - 304#64)
    (h28 : Y.regs 28 = s.regs 28) (h29 : Y.regs 29 = s.sp - 312#64) (h18 : Y.regs 18 = s.regs 18)
    (h30 : Y.regs 30 = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x41c))
    (hr0 : Y.regs 0 = BitVec.ofNat 64 qp) (hr1 : Y.regs 1 = BitVec.ofNat 64 (il - vl + 1))
    (hr2 : Y.regs 2 = BitVec.ofNat 64 qc) (hr3 : Y.regs 3 = BitVec.ofNat 64 st) (hr4 : Y.regs 4 = BitVec.ofNat 64 P)
    (hr5 : Y.regs 5 = BitVec.ofNat 64 (il + 1)) (hr6 : Y.regs 6 = BitVec.ofNat 64 C)
    (hr7 : Y.regs 7 = BitVec.ofNat 64 t) (hr8 : Y.regs 8 = BitVec.ofNat 64 vl) (hr9 : Y.regs 9 = BitVec.ofNat 64 vl)
    (hr10 : Y.regs 10 = BitVec.ofNat 64 0)
    (hA : MemFrame S.mem Y.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]))
    (hAL : LiveFrame S.mem Y.mem Lq [(qp, qp + 8 * qc)])
    (hq0 : Y.mem.readLE (s.sp.toNat - 64) 8 = qp) (hq1 : Y.mem.readLE (s.sp.toNat - 56) 8 = il - vl + 1)
    (hq2 : Y.mem.readLE (s.sp.toNat - 48) 8 = qc) (hreg : Y.mem.regions = s.mem.regions)
    (hz : natVal Y.mem qp (il - vl + 1) = 0) (hinvY : R.inv bq Lq (s.regs 28).toNat (view R.rt Lq Y.mem))
    (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) Y Q := by
  have hl := hE.lay
  have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hcap := hS.ua.cap; have hc40 := hS.ua.c40; have hqcap := hS.qa.cap; have hq40 := hS.qa.c40
  have e0 : (BitVec.ofNat 64 qp).toNat = qp := tN64r (by have := hS.qa.p48; omega)
  have e1 : (BitVec.ofNat 64 (il - vl + 1)).toNat = il - vl + 1 := tN64r (by omega)
  have e2 : (BitVec.ofNat 64 qc).toNat = qc := tN64r (by omega)
  have e3 : (BitVec.ofNat 64 st).toNat = st := tN64r (by have := hl.st48; omega)
  have e4 : (BitVec.ofNat 64 P).toNat = P := tN64r (by have := hS.ua.p48; omega)
  have e5 : (BitVec.ofNat 64 (il + 1)).toNat = il + 1 := tN64r (by omega)
  have e6 : (BitVec.ofNat 64 C).toNat = C := tN64r (by omega)
  have e7 : (BitVec.ofNat 64 t).toNat = t := tN64r (by have := hl.t48; omega)
  have e8 : (BitVec.ofNat 64 vl).toNat = vl := tN64r (by omega)
  have hLn := stk_Y hE hS hA hAL
  have hcost : dc (stLen Y.mem st) (il + 1) vl ≤ bq := by
    rw [hLn]; have := bud_div hE hS.bud3; omega
  have hpre := dr_pre hE hS Y hsp h28 hA hAL hreg hz hinvY hcost
  have hsum := drssum impl hap R dc hD bq Lq (BitVec.ofNat 64 qp) (BitVec.ofNat 64 (il - vl + 1))
    (BitVec.ofNat 64 qc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 P) (BitVec.ofNat 64 (il + 1)) (BitVec.ofNat 64 C)
    (BitVec.ofNat 64 t) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 0)
  have e30 : (Y.regs 30).toNat = 1809772 := by rw [h30]; decide
  refine ReachesRet.call_regions hsum hpc ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [e30]; exact raL impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]
    exact ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, trivial⟩
  case pre =>
    show DrsPre R bq Lq _ _ _ _ _ _ _ _ _ _ _ Y
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]; exact hpre
  show ReachesRet _ _ T Q
  rw [e0, e1, e3, e4, e5, e7, e8] at hq
  obtain ⟨hqv, hrv, L', b', ⟨hx, hb, hinv⟩, hSB, hMF, hLF⟩ := hq
  rw [h28] at hinv
  have hbud : b - cost dc (stLen s.mem st) il vl ≤ b' := by
    have hb3 := hS.bud3
    have hb1 := hE.bud
    have hc := hE.pre.cost
    rw [hLn] at hb
    simp only [cost] at hc ⊢
    omega
  have hTpc : T.pc = 1809772#64 := by rw [hT, h30]; rfl
  clear hT
  janus_run until [joinD]
  exact k L' b' (stW T.mem st) (stCap T.mem st) _ (divPost (T := ({ T with pc := 1809824#64, sp := s.sp - 304#64 } : State))
    hE hS hsp hA hAL hq0 hq1 hq2 hreg (K := 40960) (A := 96) (by omega) (by omega) rfl rfl (f2.trans h28) (f3.trans h29)
    (f4.trans h18) hrg hqv hrv hx hbud hinv hSB hMF hLF)

end FvModexp.Arm64.DivLarge
