import FvModexp.Proofs.Arm64.Nat.DrsRecP
import FvModexp.Proofs.Arm64.Nat.DrsA2
import FvModexp.Proofs.Common.MaskWord

/-!
# `divRecursiveStep` (arm64), loop body segment 2: the recursive call (natdiv.go:813)

`b2`: from `A1` (after `clear(qhat)`) → arguments `qhat0`, `stk`, `uu[s:B+n]`, `v[s:]`, `depth+1` → `CALL
divRecursiveStep` (the induction hypothesis, divisor length `n - B + 1 < n`) → its return `0x1ba614` (`A2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the own stores of segment 2: the argument slots of the recursive call -/
@[reducible] def is7 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 264, s.sp.toNat - 256), (s.sp.toNat - 136, s.sp.toNat - 104), (s.sp.toNat - 32, s.sp.toNat - 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the recursive call of segment 2, from the call state `X` (the induction hypothesis) -/
theorem b2c (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : A1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', A2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 0x1ba3a0) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h1 : X.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h2 : X.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h3 : X.regs 3 = BitVec.ofNat 64 c.st)
    (h4 : X.regs 4 = BitVec.ofNat 64 (c.up + 8 * (j - 1))) (h5 : X.regs 5 = BitVec.ofNat 64 (c.vl + 1))
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.uc - j + 1)) (h7 : X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)))
    (h8 : X.regs 8 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1)) (h9 : X.regs 9 = BitVec.ofNat 64 (c.vc - c.vl / 2 + 1))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 r2) (hF7 : MemFrame S.mem X.mem (is7 s)) (hreg : X.mem.regions = S.mem.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 264) 8 = c.vl / 2 - 1) (e2 : X.mem.readLE (s.sp.toNat - 112) 8 = c.uc - j + 1)
    (e3 : X.mem.readLE (s.sp.toNat - 24) 8 = c.up + 8 * (j - 1)) (e4 : X.mem.readLE (s.sp.toNat - 120) 8 = j)
    (e5 : X.mem.readLE (s.sp.toNat - 128) 8 = c.vc - c.vl / 2 + 1)
    (e6 : X.mem.readLE (s.sp.toNat - 136) 8 = c.vl - c.vl / 2 + 1)
    (e7 : X.mem.readLE (s.sp.toNat - 32) 8 = c.vp + 8 * (c.vl / 2 - 1)) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, huc, huc4, hvlc, hvc4, -, ⟨hvl9, -⟩, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, hu48, -, huw, -⟩,
    ⟨-, hv48, -, hvw, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hj := hA.jB
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF : MemFrame S.mem X.mem (fw s) := hF7.mono fun x n ho => by
    simp only [fw, winA, is7, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hA.ev hF hreg
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := Fp.own hcr hA.fp hF
  have rd7 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF7.readLE _ _ (by simp only [win, is7, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : Bd c s X.mem j Z := hA.bd.frame hF7
    (by simp only [FixOut, is7, outside_cons, outside_nil, and_true]; omega)
    (by simp only [IOut, is7, outside_cons, outside_nil, and_true]; omega) (rd7 _ _ hvw)
    (rd7 _ _ (huw.of_sub (by omega) (by omega))) (rd7 _ _ hqw)
  have huk : Asm.limbs X.mem c.up c.u1 = U := by
    rw [limbs_congr (rd7 _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk
  have hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0 := by rw [rd7 _ _ hcr.t0w]; exact hA.q0
  have hKb : drsC (c.l1 s) c.ul (c.vl - c.vl / 2 + 1) ≤ bk := by
    have h1 : drsC (c.l1 s) c.ul (c.vl - c.vl / 2 + 1) ≤ c.K s := by simp only [Cx.K]; omega
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_mul_of_pos_left (c.K s) (Nat.succ_pos (j / (c.vl / 2)))) hA.bud)
  have hpre := rec_pre hcr hEvX hFpX hBdX hj hjm hq0 hspn h28 hKb
  have tn : ∀ {r : BitVec 64} {v : Nat}, r = BitVec.ofNat 64 v → v < 2 ^ 64 → r.toNat = v := fun h hv => by
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have t0 := tn h0 (by have := hcr.t048; omega); have t1 := tn h1 (by omega); have t2 := tn h2 (by omega)
  have t3 := tn h3 (by have := Memory.readLE_lt S.mem (s.sp.toNat + 32) 8; rw [hA.bd.sl.s4] at this; omega)
  have t4 := tn h4 (by omega); have t5 := tn h5 (by omega); have t6 := tn h6 (by omega)
  have t7 := tn h7 (by omega); have t8 := tn h8 (by omega); have t9 := tn h9 (by omega)
  rw [show c.uc - j + 1 = c.uc - (j - 1) by omega] at t6
  rw [show c.vc - c.vl / 2 + 1 = c.vc - (c.vl / 2 - 1) by omega] at t9
  refine ReachesRet.call_regions (ih ⟨bk, Lk, c.W - 400, X.regs 0, X.regs 1, X.regs 2, X.regs 3, X.regs 4, X.regs 5,
    X.regs 6, X.regs 7, X.regs 8, X.regs 9, X.regs 10⟩) hpc
    ⟨⟨⟨by rw [h30]; decide, by rw [h30]; decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?hw, ?hp⟩, ?hmu⟩ ?hk
  case hw =>
    show drsW (X.regs 8).toNat ≤ c.W - 400
    rw [t8]; have := drsW_inner h40; omega
  case hp =>
    show DrsPreW R bk Lk (drsC (stLen X.mem (X.regs 3).toNat) (X.regs 5).toNat (X.regs 8).toNat) (c.W - 400)
      (X.regs 0).toNat (X.regs 1).toNat (X.regs 2).toNat (X.regs 3).toNat (X.regs 4).toNat (X.regs 5).toNat
      (X.regs 6).toNat (X.regs 7).toNat (X.regs 8).toNat (X.regs 9).toNat X
    rw [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]; exact hpre
  case hmu =>
    show (X.regs 8).toNat < c.vl
    rw [t8]; omega
  case hk =>
    intro X' hpc' ⟨hK, hpost⟩ hrg
    change DrsPostW R bk Lk (drsC (stLen X.mem (X.regs 3).toNat) (X.regs 5).toNat (X.regs 8).toNat) (c.W - 400)
      (X.regs 0).toNat (X.regs 1).toNat (X.regs 3).toNat (X.regs 4).toNat (X.regs 5).toNat (X.regs 7).toNat
      (X.regs 8).toNat X X' at hpost
    rw [t0, t1, t3, t4, t5, t7, t8] at hpost
    obtain ⟨L', b', hEv, hFp, hBd, hBs, hqk, huk', hbud⟩ :=
      rec_post hcr hEvX hFpX hBdX ⟨e1, e2, e3, e4, e5, e6, e7⟩ hj hjm huk hspn h28 hA.bud hpost hrg
    obtain ⟨k1, k2, k3, k4⟩ := hK
    exact k L' b' X' ⟨by rw [hpc', h30], by rw [k1, hsp], by rw [k2, h28], by rw [k3, h29], by rw [k4, h18], hcr,
      hEv, hFp, hBd, hBs, hj, hA.li, hqk, huk', hbud⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem b2 (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : A1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', A2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, huc, huc4, hvlc, hvc4, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩,
    ⟨-, hv48, -, -, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hj := hA.jB
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
  have hsl := hA.bd.sl; have hbd := hA.bd
  have hpc := hA.pc; have hsp := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hB := lsr1 c.vl (by omega)
  have hB' : BitVec.ofNat 64 c.vl >>> 1 = BitVec.ofNat 64 (c.vl / 2) := by rw [← klsr1]; exact hB
  have r1 := hsl.q0p; have r2 := hsl.q0l; have r3 := hsl.q0c; have r4 := hsl.nn; have r5 := hbd.sj
  have r6 := hsl.ul'; have r7 := hsl.s7; have r8 := hbd.sup; have r9 := hbd.suc; have r10 := hsl.s5
  have r11 := hbd.sul; have r12 := hsl.bb; have r13 := hsl.s10; have r14 := hsl.s8; have r15 := hsl.s11
  have r16 := hsl.s4
  have bv : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a + b < 2 ^ 64 → BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b)) ∧
      (b ≤ a → BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b)) := fun a b ha hb => by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have e1 := (bv (j - c.vl / 2) (c.vl / 2) (by omega) (by omega)).1 (by omega)
  rw [show j - c.vl / 2 + c.vl / 2 = j by omega] at e1
  have e2 := (bv c.uc j (by omega) (by omega)).2 (by omega)
  have e3 := (bv (c.uc - j) 1 (by omega) (by omega)).1 (by omega)
  have e4 := (bv (c.vl / 2) 1 (by omega) (by omega)).2 (by omega)
  have e5 := (bv c.vc (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e6 := (bv (c.vc - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  have e7 := (bv c.vl (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e8 := (bv (c.vl - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  have e9 := (bv c.vl 1 (by omega) (by omega)).1 (by omega)
  have mk : ∀ x y : Nat, x < 2 ^ 64 → 0 < y → y < 2 ^ 63 →
      BitVec.ofNat 64 x &&& (0#64 - BitVec.ofNat 64 y).sshiftRight 63 = BitVec.ofNat 64 x := fun x y hx h0 hy => by
    rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)]
    exact BitVec.and_allOnes
  have m1 := mk (c.vl / 2 - 1) (c.uc - j + 1) (by omega) (by omega) (by omega)
  have m2 := mk (c.vl / 2 - 1) (c.vc - c.vl / 2 + 1) (by omega) (by omega) (by omega)
  have sh : BitVec.ofNat 64 (c.vl / 2 - 1) <<< 3 = BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have a1 := (bv (c.up + 8 * (j - c.vl / 2)) (8 * (c.vl / 2 - 1)) (by omega) (by omega)).1 (by omega)
  rw [show c.up + 8 * (j - c.vl / 2) + 8 * (c.vl / 2 - 1) = c.up + 8 * (j - 1) by omega] at a1
  have a2 := (bv c.vp (8 * (c.vl / 2 - 1)) (by omega) (by omega)).1 (by omega)
  janus_run [hB', e1, e2, e3, e4, e5, e6, e7, e8, e9, m1, m2, sh, a1, a2, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16] until [0x1ba3a0]
  refine b2c impl R c ih s Lk bk S j Z U hA Q k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (by unfold is7; janus_frame) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]

end FvModexp.Arm64.DivRec
