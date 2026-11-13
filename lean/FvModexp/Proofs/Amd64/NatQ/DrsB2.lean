import FvModexp.Proofs.Amd64.NatQ.DrsA2
import FvModexp.Proofs.Common.DivmcBits

set_option autoImplicit false

/-! (amd64 twin (asm s47) of Arm64/NatQ/DrsB2.lean)
# `divRecursiveStep` (amd64), loop body segment 2: the recursive call (natdiv.go:813)

`b2`: from `A1` (`0x5efaf5`, after `clear(qhat)`) → bounds of `uu[s:B+n]` (`s = B - 1`), the argument slots
(`0x78/0xf0/0xf8/0x100/0x108/0x168/0x170(SP)`), `v[s:]` on the stack (`0/8/16(SP)`), `depth + 1` → `CALL
divRecursiveStep` at `0x5efc2c`; `b2c`: from the callee entry, the induction hypothesis (divisor length
`n - B + 1 < n`) → its return `0x5efc31` (`A2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the own stores of segment 2: the return slot and stack arguments of the call, and the argument slots -/
@[reducible] def is8 (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 400, (s.regs 4).toNat - 368), ((s.regs 4).toNat - 272, (s.regs 4).toNat - 264),
    ((s.regs 4).toNat - 152, (s.regs 4).toNat - 120), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the recursive call of segment 2, from the callee entry `X` (the induction hypothesis) -/
theorem b2c (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : A1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', A2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 0x5ef880) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h3 : X.regs 3 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h7 : X.regs 7 = BitVec.ofNat 64 c.st)
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.up + 8 * (j - 1))) (h8 : X.regs 8 = BitVec.ofNat 64 (c.vl + 1))
    (h9 : X.regs 9 = BitVec.ofNat 64 (c.uc - (j - 1)))
    (hF8 : MemFrame S.mem X.mem (is8 s)) (hreg : X.mem.regions = S.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = r2)
    (a1 : X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.vp + 8 * (c.vl / 2 - 1))
    (a2 : X.mem.readLE ((s.regs 4).toNat - 384) 8 = c.vl - c.vl / 2 + 1)
    (a3 : X.mem.readLE ((s.regs 4).toNat - 376) 8 = c.vc - (c.vl / 2 - 1))
    (hbs : Bs c s X.mem j) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have huc := hpre.ulc; have huc4 := hpre.uc40; have hv9 := hpre.v9.1
  have hu48 := hpre.ua.2.1
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hj := hA.jB
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF : MemFrame S.mem X.mem (fw s) := hF8.mono fun x n ho => by
    simp only [fw, win, is8, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hA.ev hF hreg
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := Fp.own hcr hA.fp hF
  have rd8 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF8.readLE _ _ (by simp only [win, is8, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : Bd c s X.mem j Z := hA.bd.frame hF8
    (by simp only [FixOut, is8, outside_cons, outside_nil, and_true]; omega)
    (by simp only [IOut, is8, outside_cons, outside_nil, and_true]; omega) (rd8 _ _ hvw)
    (rd8 _ _ (huw.of_sub (by omega) (by omega))) (rd8 _ _ hqw)
  have huk : Asm.limbs X.mem c.up c.u1 = U := by
    rw [limbs_congr (rd8 _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk
  have hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0 := by rw [rd8 _ _ hcr.t0w]; exact hA.q0
  have hbX := bud_cap (Cr.capOwn hcr hF) hA.bud
  have hKb : drsCQ c.ul (c.vl - c.vl / 2 + 1) + stkR c.Hq X.mem c.st ≤ bk := by
    have h1 : drsCQ c.ul (c.vl - c.vl / 2 + 1) ≤ c.K s := by simp only [Cx.K]; omega
    have h2 : c.K s ≤ (j / (c.vl / 2) + 1) * c.K s := Nat.le_mul_of_pos_left (c.K s) (Nat.succ_pos (j / (c.vl / 2)))
    have h3 := hbX
    omega
  have hrp := rec_pre hcr hEvX hFpX hBdX hj hjm hq0 hspn h14 hfs hKb a1 a2 a3
  have tn : ∀ {r : BitVec 64} {v : Nat}, r = BitVec.ofNat 64 v → v < 2 ^ 64 → r.toNat = v := fun h hv => by
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have t0 := tn h0 (by have := hcr.t048; omega); have t3 := tn h3 (by omega); have t1 := tn h1 (by omega)
  have t7 := tn h7 (by have := Janus.Arm64.Memory.readLE_lt S.mem ((s.regs 4).toNat + 56) 8; rw [hA.bd.sl.s4] at this; omega)
  have t6 := tn h6 (by omega); have t8 := tn h8 (by omega); have t9 := tn h9 (by omega)
  refine ReachesRet.call_regions (ih ⟨c.Hq, bk, Lk, c.W - 400, X.regs 0, X.regs 3, X.regs 1, X.regs 7, X.regs 6,
    X.regs 8, X.regs 9, X.regs 10, c.vp + 8 * (c.vl / 2 - 1), c.vl - c.vl / 2 + 1, c.vc - (c.vl / 2 - 1)⟩) hpc
    ⟨⟨⟨by rw [hspn, hra]; decide, hx15, hdf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?hw, ?hp⟩, ?hmu⟩ ?hk
  case hw =>
    show drsW64 (c.vl - c.vl / 2 + 1) ≤ c.W - 400
    have := drsW64_inner h40; omega
  case hp =>
    show DrsPreW R bk Lk c.Hq (drsCQ (X.regs 8).toNat (c.vl - c.vl / 2 + 1)) (c.W - 400)
      (X.regs 0).toNat (X.regs 3).toNat (X.regs 1).toNat (X.regs 7).toNat (X.regs 6).toNat (X.regs 8).toNat
      (X.regs 9).toNat (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) (c.vc - (c.vl / 2 - 1)) X
    rw [t0, t1, t3, t6, t7, t8, t9]; exact hrp
  case hmu =>
    show c.vl - c.vl / 2 + 1 < c.vl
    omega
  case hk =>
    intro X' hpc' ⟨hK, hpost⟩ hrg
    change DrsPostW R bk Lk c.Hq (drsCQ (X.regs 8).toNat (c.vl - c.vl / 2 + 1)) (c.W - 400)
      (X.regs 0).toNat (X.regs 3).toNat (X.regs 7).toNat (X.regs 6).toNat (X.regs 8).toNat
      (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) X X' at hpost
    rw [t0, t3, t6, t7, t8] at hpost
    have hfs' := hpost.1; have hdf' := hpost.2.1
    obtain ⟨L', b', hEv, hFp, hBd, hBs, hqk, huk', hbud⟩ :=
      rec_post hcr hEvX hFpX hBdX hbs hj hjm huk hspn h14 hbX hpost hrg
    obtain ⟨k1, k2, k3, k4⟩ := hK
    exact k L' b' X' ⟨by rw [hpc']; simp only [retAddrOf]; rw [hspn, hra], by rw [k1]; exact sp_ret400 hspn (by omega),
      by rw [k2, h5], by rw [k3, h14], by rw [hfs', hfs], by rw [hdf', hdf], by rw [k4, hx15], hcr,
      hEv, hFp, hBd, hBs, hj, hA.li, hqk, huk', hbud⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **segment 2**: from `A1` to the return of the recursive call (`A2`) -/
theorem b2 (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : A1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', A2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have huc := hpre.ulc; have huc4 := hpre.uc40; have hv9 := hpre.v9.1
  have hvlc := hpre.vlc; have hvc4 := hpre.vc40
  have hu48 := hpre.ua.2.1; have hv48 := hpre.va.2.1
  have hj := hA.jB
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
  have hsl := hA.bd.sl; have hbd := hA.bd
  have hpc := hA.pc; have hsp := hA.sp
  have hspS : (S.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have e400 : (s.regs 4 - 400#64).toNat = (s.regs 4).toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hA.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hsl.q0p; have r2 := hsl.q0c; have r3 := hsl.q0l; have r4 := hbd.suc; have r5 := hsl.bb
  have r6 := hbd.sup; have r7 := hsl.nn; have r8 := hsl.vc; have r9 := hsl.vp; have r10 := hsl.s9
  have r11 := hsl.s4; have r12 := hsl.s5; have r13 := hsl.ul'; have r14 := hbd.sj8; have r15 := hsl.s7
  have r16 := hbd.sul; have r17 := hbd.sj
  have bv : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a + b < 2 ^ 64 → BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b)) ∧
      (b ≤ a → BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b)) := fun a b ha hb => by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have ad1 := (bv (c.vl / 2) c.vl (by omega) (by omega)).1 (by omega)
  have lt1 : (BitVec.ofNat 64 (c.uc - (j - c.vl / 2)) < BitVec.ofNat 64 (c.vl / 2 + c.vl)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have one : (1#64) = BitVec.ofNat 64 1 := rfl
  have u1 := (bv (c.uc - (j - c.vl / 2)) (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have u2 := (bv (c.uc - (j - c.vl / 2) - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  rw [← one, show c.uc - (j - c.vl / 2) - c.vl / 2 + 1 = c.uc - (j - 1) by omega] at u2
  have b1 := (bv (c.vl / 2) 1 (by omega) (by omega)).2 (by omega)
  rw [← one] at b1
  have sh : BitVec.ofNat 64 (c.vl / 2 - 1) <<< 3 = BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have m1 : ((0#64 - BitVec.ofNat 64 (c.uc - (j - 1))).sshiftRight 63 &&& BitVec.ofNat 64 (8 * (c.vl / 2 - 1))) =
      BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) :=
    neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have pu := (bv (8 * (c.vl / 2 - 1)) (c.up + 8 * (j - c.vl / 2)) (by omega) (by omega)).1 (by omega)
  rw [show 8 * (c.vl / 2 - 1) + (c.up + 8 * (j - c.vl / 2)) = c.up + 8 * (j - 1) by omega] at pu
  have v1 := (bv c.vc (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have v2 := (bv (c.vc - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  rw [← one, show c.vc - c.vl / 2 + 1 = c.vc - (c.vl / 2 - 1) by omega] at v2
  have n1 := (bv c.vl (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have n2 := (bv (c.vl - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  rw [← one] at n2
  have m2 : ((0#64 - BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1))).sshiftRight 63 &&& BitVec.ofNat 64 (8 * (c.vl / 2 - 1))) =
      BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) :=
    neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have pv := (bv (8 * (c.vl / 2 - 1)) c.vp (by omega) (by omega)).1 (by omega)
  rw [show 8 * (c.vl / 2 - 1) + c.vp = c.vp + 8 * (c.vl / 2 - 1) by omega] at pv
  janus64_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, ad1, lt1, u1, u2, b1, sh,
    m1, pu, v1, v2, n1, n2, m2, pv, BitVec.msb_eq_decide]
    until [0x5ef880]
  refine b2c impl R c ih s Lk bk S j Z U hA Q k _ rfl ?sp ?r5 ?r14 hA.fs hA.df hA.x15 ?r0 ?r3 ?r1 ?r7 ?r6 ?r8 ?r9
    ?fr ?reg ?ra ?a1 ?a2 ?a3 ⟨?e1, ?e2, ?e3, ?e4, ?e5, ?e6, ?e7⟩
  case fr => unfold is8; janus_frame
  case reg => janus64_simp
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hA.r5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hA.r14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r1 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r7 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r6 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r8 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r9 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case a1 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case a2 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case a3 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e1 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e2 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e3 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e4 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e5 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e6 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e7 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
