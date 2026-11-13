import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsFRecP
import FvModexp.Proofs.Arm64.NatQ.DrsFRecQ
import FvModexp.Proofs.Arm64.Nat.DrsNorm
import FvModexp.Proofs.Common.MaskWord

/-! (Q-form copy of Arm64/Nat/DrsF2.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block segment 2: the recursive call (natdiv.go:863)

`f2`: from `AF1` (`0x1ba938`) → `u[s:]` (`norm6`: `u[s:].norm()`, length `k`) → the slots `s`, `u[s:]`, `v[s:]`
(`BdF`) → arguments `qhat0`, `stk`, `u[s:s+k]`, `v[s:]`, `depth+1` → `CALL divRecursiveStep` (induction hypothesis) →
its return `0x1baa04` (`AF2`). Split: `f2c` (the call), `f2x` (norm exit → call), `f2` (to the norm head).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

/-- the dividend argument of the final recursive call is small (from the loop invariant at `j ≤ B`) -/
theorem argF_lt {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} {M : Memory} (hcr : Cr R c s)
    (hli : c.LI s j Z U) (hj : j ≤ c.vl / 2) (huk : Asm.limbs M c.up c.u1 = U) :
    2 * natVal M (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) <
      2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) := by
  obtain ⟨-, hu, -, hul, -, -, htail, -⟩ := hli
  have h40 := hcr.h40; have hvu := hcr.vu1
  have htail' : ∀ d ∈ U.drop (c.vl + c.vl / 2), d = 0 := by
    intro d hd
    have e : U.drop (c.vl + c.vl / 2) = (U.drop (j + c.vl)).drop (c.vl / 2 - j) := by
      rw [List.drop_drop]; congr 1; omega
    rw [e] at hd
    exact htail d (List.mem_of_mem_drop hd)
  have hlt : Mdl.val U < 2 ^ (64 * (c.vl + c.vl / 2)) := Mdl.lt_of_drop_zero hu htail'
  have e0 : natVal M (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) = Mdl.val (U.drop (c.vl / 2 - 1)) := by
    rw [← huk, drop_limbs_v (by omega), Asm.val_limbs]; rfl
  have e1 : Mdl.val (U.drop (c.vl / 2 - 1)) = Mdl.val U / 2 ^ (64 * (c.vl / 2 - 1)) := (Mdl.val_take_mod U _ hu).2
  have h2 : Mdl.val U / 2 ^ (64 * (c.vl / 2 - 1)) < 2 ^ (64 * (c.vl + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Mdl.pow64_add]
    exact Nat.lt_of_lt_of_le hlt (Mdl.pow_le_pow_64 (by omega))
  rw [e0, e1]
  have e2 : 2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) = 2 ^ (64 * (c.vl + 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e2]
  have : 2 ≤ 2 ^ 64 := by decide
  have := Nat.mul_le_mul_left (2 ^ (64 * (c.vl + 1))) this
  omega

/-- the own stores of segment 2: `s`, `u[s:]`, `v[s:]` -/
@[reducible] def isF2 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 296, s.sp.toNat - 288), (s.sp.toNat - 272, s.sp.toNat - 264), (s.sp.toNat - 120, s.sp.toNat - 88),
    (s.sp.toNat - 24, s.sp.toNat - 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the final recursive call, from the call state `X` (the induction hypothesis) -/
theorem f2c (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : AF1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', AF2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (n' : Nat) (hk : n' ≤ c.u1 - (c.vl / 2 - 1))
    (hkv : natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) n' = natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)))
    (hkN : NatNorm S.mem (c.up + 8 * (c.vl / 2 - 1)) n')
    (X : State) (hpc : X.pc = BitVec.ofNat 64 0x1ba3a0) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h1 : X.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h2 : X.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h3 : X.regs 3 = BitVec.ofNat 64 c.st)
    (h4 : X.regs 4 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1))) (h5 : X.regs 5 = BitVec.ofNat 64 n')
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1))) (h7 : X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)))
    (h8 : X.regs 8 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1)) (h9 : X.regs 9 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rF2) (hF2 : MemFrame S.mem X.mem (isF2 s)) (hreg : X.mem.regions = S.mem.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 272) 8 = c.vl / 2 - 1)
    (e2 : X.mem.readLE (s.sp.toNat - 104) 8 = c.u1 - (c.vl / 2 - 1))
    (e3 : X.mem.readLE (s.sp.toNat - 296) 8 = c.uc - (c.vl / 2 - 1))
    (e4 : X.mem.readLE (s.sp.toNat - 96) 8 = c.up + 8 * (c.vl / 2 - 1))
    (e5 : X.mem.readLE (s.sp.toNat - 120) 8 = c.vl - (c.vl / 2 - 1))
    (e6 : X.mem.readLE (s.sp.toNat - 112) 8 = c.vc - (c.vl / 2 - 1))
    (e7 : X.mem.readLE (s.sp.toNat - 24) 8 = c.vp + 8 * (c.vl / 2 - 1)) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, huc, huc4, hvlc, hvc4, -, ⟨hvl9, -⟩, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, hu48, -, huw, -⟩,
    ⟨-, hv48, -, hvw, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hj := hA.jB
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF : MemFrame S.mem X.mem (fw s) := hF2.mono fun x n ho => by
    simp only [fw, winA, isF2, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hA.ev hF hreg
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := Fp.own hcr hA.fp hF
  have rd2 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF2.readLE _ _ (by simp only [win, isF2, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : BdF c s X.mem Z :=
    ⟨hA.sl.frame hF2 (by simp only [FixOut, isF2, outside_cons, outside_nil, and_true]; omega), e1, e2, e3, e4, e5,
      e6, e7, by rw [rd2 _ _ hvw]; exact hA.vk, by rw [rd2 _ _ (huw.of_sub (by omega) (by omega))]; exact hA.utl,
      by rw [limbs_congr (rd2 _ _ hqw)]; exact hA.zk⟩
  have huk : Asm.limbs X.mem c.up c.u1 = U := by
    rw [limbs_congr (rd2 _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk
  have hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0 := by rw [rd2 _ _ hcr.t0w]; exact hA.q0
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → X.mem.readLE x n = S.mem.readLE x n := fun x n h1 h2 =>
    rd2 _ _ (huw.of_sub h1 h2)
  have hkvX : natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) n' =
      natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) := by
    simp only [natVal] at hkv ⊢
    rw [ru _ _ (by omega) (by omega), ru _ _ (by omega) (by omega)]; exact hkv
  have hkNX : NatNorm X.mem (c.up + 8 * (c.vl / 2 - 1)) n' := by
    rcases hkN with h | h
    · exact Or.inl h
    · right; rw [ru _ _ (by omega) (by omega)]; exact h
  have hval0 := argF_lt (M := X.mem) hcr hA.li hj huk
  have hval : 2 * natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) n' <
      2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) := by rw [hkvX]; exact hval0
  have hbX := bud_cap (Cr.capOwn hcr hF) hA.bud
  have hKb : drsCQ c.ul (c.vl - c.vl / 2 + 1) + stkR c.Hq X.mem c.st ≤ bk := by
    have h1 : drsCQ c.ul (c.vl - c.vl / 2 + 1) ≤ c.K s := by simp only [Cx.K]; omega
    have h2 := hbX
    omega
  have hpre := rec_preF hcr hEvX hFpX hBdX.vk hk hval hq0 hspn h28 hKb
  have tn : ∀ {r : BitVec 64} {v : Nat}, r = BitVec.ofNat 64 v → v < 2 ^ 64 → r.toNat = v := fun h hv => by
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have t0 := tn h0 (by have := hcr.t048; omega); have t1 := tn h1 (by omega); have t2 := tn h2 (by omega)
  have t3 := tn h3 (by have := Memory.readLE_lt S.mem (s.sp.toNat + 32) 8; rw [hA.sl.s4] at this; omega)
  have t4 := tn h4 (by omega); have t5 := tn h5 (by omega); have t6 := tn h6 (by omega)
  have t7 := tn h7 (by omega); have t8 := tn h8 (by omega); have t9 := tn h9 (by omega)
  refine ReachesRet.call_regions (ih ⟨c.Hq, bk, Lk, c.W - 400, X.regs 0, X.regs 1, X.regs 2, X.regs 3, X.regs 4, X.regs 5,
    X.regs 6, X.regs 7, X.regs 8, X.regs 9, X.regs 10⟩) hpc
    ⟨⟨⟨by rw [h30]; decide, by rw [h30]; decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?hw, ?hp⟩, ?hmu⟩ ?hk
  case hw =>
    show drsW (X.regs 8).toNat ≤ c.W - 400
    rw [t8]; have := drsW_inner h40; omega
  case hp =>
    show DrsPreW R bk Lk c.Hq (drsCQ (X.regs 5).toNat (X.regs 8).toNat) (c.W - 400)
      (X.regs 0).toNat (X.regs 1).toNat (X.regs 2).toNat (X.regs 3).toNat (X.regs 4).toNat (X.regs 5).toNat
      (X.regs 6).toNat (X.regs 7).toNat (X.regs 8).toNat (X.regs 9).toNat X
    rw [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]; exact hpre
  case hmu =>
    show (X.regs 8).toNat < c.vl
    rw [t8]; omega
  case hk =>
    intro X' hpc' ⟨hK, hpost⟩ hrg
    change DrsPostW R bk Lk c.Hq (drsCQ (X.regs 5).toNat (X.regs 8).toNat) (c.W - 400)
      (X.regs 0).toNat (X.regs 1).toNat (X.regs 3).toNat (X.regs 4).toNat (X.regs 5).toNat (X.regs 7).toNat
      (X.regs 8).toNat X X' at hpost
    rw [t0, t1, t3, t4, t5, t7, t8] at hpost
    obtain ⟨L', b', hEv, hFp, hBd, hqk, huk', hbud⟩ :=
      rec_postF hcr hEvX hFpX hBdX hk huk hkvX hkNX hspn h28 hbX hpost hrg
    obtain ⟨k1, k2, k3, k4⟩ := hK
    exact k L' b' X' ⟨by rw [hpc', h30], by rw [k1, hsp], by rw [k2, h28], by rw [k3, h29], by rw [k4, h18], hcr,
      hEv, hFp, hBd, hj, hA.li, hqk, huk', hbud⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from the exit of `u[s:].norm()` (`0x1ba9a0`) through the slot stores to the recursive call -/
theorem f2x (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : AF1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', AF2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (S0 : State) (h0 : S0.regs 0 = BitVec.ofNat 64 c.t0) (h1 : S0.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h2 : S0.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h3 : S0.regs 3 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)))
    (h4 : S0.regs 4 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)))
    (h6 : S0.regs 6 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1))) (h11 : S0.regs 11 = BitVec.ofNat 64 c.vl)
    (h12 : S0.regs 12 = BitVec.ofNat 64 (c.vl / 2 - 1)) (h28 : S0.regs 28 = s.regs 28)
    (h29 : S0.regs 29 = s.sp - 408#64) (h18 : S0.regs 18 = s.regs 18) (hsp0 : S0.sp = s.sp - 400#64) :
    ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit6 → s'.mem = S.mem → s'.regs 15 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 15 16 19 S0 s' → n' ≤ c.u1 - (c.vl / 2 - 1) →
      natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) n' = natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) →
      NatNorm S.mem (c.up + 8 * (c.vl / 2 - 1)) n' → ReachesRet (LibDrs.program.link impl) (s.regs 30) s' Q := by
  intro s' n' hpc hm h15 hsp hS hle hv hN
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, huc, huc4, hvlc, hvc4, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩,
    ⟨-, hv48, -, -, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hsl := hA.sl
  have g : ∀ r, r ≠ 15 → r ≠ 16 → r ≠ 19 → s'.regs r = S0.regs r := fun r a b c => hS r a b c
  have q0 := (g 0 (by decide) (by decide) (by decide)).trans h0
  have q1 := (g 1 (by decide) (by decide) (by decide)).trans h1
  have q2 := (g 2 (by decide) (by decide) (by decide)).trans h2
  have q3 := (g 3 (by decide) (by decide) (by decide)).trans h3
  have q4 := (g 4 (by decide) (by decide) (by decide)).trans h4
  have q6 := (g 6 (by decide) (by decide) (by decide)).trans h6
  have q11 := (g 11 (by decide) (by decide) (by decide)).trans h11
  have q12 := (g 12 (by decide) (by decide) (by decide)).trans h12
  have q28 := (g 28 (by decide) (by decide) (by decide)).trans h28
  have q29 := (g 29 (by decide) (by decide) (by decide)).trans h29
  have q18 := (g 18 (by decide) (by decide) (by decide)).trans h18
  have hsp' : s'.sp = s.sp - 400#64 := hsp.trans hsp0
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hB := lsr1 c.vl (by omega)
  have hB' : BitVec.ofNat 64 c.vl >>> 1 = BitVec.ofNat 64 (c.vl / 2) := by rw [← klsr1]; exact hB
  have r13 := hsl.s10; have r14 := hsl.s8; have r15 := hsl.s11; have r16 := hsl.s4
  have bv : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a + b < 2 ^ 64 → BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b)) ∧
      (b ≤ a → BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b)) := fun a b ha hb => by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have e5 := (bv c.vc (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e6 : BitVec.ofNat 64 (c.vc - c.vl / 2) + 1#64 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e7 := (bv c.vl (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e8 := (bv (c.vl - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  have mk : ∀ x y : Nat, x < 2 ^ 64 → 0 < y → y < 2 ^ 63 →
      BitVec.ofNat 64 x &&& (0#64 - BitVec.ofNat 64 y).sshiftRight 63 = BitVec.ofNat 64 x := fun x y hx h0 hy => by
    rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)]
    exact BitVec.and_allOnes
  have m2 := mk (c.vl / 2 - 1) (c.vc - (c.vl / 2 - 1)) (by omega) (by omega) (by omega)
  have sh : BitVec.ofNat 64 (c.vl / 2 - 1) <<< 3 = BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have a2 := (bv c.vp (8 * (c.vl / 2 - 1)) (by omega) (by omega)).1 (by omega)
  have hn' : n' < 2 ^ 64 := by omega
  janus_run [hm, q0, q1, q2, q3, q4, q6, q11, q12, q28, q29, q18, h15, hB', e5, e6, e7, e8, m2, sh, a2, r13, r14, r15,
    r16] until [0x1ba3a0]
  refine f2c impl R c ih s Lk bk S j Z U hA Q k n' hle hv hN _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (by unfold isF2; janus_frame) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact q0
  · exact q1
  · exact q2
  · exact q4
  · exact q6
  · exact q28
  · exact q29
  · exact q18
  all_goals (try dsimp only)
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- at the head of `u[s:].norm()` (`0x1ba98c`) -/
theorem f2h (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : AF1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', AF2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 nHead6) (hm : S0.mem = S.mem)
    (h15 : S0.regs 15 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)))
    (h0 : S0.regs 0 = BitVec.ofNat 64 c.t0) (h1 : S0.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h2 : S0.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h3 : S0.regs 3 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)))
    (h4 : S0.regs 4 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)))
    (h6 : S0.regs 6 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1))) (h11 : S0.regs 11 = BitVec.ofNat 64 c.vl)
    (h12 : S0.regs 12 = BitVec.ofNat 64 (c.vl / 2 - 1)) (h28 : S0.regs 28 = s.regs 28)
    (h29 : S0.regs 29 = s.sp - 408#64) (h18 : S0.regs 18 = s.regs 18) (hsp0 : S0.sp = s.sp - 400#64) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S0 Q := by
  have hcr := hA.cr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hua, hu48, -, -, -⟩, -⟩ := hcr.pre
  have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have huc : c.uc < 2 ^ 40 := hcr.pre.2.2.2.2.2.2.1
  have hulc : c.ul ≤ c.uc := hcr.pre.2.2.2.2.2.1
  have hn0 : c.u1 - (c.vl / 2 - 1) < 2 ^ 40 := by omega
  have hp : c.up + 8 * (c.vl / 2 - 1) + 8 * (c.u1 - (c.vl / 2 - 1)) ≤ 2 ^ 48 := by omega
  have hra : S.mem.accessible c.up (8 * c.ul) false = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_read_of_write _ hua
  have hacc : S.mem.accessible (c.up + 8 * (c.vl / 2 - 1)) (8 * (c.u1 - (c.vl / 2 - 1))) false = true :=
    Memory.accessible_mono _ hra (by omega) (by omega)
  exact norm6 impl (s.regs 30) S.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1))
    (natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1))) S0 Q
    (f2x impl R c ih s Lk bk S j Z U hA Q k S0 h0 h1 h2 h3 h4 h6 h11 h12 h28 h29 h18 hsp0) hn0 hp hacc h4
    (c.u1 - (c.vl / 2 - 1)) S0 (Nat.le_refl _) hpc h15 rfl (fun _ _ _ _ => rfl) hm rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the final recursive call**: `AF1` → `u[s:].norm()` → `CALL divRecursiveStep` → `AF2` -/
theorem f2 (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : AF1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', AF2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, huc, huc4, hvlc, hvc4, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, -, -, -⟩,
    ⟨-, hv48, -, -, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hsl := hA.sl
  have hpc := hA.pc; have hsp := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hB := lsr1 c.vl (by omega)
  have hB' : BitVec.ofNat 64 c.vl >>> 1 = BitVec.ofNat 64 (c.vl / 2) := by rw [← klsr1]; exact hB
  have r1 := hsl.q0p; have r2 := hsl.q0l; have r3 := hsl.q0c; have r4 := hsl.nn; have r5 := hsl.bb
  have r6 := hsl.ul'; have r7 := hsl.s7; have r10 := hsl.s5
  have bv : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a + b < 2 ^ 64 → BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b)) ∧
      (b ≤ a → BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b)) := fun a b ha hb => by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have e1 := (bv (c.vl / 2) 1 (by omega) (by omega)).2 (by omega)
  have e2 := (bv c.uc (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e3 := (bv c.u1 (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e4 : BitVec.ofNat 64 (c.uc - c.vl / 2) + 1#64 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e5 : BitVec.ofNat 64 (c.u1 - c.vl / 2) + 1#64 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have mk : ∀ x y : Nat, x < 2 ^ 64 → 0 < y → y < 2 ^ 63 →
      BitVec.ofNat 64 x &&& (0#64 - BitVec.ofNat 64 y).sshiftRight 63 = BitVec.ofNat 64 x := fun x y hx h0 hy => by
    rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)]
    exact BitVec.and_allOnes
  have m1 := mk (c.vl / 2 - 1) (c.uc - (c.vl / 2 - 1)) (by omega) (by omega) (by omega)
  have sh : BitVec.ofNat 64 (c.vl / 2 - 1) <<< 3 = BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have a1 := (bv c.up (8 * (c.vl / 2 - 1)) (by omega) (by omega)).1 (by omega)
  janus_run [hB', e1, e2, e3, e4, e5, m1, sh, a1, r1, r2, r3, r4, r5, r6, r7, r10] until [nHead6]
  refine f2h impl R c ih s Lk bk S j Z U hA Q k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  all_goals (first | exact h28 | exact h29 | exact h18 | skip)

end FvModexp.Arm64.Q.DivRec
