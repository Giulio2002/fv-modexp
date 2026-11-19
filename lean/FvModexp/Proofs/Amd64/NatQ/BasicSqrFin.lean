import FvModexp.Proofs.Amd64.NatQ.BasicSqrVV
import FvModexp.Proofs.Amd64.NatQ.BasicSqrEnv
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/BasicSqrFin.lean — TIGHT COSTS, divmc s37] `basicSqr` (amd64): after the loop (`i = n`, natmul.go:131-133)

`t[2n-1] = lshVU(t[1:2n-1], t[1:2n-1], 1)` (`lshVU.abi0`, frame at `RSP - 200`, carry at `RSP - 136`), then the
`addVV.abi0` arguments, up to `fin3`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.Q.BasicSqr

variable {H : Nat}

abbrev callLsh : Nat := segAddr Extracted.program fn + 0x320

/-- after `lshVU(t[1:2n-1], t[1:2n-1], 1)` and `t[2n-1] = c`: `t[0:2n] = 2 · Σ_{j<n} x_j·x[0:j]·B^j` -/
theorem tval {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl xc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b H L st zp zl zc xp xl s t L1 b1 w1 c1) {M C w : Memory}
    (hI : Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 xl M)
    (hF : MemFrame M C [((s.regs 4).toNat - 200, (s.regs 4).toNat - 136), ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48)])
    (q1 : natVal w (t + 8) (2 * xl - 2) = (natVal C (t + 8) (2 * xl - 2) * 2) % 2 ^ (64 * (2 * xl - 2)))
    (q2 : w.readLE ((s.regs 4).toNat - 136) 8 = (natVal C (t + 8) (2 * xl - 2) * 2) / 2 ^ (64 * (2 * xl - 2)))
    (q3 : MemFrame C w [(t + 8, t + 8 + 8 * (2 * xl - 2)), ((s.regs 4).toNat - 136, (s.regs 4).toNat - 128)]) :
    natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE ((s.regs 4).toNat - 136) 8)) t (2 * xl) =
      2 * SqrMath.sqT (SqrMath.lim s.mem xp) xl := by
  have hl := hE.lay
  have hx0 := hl.x0; have hbig := hE.big; have hsp0 := hl.sp0
  obtain ⟨-, -, hvt, -⟩ := hI
  have htw := hl.tw
  -- the old value: T = t0 + B (V + B^(2n-2) top)
  have hC : natVal C (t + 8) (2 * xl - 2) = natVal M (t + 8) (2 * xl - 2) :=
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  rw [hC] at q1 q2
  have e1 := natVal_add M t 1 (2 * xl - 1)
  have e2 := natVal_add M (t + 8 * 1) (2 * xl - 2) 1
  rw [show 1 + (2 * xl - 1) = 2 * xl by omega, hvt] at e1
  rw [show 2 * xl - 2 + 1 = 2 * xl - 1 by omega, show t + 8 * 1 = t + 8 by omega] at e2
  have e3 : natVal M t 1 = M.readLE t 8 := rfl
  have e4 : natVal M (t + 8 + 8 * (2 * xl - 2)) 1 = M.readLE (t + 8 * (2 * xl - 1)) 8 := by
    show M.readLE _ (8 * 1) = _; congr 1; omega
  rw [e2, e3, e4, show (64 * 1) = 64 by rfl] at e1
  have hmod := SqrMath.sqT_mod (SqrMath.lim s.mem xp) xl
  have hlt := SqrMath.sqT_lt (SqrMath.lim s.mem xp) (SqrMath.lim_lt s.mem xp) (xl - 1)
  rw [show xl - 1 + 1 = xl by omega, show 2 * (xl - 1) + 1 = 2 * xl - 1 by omega] at hlt
  -- the new value
  have f1 := natVal_add (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE ((s.regs 4).toNat - 136) 8)) t 1 (2 * xl - 1)
  have f2 := natVal_add (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE ((s.regs 4).toNat - 136) 8)) (t + 8 * 1) (2 * xl - 2) 1
  rw [show 1 + (2 * xl - 1) = 2 * xl by omega] at f1
  rw [show 2 * xl - 2 + 1 = 2 * xl - 1 by omega, show t + 8 * 1 = t + 8 by omega] at f2
  have g0 : natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE ((s.regs 4).toNat - 136) 8)) t 1 = M.readLE t 8 := by
    show Janus.Arm64.Memory.readLE _ t (8 * 1) = _
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have g1 : natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE ((s.regs 4).toNat - 136) 8)) (t + 8) (2 * xl - 2) =
      natVal w (t + 8) (2 * xl - 2) := Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have g2 : natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE ((s.regs 4).toNat - 136) 8)) (t + 8 + 8 * (2 * xl - 2)) 1 =
      w.readLE ((s.regs 4).toNat - 136) 8 := by
    show Janus.Arm64.Memory.readLE _ _ (8 * 1) = _
    rw [show t + 8 + 8 * (2 * xl - 2) = t + 8 * (2 * xl - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)]
  rw [f1, f2, g0, g1, g2, q1, q2, Nat.mod_add_div]
  have ht0 : M.readLE t 8 < 2 ^ 64 := by have := Janus.Arm64.Memory.readLE_lt M t 8; simpa using this
  have eP : 2 ^ (64 * (2 * xl - 1)) = 2 ^ 64 * 2 ^ (64 * (2 * xl - 2)) := by
    rw [← Nat.pow_add, show 64 + 64 * (2 * xl - 2) = 64 * (2 * xl - 1) by omega]
  rw [eP] at hlt
  rw [e1] at hmod hlt
  generalize natVal M (t + 8) (2 * xl - 2) = V at hmod hlt e1 ⊢
  generalize M.readLE t 8 = t0 at hmod hlt e1 ht0 ⊢
  generalize M.readLE (t + 8 * (2 * xl - 1)) 8 = top at hmod hlt e1
  generalize 2 ^ (64 * (2 * xl - 2)) = P at hmod hlt e1 ⊢
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht0] at hmod
  subst hmod
  have htop : top = 0 := by
    rcases Nat.eq_zero_or_pos top with h | h
    · exact h
    · exfalso
      have h1 : P ≤ V + P * top := by have := Nat.le_mul_of_pos_right P h; omega
      have h2 : 2 ^ 64 * P ≤ 2 ^ 64 * (V + P * top) := Nat.mul_le_mul_left _ h1
      omega
  subst htop
  rw [e1]; simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  rw [Nat.mul_comm V 2, Nat.mul_left_comm]

/-- `lshVU`'s postcondition with the frame words of the call state known -/
theorem lshQ {C : State} {m : Memory} {z n : Nat} (hz : C.mem.readLE ((C.regs 4).toNat + 8) 8 = z)
    (hn : C.mem.readLE ((C.regs 4).toNat + 16) 8 = n) (hx : C.mem.readLE ((C.regs 4).toNat + 32) 8 = z)
    (hs : C.mem.readLE ((C.regs 4).toNat + 56) 8 = 1) (h : LshVUSum.Q C m) :
    natVal m z n = (natVal C.mem z n * 2) % 2 ^ (64 * n) ∧
      m.readLE ((C.regs 4).toNat + 64) 8 = (natVal C.mem z n * 2) / 2 ^ (64 * n) ∧
      MemFrame C.mem m [(z, z + 8 * n), ((C.regs 4).toNat + 64, (C.regs 4).toNat + 72)] := by
  unfold LshVUSum.Q at h
  rw [hz, hn, hx, hs, Nat.pow_one] at h
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- from the `CALL lshVU.abi0` (state `C`, memory = the head's `M` with the frame stores) to the `CALL addVV.abi0` -/
theorem fin2 (impl : List Amd64.Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b H L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (M : Memory) (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat M)
    (C : State) (hpc : C.rip = BitVec.ofNat 64 callLsh) (hsp : C.regs 4 = s.regs 4 - 192#64)
    (h5 : C.regs 5 = s.regs 4 - 8#64) (h14 : C.regs 14 = s.regs 14) (hfs : C.fsBase = s.fsBase)
    (hdf : C.df = false)
    (hF : MemFrame M C.mem [((s.regs 4).toNat - 192, (s.regs 4).toNat - 136),
      ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48)])
    (k1 : C.mem.readLE ((s.regs 4).toNat - 200 + 8) 8 = t + 8)
    (k2 : C.mem.readLE ((s.regs 4).toNat - 200 + 16) 8 = 2 * xl.toNat - 2)
    (k3 : C.mem.readLE ((s.regs 4).toNat - 200 + 32) 8 = t + 8)
    (k4 : C.mem.readLE ((s.regs 4).toNat - 200 + 56) 8 = 1)
    (k5 : C.mem.readLE ((s.regs 4).toNat - 56) 8 = 2 * xl.toNat - 1)
    (hinvC : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 C.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) C fun s' =>
      RegsOK s s' ∧ Post R b H L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hbig := hE.big
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM
  have hCacc : ∀ a n v, C.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF.accessible, mfr.accessible]
  have htacc : s.mem.accessible (t + 8) (8 * (2 * xl.toNat - 2)) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hscr.acc (by omega) (by omega)
  have htacc' := Janus.Arm64.Memory.accessible_weaken _ htacc
  have htH : Held R L1 (t + 8) (8 * (2 * xl.toNat - 2)) := hscr.held.sub (by omega) (by omega)
  have hro : Outside ((s.regs 4).toNat - 200 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg' : Apart (t + 8) (8 * (2 * xl.toNat - 2)) ((s.regs 14).toNat + 16) 8 := by
    unfold Apart; have := hl.gt; omega
  have htt : Apart (t + 8) (8 * (2 * xl.toNat - 2)) (s.fsBase.toNat - 8) 8 := by unfold Apart; have := hl.ft; omega
  have hrg : Apart ((s.regs 4).toNat - 200 + 64) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have hrt : Apart ((s.regs 4).toNat - 200 + 64) 8 (s.fsBase.toNat - 8) 8 := by unfold Apart at htw ⊢; omega
  have htr2 : Apart (t + 8) (8 * (2 * xl.toNat - 2)) ((s.regs 4).toNat - 200) 72 := by
    unfold Apart; have := hl.tw; omega
  have htr3 : Apart (t + 8) (8 * (2 * xl.toNat - 2)) ((s.regs 4).toNat - 200 + 64) 8 := by
    unfold Apart; have := hl.tw; omega
  have hwacc : C.mem.accessible ((s.regs 4).toNat - 200) 72 true = true := by
    rw [hCacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hle : t + 8 ≤ t + 8 := Nat.le_refl _
  clear hpre hscr
  janus64_run [k1, k2, k3, k4, hfs] until [callLsh + 5] calls [hLsh b1 L1]
  rename_i w _ _ hq hinvw hgd htl
  have e200 : (s.regs 4 - 200#64).toNat = (s.regs 4).toNat - 200 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have kk : ∀ k v, (s.regs 4).toNat - 200 + 8 ≤ k → C.mem.readLE k 8 = v →
      (C.mem.writeLE ((s.regs 4).toNat - 200) 8 6232005).readLE k 8 = v := fun k v hk h => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h
  obtain ⟨q1, q2, q3⟩ := lshQ (z := t + 8) (n := 2 * xl.toNat - 2)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e200]; exact kk _ _ (by omega) k1)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e200]; exact kk _ _ (by omega) k2)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e200]; exact kk _ _ (by omega) k3)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e200]; exact kk _ _ (by omega) k4) hq
  simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e200,
    show (s.regs 4).toNat - 200 + 64 = (s.regs 4).toNat - 136 by omega,
    show (s.regs 4).toNat - 200 + 72 = (s.regs 4).toNat - 128 by omega] at q2 q3
  have hP : MemFrame M (C.mem.writeLE ((s.regs 4).toNat - 200) 8 6232005)
      [((s.regs 4).toNat - 200, (s.regs 4).toNat - 136), ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)],
     fun a n v => by rw [Janus.Arm64.Memory.accessible_writeLE, hF.accessible]⟩
  have htw := hl.tw; have hzw := hl.zw
  have rdw : ∀ a, ((s.regs 4).toNat - 128 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 56) ∨
      ((s.regs 4).toNat - 48 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 8) ∨
      ((s.regs 4).toNat + 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → w.readLE a 8 = M.readLE a 8 := by
    intro a ha
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hP.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have w56 : w.readLE ((s.regs 4).toNat - 56) 8 = 2 * xl.toNat - 1 := by
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact kk _ _ (by omega) k5
  have w88 := (rdw _ (by omega)).trans m3
  have w80 := (rdw _ (by omega)).trans m4
  have w48 := (rdw _ (by omega)).trans m5
  have w16 := (rdw _ (by omega)).trans m10
  have w24 := (rdw _ (by omega)).trans m11
  have w32 := (rdw _ (by omega)).trans m12
  have wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    have := hl.fw; have := hl.ft; have := hl.fs
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hP.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m19
  have wtacc : w.accessible (s.fsBase.toNat - 8) 8 false = true := by
    rw [q3.accessible, hP.accessible, mfr.accessible]; exact htr
  have hwacc2 : w.accessible (t + 8 * (2 * xl.toNat - 1)) 8 true = true := by
    rw [q3.accessible, hP.accessible, mfr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hE.scr.acc (by omega) (by omega)
  have hwacc3 : w.accessible ((s.regs 4).toNat - 4424) (4424 + 64) true = true := by
    rw [q3.accessible, hP.accessible, mfr.accessible]; exact hw
  have hfs8 : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  have htv := tval hE hI hP q1 q2 q3
  have hC' : natVal (C.mem.writeLE ((s.regs 4).toNat - 200) 8 6232005) (t + 8) (2 * xl.toNat - 2) =
      natVal M (t + 8) (2 * xl.toNat - 2) :=
    hP.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  rw [q2, hC'] at htv
  janus64_run [w56, w88, w80, w48, w16, w24, w32, wtl, hfs8, hfs,
    mod64_of_lt (t + 8 * (2 * xl.toNat - 1)) (by omega)] until [callVV]
  refine fin3 impl R hVV b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE M hI _ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?_ ?_ ?_ ?_ ?qT ?qI
  case qF => janus_frame
  case qT =>
    show Janus.Arm64.Memory.readLE _ _ _ = _
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    first | exact htv | (rw [show t + (2 * xl.toNat - 1) * 8 = t + 8 * (2 * xl.toNat - 1) by omega]; exact htv)
  case qI =>
    refine RtInv.inv_frame' (ws := [(t + 8 * (2 * xl.toNat - 1), t + 8 * (2 * xl.toNat - 1) + 8),
      ((s.regs 4).toNat - 192, (s.regs 4).toNat - 120)]) (by janus_frame) (fun r hr => ?_) hinvw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hE.scr.held.sub (a := t + 8 * (2 * xl.toNat - 1)) (n := 8) (by omega) (by omega)
      rcases this with h | h
      · right; simpa using h
      · left; simpa using h
    · left; exact hout.of_sub (by omega) (by omega)
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem fin1 (impl : List Amd64.Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b H L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) :
    HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1
      (fun s' => RegsOK s s' ∧ Post R b H L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s') xl.toNat := by
  intro S hpc hsp h5 h14 hfs hx15 hdf r0 r3 r1 r7 r6 r8 r9 r10 hI
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hbig := hE.big
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hb' ha hw
  have hz40 := hpre.zcb; have hzc := hpre.zlc
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM
  have hmask : ((0#64 - (BitVec.ofNat 64 (2 * xl.toNat) - 1#64)).sshiftRight 63).toNat = 18446744073709551615 := by
    refine sshr63_of_lt _ _ ?_ ?_ <;> simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 4424) (4424 + 64) true = true := by
    rw [mfr.accessible]; exact hw
  clear hpre
  janus64_run [BitVec.msb_eq_decide, hmask, hfs, mod64_of_lt (t + 8) (by omega)] until [callLsh]
  refine fin2 impl R hLsh hVV b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE S.mem hI _ ?_ ?_ ?_ ?_ ?_ ?_ ?F
    ?_ ?_ ?_ ?_ ?_ ?inv
  case F => janus_frame
  case inv =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 192, (s.regs 4).toNat - 136),
      ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48)]) (by janus_frame) (fun r hr => ?_) minv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf | omega | skip

end FvModexp.Amd64.Q.BasicSqr
