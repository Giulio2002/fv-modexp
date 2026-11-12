import FvModexp.Proofs.Amd64.Nat.DivBasicExit
import FvModexp.Proofs.Amd64.Nat.DivBasicStep

set_option autoImplicit false

/-!
# `divBasic` (amd64): the main loop by induction, from the head after the prologue to the return (twin of the arm64 Loop)

`loop`: with `k` iterations left (`RDX = k - 1`) and `Inv k`, the function returns with `RQ` (`k = 0`: `fin` with the
values of `Mdl.DbInv … 0`; `k + 1`: `step`). `fromHead`: `len u < len v` exits at once (`u` untouched, `U < V`);
otherwise the initial invariant `Inv (m + 1) 0` (as in `Mdl.divBasic_contract`) and `loop`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

theorem Hd.cast {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} {S : State} {r1 r1' ujn : Nat}
    (h : Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S r1 ujn) (e : r1 % 2 ^ 64 = r1' % 2 ^ 64) :
    Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S r1' ujn :=
  ⟨h.pc, h.sp, h.r5, h.r14, h.fs, h.x15, h.df, h.r0, h.r1, by
    rw [h.r2]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; exact e, h.r3, h.r6, h.r7, h.r8, h.r10,
    h.r11, h.env, h.mem⟩

/-- the values at the end of the loop (`Inv … 0`) -/
theorem inv0_vals {qp ql up ul vp vl : Nat} {s : State} {ujn : Nat} {M : Memory} (hvu : vl ≤ ul)
    (hI : Inv qp ql up ul vp vl s 0 ujn M) :
    natVal M qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl ∧
      natVal M up ul = natVal s.mem up ul % natVal s.mem vp vl := by
  obtain ⟨-, -, -, -, -, huv, -, -, -, hqv⟩ := hI
  simp only [List.drop_zero, Nat.sub_zero, Asm.val_limbs] at huv hqv
  refine ⟨?_, huv⟩
  show Asm.lv M qp (qn ql ul vl) = Asm.lv s.mem up ul / Asm.lv s.mem vp vl
  rw [← hqv, ← Asm.val_limbs]
  have e : (Asm.limbs M qp ql).take (ul - vl + 1) = Asm.limbs M qp (qn ql ul vl) := by
    unfold qn; rw [if_pos hvu]
    by_cases h : ul - vl + 1 ≤ ql
    · rw [Nat.min_eq_left h]; exact Asm.limbs_take _ _ _ _ h
    · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by simp; omega)]
  rw [e]

/-- `len u < len v`: `U < V` -/
theorem short_lt {m : Memory} {up ul vp vl : Nat} (h : ul < vl) (hv : 2 ^ 63 ≤ m.readLE (vp + 8 * (vl - 1)) 8) :
    natVal m up ul < natVal m vp vl := by
  have h1 : natVal m up ul < 2 ^ (64 * ul) := by
    have := Janus.Arm64.Memory.readLE_lt m up (8 * ul)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * ul) = 64 * ul by omega] at this; exact this
  have h2 := Mdl.val_ge_top (Asm.limbs m vp vl)
  rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega), Asm.val_limbs] at h2
  have h3 : 2 ^ (64 * ul) ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 2 ^ (64 * (vl - 1)) ≤ m.readLE (vp + 8 * (vl - 1)) 8 * 2 ^ (64 * (vl - 1)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  show natVal m up ul < Asm.lv m vp vl
  omega

theorem loop (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (hvu : vl ≤ ul) :
    ∀ k, k ≤ ul - vl + 1 → ∀ S ujn, Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S (k + 2 ^ 64 - 1) ujn →
      Inv qp ql up ul vp vl s k ujn S.mem →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S (RQ R b L qp ql st up ul vp vl s)
  | 0, _, S, ujn, hH, hI => by
    have hv := inv0_vals hvu hI
    exact fin impl R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S _ ujn hH (by omega) (by omega) (fun _ => hv.1) hv.2
  | k + 1, hk, S, ujn, hH, hI =>
    step impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE hvu k ujn (by omega) S (hH.cast (by omega)) hI _
      (fun S' ujn' hH' hI' => loop impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE hvu k (by omega) S'
        ujn' hH' hI')

theorem fromHead (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State)
    (hH : Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S (ul + 2 ^ 64 - vl) 0)
    (hqu : ∀ a n, (qp ≤ a ∧ a + n ≤ qp + 8 * ql) ∨ (up ≤ a ∧ a + n ≤ up + 8 * ul) →
      S.mem.readLE a n = s.mem.readLE a n) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S (RQ R b L qp ql st up ul vp vl s) := by
  have hE := hH.env
  have hpre := hE.pre
  have hv2 := hpre.v2; have hvt := hpre.vtop; have hub := hpre.ub
  have hu : natVal S.mem up ul = natVal s.mem up ul := hqu _ _ (Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩)
  by_cases hvu : vl ≤ ul
  · -- the initial invariant
    have hlq : Asm.limbs S.mem qp ql = Asm.limbs s.mem qp ql :=
      Asm.limbs_ext fun i hi => hqu _ _ (Or.inl ⟨by omega, by omega⟩)
    have hlu : Asm.limbs S.mem up ul = Asm.limbs s.mem up ul :=
      Asm.limbs_ext fun i hi => hqu _ _ (Or.inr ⟨by omega, by omega⟩)
    have hvW : Mdl.Wd (Asm.limbs s.mem vp vl) := Asm.Wd_limbs _ _ _
    have hlt1 : Mdl.val ((Asm.limbs s.mem up ul).drop (ul - vl + 1)) < Mdl.val (Asm.limbs s.mem vp vl) := by
      have hlen1 : ((Asm.limbs s.mem up ul).drop (ul - vl + 1)).length = vl - 1 := by simp; omega
      have h1 := Mdl.val_lt ((Asm.Wd_limbs s.mem up ul).drop (ul - vl + 1))
      rw [hlen1] at h1
      have h2 := Mdl.val_ge_top (Asm.limbs s.mem vp vl)
      rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega)] at h2
      have h4 : 2 ^ (64 * (vl - 1)) ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 * 2 ^ (64 * (vl - 1)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hI0 : Inv qp ql up ul vp vl s (ul - vl + 1) 0 S.mem := by
      show Mdl.DbInv _ _ _ _ _ (Asm.limbs S.mem qp ql) (Asm.limbs S.mem up ul) _
      rw [hlq, hlu]
      refine ⟨Asm.Wd_limbs _ _ _, Asm.Wd_limbs _ _ _, rfl, rfl, rfl, ?_, fun _ => ?_, rfl, rfl, ?_⟩
      · exact (Nat.mod_eq_of_lt hlt1).symm
      · simp only [Nat.add_sub_cancel, Asm.length_limbs]
        exact (Mdl.getD_out _ _ (by simp; omega)).symm
      · simp only [Nat.sub_self, List.take_zero, Mdl.val_nil]
        exact (Nat.div_eq_of_lt hlt1).symm
    exact loop impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE hvu _ (Nat.le_refl _) S 0
      (hH.cast (by omega)) hI0
  · have hlt := short_lt (m := s.mem) (up := up) (ul := ul) (vp := vp) (vl := vl) (by omega) hvt
    exact fin impl R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S _ 0 hH (by have := hpre.stlen; omega) (by omega)
      (fun h => absurd h hvu) (by rw [hu, Nat.mod_eq_of_lt hlt])

end FvModexp.Amd64.DivBasic
