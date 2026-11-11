import FvModexp.Proofs.Arm64.Nat.DivBasicDefs
import FvModexp.Proofs.Common.DivBasicBridge
import FvModexp.Proofs.Common.DivBasicMach

/-!
# `divBasic` (arm64): the loop invariant's consequences for one iteration (pure)

`pre_facts`: from `Inv (j + 1)` at the head: the window is in range, `ujn ≤ v[n-1]` (for `divWW`), the `qhatv[n] = 0`
fact the `qhl--` needs, the `q[j]` bound, and `Mdl.dbStep_inv`'s invariant for the next head, all with the machine's
reads in place of the model's `getD`s.
-/

open Janus Janus.Arm64 Janus.Contracts

namespace FvModexp.Arm64.DivBasic


/-- the machine's `qhat` estimate at iteration `j` (memory `M` at the head) -/
@[reducible] def qhatM (s : State) (vp vl : Nat) (M : Memory) (up j ujn : Nat) : Nat :=
  Mdl.qhatEst (s.mem.readLE (vp + 8 * (vl - 1)) 8) (s.mem.readLE (vp + 8 * (vl - 2)) 8)
    (Mdl.reciprocalWord (s.mem.readLE (vp + 8 * (vl - 1)) 8)) ujn (M.readLE (up + 8 * (j + vl - 1)) 8)
    (M.readLE (up + 8 * (j + vl - 2)) 8)

theorem pre_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (hpre : Pre R b L qp ql st up ul uc vp vl s) (hvu : vl ≤ ul) {j ujn : Nat} {M : Memory}
    (hjm : j ≤ ul - vl) (hI : Inv qp ql up ul vp vl s (j + 1) ujn M) :
    j + vl ≤ ul ∧ ujn ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 ∧
      (ul = j + vl → (Mdl.mulAddVWW (Asm.limbs s.mem vp vl) (qhatM s vp vl M up j ujn) 0).2 = 0) ∧
      (¬ (j = ul - vl ∧ ul - vl = ql ∧
        (Mdl.dbSubAdd (Asm.limbs s.mem vp vl) j (qhatM s vp vl M up j ujn) (Asm.limbs M up ul)).2 = 0) → j < ql) ∧
      Mdl.DbInv (Asm.limbs s.mem vp vl) (Asm.limbs s.mem up ul) (Asm.limbs s.mem qp ql) (ul - vl) j
        (Mdl.dbStep (Asm.limbs s.mem vp vl) (Mdl.topLimb (Asm.limbs s.mem vp vl))
          (Mdl.reciprocalWord (Mdl.topLimb (Asm.limbs s.mem vp vl))) (ul - vl) j (Asm.limbs M qp ql) (Asm.limbs M up ul) ujn).1
        (Mdl.dbStep (Asm.limbs s.mem vp vl) (Mdl.topLimb (Asm.limbs s.mem vp vl))
          (Mdl.reciprocalWord (Mdl.topLimb (Asm.limbs s.mem vp vl))) (ul - vl) j (Asm.limbs M qp ql) (Asm.limbs M up ul) ujn).2.1
        (Mdl.dbStep (Asm.limbs s.mem vp vl) (Mdl.topLimb (Asm.limbs s.mem vp vl))
          (Mdl.reciprocalWord (Mdl.topLimb (Asm.limbs s.mem vp vl))) (ul - vl) j (Asm.limbs M qp ql) (Asm.limbs M up ul) ujn).2.2 ∧
      Mdl.dbStep (Asm.limbs s.mem vp vl) (Mdl.topLimb (Asm.limbs s.mem vp vl))
          (Mdl.reciprocalWord (Mdl.topLimb (Asm.limbs s.mem vp vl))) (ul - vl) j (Asm.limbs M qp ql) (Asm.limbs M up ul) ujn =
        (if j = ul - vl ∧ ul - vl = ql ∧
            (Mdl.dbSubAdd (Asm.limbs s.mem vp vl) j (qhatM s vp vl M up j ujn) (Asm.limbs M up ul)).2 = 0
          then Asm.limbs M qp ql
          else Mdl.upd (Asm.limbs M qp ql) j
            [(Mdl.dbSubAdd (Asm.limbs s.mem vp vl) j (qhatM s vp vl M up j ujn) (Asm.limbs M up ul)).2],
         (Mdl.dbSubAdd (Asm.limbs s.mem vp vl) j (qhatM s vp vl M up j ujn) (Asm.limbs M up ul)).1,
         (Mdl.dbSubAdd (Asm.limbs s.mem vp vl) j (qhatM s vp vl M up j ujn) (Asm.limbs M up ul)).1.getD (j + vl - 1) 0) := by
  have hv2 := hpre.v2
  have hvW : Mdl.Wd (Asm.limbs s.mem vp vl) := Asm.Wd_limbs _ _ _
  have hn : 2 ≤ (Asm.limbs s.mem vp vl).length := by simp; omega
  have htop : Mdl.topLimb (Asm.limbs s.mem vp vl) = s.mem.readLE (vp + 8 * (vl - 1)) 8 := by
    unfold Mdl.topLimb; rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega)]
  have hb : 2 ^ 63 ≤ Mdl.topLimb (Asm.limbs s.mem vp vl) := by rw [htop]; exact hpre.vtop
  have hmd : ul - vl + (Asm.limbs s.mem vp vl).length = (Asm.limbs s.mem up ul).length := by simp; omega
  have hm : ul - vl ≤ (Asm.limbs s.mem qp ql).length ∧
      (ul - vl = (Asm.limbs s.mem qp ql).length → Mdl.val ((Asm.limbs s.mem up ul).drop (ul - vl)) <
        Mdl.val (Asm.limbs s.mem vp vl)) := by
    simp only [Asm.length_limbs]
    rcases hpre.room hvu with h | ⟨h1, h2⟩
    · exact ⟨by omega, fun h' => by omega⟩
    · refine ⟨by omega, fun _ => ?_⟩
      have hs := Mdl.val_split (Asm.limbs s.mem up ul) (ul - vl) (by simp)
      have hu : Mdl.val (Asm.limbs s.mem up ul) = natVal s.mem up ul := Asm.val_limbs _ _ _
      have hv : Mdl.val (Asm.limbs s.mem vp vl) = natVal s.mem vp vl := Asm.val_limbs _ _ _
      rw [hu] at hs; rw [hv]
      rw [← h1] at h2
      refine Nat.lt_of_not_le (fun hge => ?_)
      have := Nat.mul_le_mul_left (2 ^ (64 * (ul - vl))) hge
      rw [Nat.mul_comm (natVal s.mem vp vl)] at h2
      omega
  have hI' := hI
  obtain ⟨hWq, hWu, hql, hul, -⟩ := hI
  obtain ⟨hj', hzero, hXD, hujn, hD0⟩ := Mdl.win_facts _ _ _ _ j _ _ ujn hvW hn hb (Asm.Wd_limbs _ _ _) hmd hjm hI'
  have hjl : j + vl ≤ ul := by simp at hj' hul; omega
  have hle := Mdl.ujn_le _ _ j ujn hvW hWu hn hj' hzero hXD hujn
  rw [htop] at hle
  have e1 : (Asm.limbs M up ul).getD (j + (Asm.limbs s.mem vp vl).length - 1) 0 = M.readLE (up + 8 * (j + vl - 1)) 8 := by
    rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega)]
  have e2 : (Asm.limbs M up ul).getD (j + (Asm.limbs s.mem vp vl).length - 2) 0 = M.readLE (up + 8 * (j + vl - 2)) 8 := by
    rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega)]
  have e3 : (Asm.limbs s.mem vp vl).getD ((Asm.limbs s.mem vp vl).length - 2) 0 = s.mem.readLE (vp + 8 * (vl - 2)) 8 := by
    rw [Asm.length_limbs, Asm.limbs_getD _ _ _ _ (by omega)]
  obtain ⟨d1, -, d3, d4⟩ := Mdl.dbStep_inv _ _ _ _ j _ _ ujn hvW hn hb (Asm.Wd_limbs _ _ _) hmd hjm hm hI'
  rw [htop, e1, e2, e3] at d3 d4
  simp only [Asm.length_limbs] at d3 d4
  refine ⟨hjl, hle, fun h => d3 (by first | omega | (simp only [Asm.length_limbs]; omega)), d4, d1, ?_⟩
  have f1 : (Asm.limbs M up ul).getD (j + vl - 1) 0 = M.readLE (up + 8 * (j + vl - 1)) 8 :=
    Asm.limbs_getD _ _ _ _ (by omega)
  have f2 : (Asm.limbs M up ul).getD (j + vl - 2) 0 = M.readLE (up + 8 * (j + vl - 2)) 8 :=
    Asm.limbs_getD _ _ _ _ (by omega)
  have f3 : (Asm.limbs s.mem vp vl).getD (vl - 2) 0 = s.mem.readLE (vp + 8 * (vl - 2)) 8 :=
    Asm.limbs_getD _ _ _ _ (by omega)
  simp only [Mdl.dbStep, htop, Asm.length_limbs, qhatM, f1, f2, f3]

theorem corrLoop_lt (vn1 vn2 un2 : Nat) : ∀ (F qh rh x1 x2 : Nat), qh < 2 ^ 64 →
    Mdl.corrLoop vn1 vn2 un2 F qh rh x1 x2 < 2 ^ 64
  | 0, qh, _, _, _, h => by simp [Mdl.corrLoop, h]
  | F + 1, qh, rh, x1, x2, h => by
    simp only [Mdl.corrLoop]
    split
    · split
      · exact Nat.mod_lt _ (by omega)
      · exact corrLoop_lt vn1 vn2 un2 F _ _ _ _ (Nat.mod_lt _ (by omega))
    · exact h

/-- the estimate is a word -/
theorem qhatM_lt {s : State} {vp vl : Nat} (M : Memory) (up j ujn : Nat)
    (hv1 : 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) (hle : ujn ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) :
    qhatM s vp vl M up j ujn < 2 ^ 64 := by
  have h1 := Memory.readLE_lt s.mem (vp + 8 * (vl - 1)) 8
  have h2 := Memory.readLE_lt M (up + 8 * (j + vl - 1)) 8
  simp only [qhatM]
  rw [Mdl.qhatEst_eq _ _ _ _ _ hv1 (by simpa using h1) hle (by simpa using h2)]
  split
  · apply corrLoop_lt
    apply Nat.div_lt_of_lt_mul
    have : ujn < s.mem.readLE (vp + 8 * (vl - 1)) 8 := by omega
    have h3 : (ujn + 1) * 2 ^ 64 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
    have h4 : M.readLE (up + 8 * (j + vl - 1)) 8 < 2 ^ 64 := by simpa using h2
    rw [Nat.add_mul, Nat.one_mul] at h3
    rw [Nat.mul_comm (s.mem.readLE _ 8)]; omega
  · omega

/-- the carry of `mulAddVWW(x, y, 0)` -/
theorem mav_carry (V : List Nat) (y : Nat) (hV : Mdl.Wd V) (hy : y < 2 ^ 64) :
    (Mdl.mulAddVWW V y 0).2 = Mdl.val V * y / 2 ^ (64 * V.length) := by
  obtain ⟨hl, hw, -, hv⟩ := Mdl.mulAddVWW_spec V y 0 hV hy (by omega)
  have := Mdl.val_lt hw
  rw [hl] at this
  rw [Nat.add_zero] at hv
  rw [← hv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt this, Nat.zero_add]

end FvModexp.Arm64.DivBasic
