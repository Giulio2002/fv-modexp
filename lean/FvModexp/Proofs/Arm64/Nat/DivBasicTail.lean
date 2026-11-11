import FvModexp.Proofs.Arm64.Nat.DivBasicAdd

/-!
# `divBasic` (arm64): `ujn = u[j+n-1]`; `if j == m && m == len(q) && qhat == 0 { continue }`; `q[j] = qhat`; `j--`
(natdiv.go:719-722), `+0x2d8 → head`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

/-- the `continue` of natdiv.go:719 -/
@[reducible] def skipQ (j ul vl ql qh : Nat) : Prop := j = ul - vl ∧ ul - vl = ql ∧ qh = 0

theorem mem_q {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {M : Memory} (hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M) {j : Nat} (h1 : j + vl ≤ ul) (h2 : j < ql)
    (v : Nat) : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 (M.writeLE (qp + 8 * j) 8 v) := by
  refine Mem.frame hE hM ⟨fun a n ho => ?_, fun a n w => by simp only [Memory.accessible_writeLE]⟩
  simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho
  obtain ⟨-, -, -, -, -, -, h7, -, -⟩ := ho
  have : j < qn ql ul vl := by unfold qn; rw [if_pos (by omega)]; omega
  exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qh : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S tailPt j)
    (h0 : S.regs 0 = BitVec.ofNat 64 vl) (h4 : S.regs 4 = BitVec.ofNat 64 ul) (h7 : S.regs 7 = BitVec.ofNat 64 up)
    (h2 : S.regs 2 = BitVec.ofNat 64 qh) (hqh : qh < 2 ^ 64) (hj : j + vl ≤ ul)
    (hst : ¬ skipQ j ul vl ql qh → j < ql) (Q : State → Prop)
    (k : ∀ S', Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' (j + 2 ^ 64 - 1)
        (S.mem.readLE (up + 8 * (j + vl - 1)) 8) →
      (∀ a n, S'.mem.readLE a n = (if skipQ j ul vl ql qh then S.mem else S.mem.writeLE (qp + 8 * j) 8 qh).readLE a n) →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hpc, hsp, h28, h29, h18, hM, hjj⟩ := hB
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hu48 := hl.u48; have hq48 := hl.q48
  have huw := hl.uw; have hqw := hl.qw
  have hub := hE.pre.ub; have hqb := hE.pre.qb
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hE.pre.ce
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have huacc : S.mem.accessible up (8 * ul) false = true := by
    rw [hMacc]; exact Memory.accessible_weaken _ hE.pre.uacc
  have hqacc : S.mem.accessible qp (8 * ql) true = true := by rw [hMacc]; exact hE.pre.qacc
  have mm := hM.mm; have s1 := hM.s1; have s2 := hM.s2; have rw' := hM.rw
  have hmm : (ul + 2 ^ 64 - vl) % 2 ^ 64 = ul - vl := by omega
  rw [hmm] at mm
  have hu1 : S.mem.readLE (up + (vl + j - 1) * 8) 8 = S.mem.readLE (up + 8 * (j + vl - 1)) 8 := by
    congr 1; omega
  have hr1 : BitVec.ofNat 64 j - 1#64 = BitVec.ofNat 64 (j + 2 ^ 64 - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  by_cases hsk : skipQ j ul vl ql qh
  · obtain ⟨e1, e2, e3⟩ := hsk
    janus_run [h0, h4, h7, h2, hjj, mm, s1, s2, rw', hu1, e3] until [head]
    refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE, hM⟩ (fun a n => by rw [if_pos ⟨e1, e2, e3⟩])
    · janus_simp
    · janus_simp
    · janus_simp
    · janus_simp
    · janus_simp
    · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, rw']
    · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
      congr 3; omega
  · have hjq := hst hsk
    janus_run [h0, h4, h7, h2, hjj, mm, s1, s2, rw', hu1] until [head]
    · refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE, ?_⟩ ?_
      · janus_simp
      · janus_simp
      · janus_simp
      · janus_simp
      · janus_simp
      · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, rw']
      · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        congr 3; omega
      · dsimp only; rw [show qp + (ul - vl) * 8 = qp + 8 * j by omega]; exact mem_q hE hM hj hjq qh
      · intro a n; dsimp only; rw [if_neg hsk]; congr 2; omega
    · refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE, ?_⟩ ?_
      · janus_simp
      · janus_simp
      · janus_simp
      · janus_simp
      · janus_simp
      · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, rw']
      · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · dsimp only; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        congr 3; omega
      · dsimp only; rw [show qp + j * 8 = qp + 8 * j by omega]; exact mem_q hE hM hj hjq qh
      · intro a n; dsimp only; rw [if_neg hsk]; congr 2; omega

end FvModexp.Arm64.DivBasic
