import FvModexp.Proofs.Amd64.Nat.DivBasicMemF
import FvModexp.Proofs.Amd64.Nat.DivBasicTailR

set_option autoImplicit false

/-!
# `divBasic` (amd64): `ujn = u[j+n-1]`; `if j == m && m == len(q) && qhat == 0 { continue }`; `q[j] = qhat`; `j--`
(natdiv.go:719-722), `tailPt = +0x4c9 → head`

The run is DivBasicTailR's `tailRun`. The twin of `Arm64/Nat/DivBasicTail.lean` (+ TailN/TailS).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

theorem mem_q {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {M : Memory} (hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M) {j : Nat} (h1 : j + vl ≤ ul) (h2 : j < ql)
    (v : Nat) : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 (M.writeLE (qp + 8 * j) 8 v) := by
  refine Mem.frame hE hM ⟨fun a n ho => ?_, fun a n w => by simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
  simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho
  obtain ⟨-, -, -, -, -, h7, -, -⟩ := ho
  have : j < qn ql ul vl := by unfold qn; split <;> omega
  exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem tail (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qh : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S tailPt j)
    (h0 : S.regs 0 = BitVec.ofNat 64 vl) (h6 : S.regs 6 = BitVec.ofNat 64 ul) (h10 : S.regs 10 = BitVec.ofNat 64 up)
    (h8 : S.regs 8 = BitVec.ofNat 64 qh) (hqh : qh < 2 ^ 64) (hj : j + vl ≤ ul)
    (hst : ¬ skipQ j ul vl ql qh → j < ql) (Q : State → Prop)
    (k : ∀ S', Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' (j + 2 ^ 64 - 1)
        (S.mem.readLE (up + 8 * (j + vl - 1)) 8) →
      (∀ a n, S'.mem.readLE a n = (if skipQ j ul vl ql qh then S.mem else S.mem.writeLE (qp + 8 * j) 8 qh).readLE a n) →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, retAddrOf s = (r : W64) := ⟨(retAddrOf s).toNat, by simp⟩
  rw [hr] at k ⊢
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hM := hB.mem
  have hsp : (S.regs 4).toNat + 224 = (s.regs 4).toNat := by
    rw [hB.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hce := hE.pre.ce
  have hub := hE.pre.ub
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have mm : S.mem.readLE ((s.regs 4).toNat - 104) 8 = ul - vl := by rw [hM.mm]; omega
  refine tailRun impl r Q S (s.regs 4).toNat j vl ul up ql qp qh _ (vl + 1) vp (vl + 1) t _ hB.pc hsp hsp0 hsp1
    (by rw [hMacc]; exact hce.2.1.2.2) h0 h6 h10 h8 hqh hj (by omega) hub hE.pre.qb hst hl.u48
    (by rw [hMacc]; exact Janus.Arm64.Memory.accessible_read_of_write _ hE.pre.uacc) hl.q48
    (by rw [hMacc]; exact hE.pre.qacc) hl.qw hB.jj mm hM.s2 hM.s1 hM.rw hM.s8 hM.hl hM.s7 hM.hc hM.tp hM.vn1 ?_
  intro S' e0 e4 e5 e14 e0' e1 e2 e3 e6 e7 e8 e10 e11 em ex efs edf
  have hM' : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S'.mem := by
    rw [em]; split
    · exact hM
    · rename_i hs; exact mem_q hE hM hj (hst hs) qh
  exact k S' ⟨e0, e4.trans hB.sp, e5.trans hB.r5, e14.trans hB.r14, efs.trans hB.fs, by rw [ex]; exact hB.x15,
    edf.trans hB.df, e0', e1, e2, e3, e6, e7, e8, e10, e11, hE, hM'⟩ (fun a n => by rw [em])

end FvModexp.Amd64.DivBasic
