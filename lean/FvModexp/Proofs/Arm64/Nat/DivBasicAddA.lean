import FvModexp.Proofs.Arm64.Nat.DivBasicAddFin
import FvModexp.Proofs.Arm64.Nat.DivBasicCorr
/-!
# `divBasic` (arm64): the add-back `if c != 0 { c := addVV(u[j:j+n], u[j:j+n], v); if n < qhl { u[j+n] += c }; qhat-- }`
(natdiv.go:710-720), `+0x230 → +0x2d8`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic



set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem addA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat bw : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterSub j)
    (hqh : S.mem.readLE (s.sp.toNat - 96) 8 = qhat) (hql : S.mem.readLE (s.sp.toNat - 120) 8 = vl)
    (huj : S.mem.readLE (s.sp.toNat - 48) 8 = up + 8 * j) (hcj : S.mem.readLE (s.sp.toNat - 64) 8 = uc - j)
    (hbw : S.mem.readLE (s.sp.toNat - 160) 8 = bw) (hbw0 : bw ≠ 0)
    (hj : j + vl ≤ ul) (Q : State → Prop)
    (k : ∀ S', AddK R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S S' j qhat vl bw →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hpc, hsp, h28, h29, h18, hM, hjj⟩ := hB
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvb := hl.vb; have hv48 := hl.v48
  have hu48 := hl.u48; have hvw := hl.vw; have huw := hl.uw; have huv := hl.uv; have hug := hl.ug
  have hulc := hE.pre.ulc; have hub := hE.pre.ub; have hucB := hE.pre.ucb
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hE.pre.ce
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have huacc : S.mem.accessible up (8 * ul) true = true := by rw [hMacc]; exact hE.pre.uacc
  have hvacc : S.mem.accessible vp (8 * vl) false = true := by rw [hMacc]; exact hE.pre.vacc
  have hqB : qhat < 2 ^ 64 := by rw [← hqh]; exact Memory.readLE_lt _ _ _
  have hinv := hM.inv
  have s8 := hM.s8; have s4 := hM.s4; have s5 := hM.s5; have s6 := hM.s6; have s7 := hM.s7; have s9 := hM.s9
  have hview := view_win hout L1
  have huH : Held R L1 (up + 8 * j) (8 * vl) := (hE.ext.held hE.pre.uh).sub (by omega) (by omega)
  have f1 : up + 8 * j = vp ∨ Apart (up + 8 * j) (8 * vl) vp (8 * vl) := Or.inr (by unfold Apart; omega)
  have f2 : up + 8 * j + 8 * vl ≤ (s.regs 28).toNat + 16 ∨ (s.regs 28).toNat + 16 + 8 ≤ up + 8 * j := by omega
  have hbw' : (S.mem.readLE (s.sp.toNat - 160) 8 = 0) = False := by simp only [hbw, hbw0]
  janus_run [hqh, hql, huj, hcj, hbw', hjj, s8, s4, s5, s6, s7, s9, hview] until [tailPt]
    calls [addvv impl hap R b1 L1]
  rename_i w hv1 hv2 hFw hinvw hgd
  have e80 : s.sp.toNat - 240 + 80 = s.sp.toNat - 160 := by omega
  have e88 : s.sp.toNat - 240 + 88 = s.sp.toNat - 152 := by omega
  rw [e80] at hv2; rw [e80, e88] at hFw
  have hf := finA hE hM hj hFw hv1 hv2
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, hf.mem, ?jj⟩, ?r0, ?r4, ?r7, ?r2, hf.fr, fun h => absurd h hbw0,
    fun _ => ⟨w.readLE (s.sp.toNat - 160) 8, hf.val, fun h => absurd h (Nat.lt_irrefl _)⟩⟩
  case jj => show w.readLE _ _ = _; rw [hf.rd _ _ (by omega) (by omega) (by omega)]; exact hjj
  case r2 =>
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, if_neg hbw0]
    exact bv_dec qhat hqB
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals janus_simp

end FvModexp.Arm64.DivBasic
