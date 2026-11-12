import FvModexp.Proofs.Amd64.Nat.DivBasicQhR
import FvModexp.Proofs.Amd64.Nat.DivBasicLay

set_option autoImplicit false

/-!
# `divBasic` (amd64): the loop head and the estimate `qhat` (natdiv.go:667-697)

`est`: from the head with `j ≥ 0` (`RDX = j`, `R8 = ujn`) to `mulPt = +0x26c` (`R8 = qhat`): `ujn == vn1` → `qhat = _M`
(`+0x265`); else `qhat, rhat := divWW(ujn, u[j+n-1], vn1, rec)` (`CALL +0x1e9`), `x1, x2 := mulWW(qhat, vn2)` (`MULQ`),
the correction loop (`corr`), `+0x59e` reloads the head registers. The value is `Mdl.qhatEst` (by `Mdl.qhatEst_eq`).
Writes only the slot `j` (`RSP-96`) and `divWW`'s return slot. The twin of `Arm64/Nat/DivBasicQh.lean`; the runs are
the small lemmas of DivBasicQhR (`estE`, `estD1`, `estD2`, `estX`) and DivBasicCorr's `corr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

theorem sp_224 {s S : State} (h : S.regs 4 = s.regs 4 - 224#64) (h0 : 4424 ≤ (s.regs 4).toNat) :
    (S.regs 4).toNat + 224 = (s.regs 4).toNat := by
  rw [h, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
  have := (s.regs 4).isLt; omega

theorem frame2 {M M' : Memory} {sp : Nat}
    (h : ∀ a n, (a + n ≤ sp - 232 ∨ sp - 224 ≤ a) → (a + n ≤ sp - 96 ∨ sp - 88 ≤ a) → M'.readLE a n = M.readLE a n)
    (hacc : ∀ a n v, M'.accessible a n v = M.accessible a n v) :
    MemFrame M M' [(sp - 232, sp - 224), (sp - 96, sp - 88)] :=
  ⟨fun a n ho => by simp only [outside_cons, outside_nil, and_true] at ho; exact h a n ho.1 ho.2, hacc⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem est (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (j ujn : Nat)
    (hH : Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S j ujn)
    (hj : j + vl ≤ ul) (hle : ujn ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) (Q : State → Prop)
    (k : ∀ S', AtMul s S S' vp vl t (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))
      (s.mem.readLE (vp + 8 * (vl - 1)) 8) j
      (Mdl.qhatEst (s.mem.readLE (vp + 8 * (vl - 1)) 8) (s.mem.readLE (vp + 8 * (vl - 2)) 8)
      (Mdl.reciprocalWord (s.mem.readLE (vp + 8 * (vl - 1)) 8)) ujn (S.mem.readLE (up + 8 * (j + vl - 1)) 8)
      (S.mem.readLE (up + 8 * (j + vl - 2)) 8)) → ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, retAddrOf s = (r : W64) := ⟨(retAddrOf s).toNat, by simp⟩
  rw [hr] at k ⊢
  have hE := hH.env; have hM := hH.mem; have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hsp := sp_224 hH.sp hsp0
  have hub := hE.pre.ub
  have hvtop := hE.pre.vtop
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 4424) (4424 + 88) true = true := by
    rw [hMacc]; exact hE.pre.ce.2.1.2.2
  have hV64 : s.mem.readLE (vp + 8 * (vl - 1)) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hun1 : S.mem.readLE (up + 8 * (j + vl - 1)) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  rw [Mdl.qhatEst_eq _ _ _ _ _ hvtop hV64 hle hun1] at k
  by_cases hq : ujn = s.mem.readLE (vp + 8 * (vl - 1)) 8
  · simp only [ne_eq, hq, not_true_eq_false, ↓reduceIte] at k
    refine estE impl _ Q S (s.regs 4).toNat j _ hH.pc hsp hsp0 hsp1 hwacc hH.r2 (by omega) (hq ▸ hH.r8) hH.r11 ?_
    intro S' e0 hregs e8 em ex efs edf
    refine k S' ⟨e0, (hregs 4 (by decide)).trans hH.sp, (hregs 5 (by decide)).trans hH.r5,
      (hregs 14 (by decide)).trans hH.r14, efs.trans hH.fs, by rw [ex]; exact hH.x15, edf.trans hH.df,
      (hregs 0 (by decide)).trans hH.r0, (hregs 1 (by decide)).trans hH.r1, (hregs 2 (by decide)).trans hH.r2,
      (hregs 3 (by decide)).trans hH.r3, (hregs 6 (by decide)).trans hH.r6, (hregs 7 (by decide)).trans hH.r7,
      e8, (hregs 10 (by decide)).trans hH.r10, (hregs 11 (by decide)).trans hH.r11, ?_, ?_⟩
    · refine frame2 (fun a n _ h2 => ?_) (fun a n v => ?_)
      · rw [em, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      · rw [em, Janus.Arm64.Memory.accessible_writeLE]
    · rw [em, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  · have hlt : ujn < s.mem.readLE (vp + 8 * (vl - 1)) 8 := by omega
    simp only [ne_eq, hq, not_false_eq_true, ↓reduceIte] at k
    have huacc : S.mem.accessible up (8 * ul) false = true := by
      rw [hMacc]; exact Janus.Arm64.Memory.accessible_weaken _ hE.pre.uacc
    refine estD1 impl hap _ Q S (s.regs 4).toNat j vl ul up _ ujn _ hH.pc hsp hsp0 hsp1 hwacc huacc hl.u48 hl.uw
      hH.r0 hH.r1 hH.r2 hH.r8 hH.r11 (by omega) hj hub hlt hV64 hM.s5 hM.s4 rfl ?_
    intro S1 e0 e4 e5 e14 er0 er3 hF1 ex1 efs1 edf1
    have rd1 : ∀ a n, (a + n ≤ (s.regs 4).toNat - 232 ∨ (s.regs 4).toNat - 224 ≤ a) →
        (a + n ≤ (s.regs 4).toNat - 96 ∨ (s.regs 4).toNat - 88 ≤ a) → S1.mem.readLE a n = S.mem.readLE a n := by
      intro a n h1 h2
      rw [hF1.readLE _ _ (by simp only [outside_nil]), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have acc1 : ∀ a n v, S1.mem.accessible a n v = S.mem.accessible a n v := fun a n v => by
      rw [hF1.accessible, Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE]
    have m96 : S1.mem.readLE ((s.regs 4).toNat - 96) 8 = j := by
      rw [hF1.readLE _ _ (by simp only [outside_nil]), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
    have hvw := hl.vw; have huw := hl.uw
    have hvacc : S.mem.accessible vp (8 * vl) false = true := by rw [hMacc]; exact hE.pre.vacc
    have hnz : 0 < s.mem.readLE (vp + 8 * (vl - 1)) 8 := by omega
    have hq0 : (ujn * 2 ^ 64 + S.mem.readLE (up + 8 * (j + vl - 1)) 8) / s.mem.readLE (vp + 8 * (vl - 1)) 8 < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (ujn + 1) * 2 ^ 64 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      rw [Nat.mul_comm]; omega
    refine estD2 impl _ Q S1 (s.regs 4).toNat j vl vp ul up (s.mem.readLE (vp + 8 * (vl - 1)) 8) (s.mem.readLE (vp + 8 * (vl - 2)) 8)
      (S.mem.readLE (up + 8 * (j + vl - 2)) 8) _ e0 (by rw [e4]; exact hsp) hsp0 hsp1 (by rw [acc1]; exact hwacc)
      (by rw [acc1]; exact huacc) hl.u48 (by rw [acc1]; exact hvacc) hl.v48 er0 hq0 hv2 hj hub
      (by rw [rd1 _ _ (by omega) (by omega)]; exact hM.s8) (by rw [rd1 _ _ (by omega) (by omega)]; exact hM.s7) m96
      (by rw [rd1 _ _ (by omega) (by omega)]; exact hM.s5) (by rw [rd1 _ _ (by omega) (by omega)]; exact hM.s4)
      (by rw [rd1 _ _ (by omega) (by omega)]; exact hM.vn1)
      (by rw [rd1 _ _ (by omega) (by omega)]; exact hM.vs _ _ (by omega) (by omega))
      (by rw [rd1 _ _ (by omega) (by omega)]) ?_
    intro S2 f0 f4 f5 f14 f3 f9 f2 f0' f6 f8 f13 f10 f7 fm fx ffs fdf
    have hV2 : s.mem.readLE (vp + 8 * (vl - 2)) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
    have hU2 : S.mem.readLE (up + 8 * (j + vl - 2)) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
    have hr0 : (ujn * 2 ^ 64 + S.mem.readLE (up + 8 * (j + vl - 1)) 8) % s.mem.readLE (vp + 8 * (vl - 1)) 8 < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ hnz) (by omega)
    have hx1 := Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_le hq0 (Nat.le_of_lt hV2) (Nat.two_pow_pos 64))
    have hx2 := Nat.mod_lt ((ujn * 2 ^ 64 + S.mem.readLE (up + 8 * (j + vl - 1)) 8) / s.mem.readLE (vp + 8 * (vl - 1)) 8 *
      s.mem.readLE (vp + 8 * (vl - 2)) 8) (Nat.two_pow_pos 64)
    refine corr impl r Q _ _ _ hnz hV64 hV2 hU2 (2 ^ 64) _ _ _ _ S2 f0 f9 (f3.trans er3) f2 f0' f6 f8 f13
      hq0 hr0 hx1 hx2 (by omega) ?_
    intro S3 g0 g0v hregs3 gm gx gfs gdf
    have m3 : S3.mem = S1.mem := gm.trans fm
    refine estX impl _ Q S3 (s.regs 4).toNat g0 (by rw [hregs3 4 (by decide) (by decide) (by decide) (by decide), f4, e4]; exact hsp)
      hsp0 hsp1 (by rw [m3, acc1]; exact hwacc) (vl + 1) vp (vl + 1) t (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))
      (by rw [m3, rd1 _ _ (by omega) (by omega)]; exact hM.hl) (by rw [m3, rd1 _ _ (by omega) (by omega)]; exact hM.s7)
      (by rw [m3, rd1 _ _ (by omega) (by omega)]; exact hM.hc) (by rw [m3, rd1 _ _ (by omega) (by omega)]; exact hM.tp)
      (by rw [m3, rd1 _ _ (by omega) (by omega)]; exact hM.rw) ?_
    intro S4 x0 x4 x5 x14 x1 x2 x3 x6 x7 x10 x11 x8 x0' xm xx xfs xdf
    have r4 : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 9 → S3.regs i = S2.regs i := hregs3
    refine k S4 ⟨x0, by rw [x4, r4 4 (by decide) (by decide) (by decide) (by decide), f4, e4]; exact hH.sp,
      by rw [x5, r4 5 (by decide) (by decide) (by decide) (by decide), f5, e5]; exact hH.r5,
      by rw [x14, r4 14 (by decide) (by decide) (by decide) (by decide), f14, e14]; exact hH.r14,
      by rw [xfs, gfs, ffs, efs1]; exact hH.fs, by rw [xx, gx, fx, ex1]; exact hH.x15,
      by rw [xdf, gdf, fdf, edf1]; exact hH.df, x0',
      by rw [x1, r4 10 (by decide) (by decide) (by decide) (by decide), f10],
      by rw [x2, r4 7 (by decide) (by decide) (by decide) (by decide), f7], x3, x6, x7, by rw [x8, g0v], x10,
      by rw [x11, r4 13 (by decide) (by decide) (by decide) (by decide), f13], ?_, by rw [xm, m3]; exact m96⟩
    refine frame2 (fun a n h1 h2 => ?_) (fun a n v => ?_)
    · rw [xm, m3, rd1 a n h1 h2]
    · rw [xm, m3, acc1]

end FvModexp.Amd64.DivBasic
