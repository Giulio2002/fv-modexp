import FvModexp.Proofs.Amd64.Nat.DivBasicAddR

set_option autoImplicit false

/-!
# `divBasic` (amd64): the add-back, all cases (natdiv.go:710-716), `afterSub = +0x3bc → tailPt = +0x4c9`

`c = 0`: `add0Run`; `c ≠ 0`: `addRun` (`addVV.abi0`) then `addFin` (`u[j+n] += c` when `qhl = n + 1`, `qhat--`).
The twin of `Arm64/Nat/DivBasicAdd.lean` (+ AddA/AddB/AddFin).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem add1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat q bw : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterSub j)
    (hqh : S.mem.readLE ((s.regs 4).toNat - 112) 8 = qhat) (hql : S.mem.readLE ((s.regs 4).toNat - 128) 8 = q)
    (huj : S.mem.readLE ((s.regs 4).toNat - 48) 8 = up + 8 * j)
    (hcj : S.mem.readLE ((s.regs 4).toNat - 80) 8 = uc - j)
    (hbw : S.mem.readLE ((s.regs 4).toNat - 152) 8 = bw) (hq : q = vl ∨ q = vl + 1) (hj : j + q ≤ ul)
    (Q : State → Prop)
    (k : ∀ S', AddK R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S S' j qhat q bw →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, retAddrOf s = (r : W64) := ⟨(retAddrOf s).toNat, by simp⟩
  rw [hr] at k ⊢
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hu48 := hl.u48; have hvb := hl.vb
  have hM := hB.mem
  have hsp : (S.regs 4).toNat + 224 = (s.regs 4).toNat := by
    rw [hB.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hce := hE.pre.ce
  have hulc := hE.pre.ulc; have hucb := hE.pre.ucb
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hqB : qhat < 2 ^ 64 := hqh ▸ Janus.Arm64.Memory.readLE_lt _ _ 8
  have hbw64 : bw < 2 ^ 64 := hbw ▸ Janus.Arm64.Memory.readLE_lt _ _ 8
  have hdec : BitVec.ofNat 64 qhat - 1#64 = BitVec.ofNat 64 ((qhat + 2 ^ 64 - 1) % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  by_cases h0 : bw = 0
  · subst h0
    refine add0Run impl r Q S (s.regs 4).toNat vl ul up qhat hB.pc hsp hsp0 hsp1
      (by rw [hMacc]; exact hce.2.1.2.2) hbw hM.s8 hM.s5 hM.s4 hqh ?_
    intro S' e0 e4 e5 e14 e0' e6 e10 e8 em ex efs edf
    have hfr : MemFrame S.mem S'.mem (scr s ++ [(up + 8 * j, up + 8 * j + 8 * q)]) :=
      ⟨fun a n _ => by rw [em], fun a n v => by rw [em]⟩
    refine k S' ⟨⟨e0, e4.trans hB.sp, e5.trans hB.r5, e14.trans hB.r14, efs.trans hB.fs, by rw [ex]; exact hB.x15,
      edf.trans hB.df, by rw [em]; exact hM, by rw [em]; exact hB.jj⟩, e0', e6, e10,
      by rw [e8]; simp only [↓reduceIte], hfr, fun _ a n => by rw [em], fun h => absurd rfl h⟩
  -- `c ≠ 0`
  have hjv : j + vl ≤ ul := by omega
  have hzw : up + 8 * j + 8 * vl ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ up + 8 * j := by
    have := hl.uw; omega
  have htl : TlsG S := by
    obtain ⟨hb, hacc, -⟩ := hce.2.2.2.2.2.2.2.2.2.1
    exact ⟨by rw [hB.fs]; exact hb, by rw [hB.fs, hMacc]; exact hacc, by rw [hB.fs, hB.r14]; exact hM.tls⟩
  refine addRun impl hap R b1 L1 r Q S (s.regs 4).toNat vl j (up + 8 * j) uc vp vc bw hB.pc hsp hsp0 hsp1
    (by rw [hMacc]; exact hce.2.1.2.2) hvb (by omega) hucb h0 hbw64 (by omega) (by have := hl.v48; omega)
    hbw hB.jj hM.s8 hM.s6 huj hcj hM.s7 hM.s9
    (by rw [hMacc]; exact Janus.Arm64.Memory.accessible_mono _ hE.pre.uacc (by omega) (by omega))
    (by rw [hMacc]; exact hE.pre.vacc) (by unfold Apart; have := hl.uv; omega) hzw hl.vw
    ((hE.ext.held hE.pre.uh).sub (by omega) (by omega)) (by rw [hB.r14]; exact hM.inv) hce.2.2.2.2.1
    (by rw [hB.r14]; exact hce.2.2.2.2.2.1) (by rw [hB.r14]; unfold Apart; have := hl.ug; omega) htl
    (by rw [hB.fs]; exact hce.2.2.2.2.2.2.2.2.2.2.2) (by rw [hB.fs]; unfold Apart; have := hl.tlu; omega) ?_
  intro S1 f0 f4 f5 f14 fx ffs fdf hv hc h88 hfr
  have hfr1 : MemFrame S.mem S1.mem (scr s ++ wsL qp ql up ul vl t) := hfr.mono fun a n ho => by
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    omega
  have hM1 : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S1.mem := Mem.frame hE hM hfr1
  have hM1acc : ∀ a n v, S1.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM1.fr.accessible a n v
  have rd1 : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 232 ∨ (s.regs 4).toNat - 144 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat - 80 ≤ a) → (a + 8 ≤ up + 8 * j ∨ up + 8 * j + 8 * vl ≤ a) →
      S1.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a h1 h2 h3 => hfr.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hsp' : (S1.regs 4).toNat + 224 = (s.regs 4).toNat := by rw [f4]; exact hsp
  refine addFin impl r Q S1 (s.regs 4).toNat vl ul up j q
    ((natVal S.mem (up + 8 * j) vl + natVal S.mem vp vl) / 2 ^ (64 * vl)) qhat (by rw [f0]) hsp' hsp0 hsp1
    (by rw [hM1acc]; exact hce.2.1.2.2) hvb hq hj hE.pre.ub hu48 (by rw [hM1acc]; exact hE.pre.uacc) hl.uw
    hM1.s8 (by rw [rd1 _ (by omega) (by omega) (by omega)]; exact hql) hM1.s5 h88 hc hM1.s4
    (by rw [rd1 _ (by omega) (by omega) (by omega)]; exact hqh) ?_
  intro S' g0 g4 g5 g14 g0' g6 g10 g8 gm gx gfs gdf
  have hf2 : MemFrame S1.mem S'.mem [(up + 8 * (j + vl), up + 8 * (j + vl) + 8 * (q - vl))] := by
    rw [gm]; split
    · janus_frame
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  have hfS : MemFrame S.mem S'.mem (scr s ++ [(up + 8 * j, up + 8 * j + 8 * q)]) := (mfTrans hfr hf2).mono
    fun a n ho => by
      simp only [scr, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      omega
  have hM' : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S'.mem := Mem.frame hE hM1 (hf2.mono fun a n ho => by
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    omega)
  have hvs : natVal S.mem vp vl = natVal s.mem vp vl := hM.vs _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hzS : natVal S'.mem (up + 8 * j) vl = natVal S1.mem (up + 8 * j) vl :=
    hf2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine k S' ⟨⟨g0, (g4.trans f4).trans hB.sp, (g5.trans f5).trans hB.r5, (g14.trans f14).trans hB.r14,
    (gfs.trans ffs).trans hB.fs, by rw [gx]; exact fx, (gdf.trans fdf).trans hB.df, hM', ?_⟩, g0', g6, g10,
    by rw [g8, hdec]; simp only [h0, ↓reduceIte], hfS, fun h => absurd h h0, fun _ => ⟨(natVal S.mem (up + 8 * j) vl + natVal S.mem vp vl) / 2 ^ (64 * vl), ?_, fun hvq => ?_⟩⟩
  · rw [hf2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      rd1 _ (by omega) (by omega) (by omega)]; exact hB.jj
  · rw [hzS, hv, ← hvs]; exact Nat.mod_add_div _ _
  · rw [gm]; simp only [show (vl < q) = True from eq_true hvq, ite_true]
    rw [show up + 8 * j + 8 * vl = up + 8 * (j + vl) by omega, Janus.Arm64.Memory.readLE_writeLE_self,
      rd1 _ (by omega) (by omega) (by omega)]

end FvModexp.Amd64.DivBasic
