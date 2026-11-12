import FvModexp.Proofs.Amd64.Nat.DivBasicMemF
import FvModexp.Proofs.Amd64.Nat.DivBasicMulR

set_option autoImplicit false

/-!
# `divBasic` (amd64): `qhatv[n] = mulAddVWW(qhatv[0:n], v, qhat, 0)` (natdiv.go:703), `mulPt = +0x26c → +0x2bf`

`qhat` spilled at `RSP-112`; the ABI0 frame `[RSP-224, RSP-160)` = `(t, n, n+1, vp, n, vc, qhat, 0)`; the carry comes
back at `RSP-160`; then `XORPS X15, X15; MOVQ FS:-8, R14`. The run is DivBasicMulR's `mulRun`. The twin of
`Arm64/Nat/DivBasicMul.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mul1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S0 S : State) (j qhat rec vn1 : Nat) (hM0 : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S0.mem)
    (hA : AtMul s S0 S vp vl t rec vn1 j qhat) (hq : qhat < 2 ^ 64) (Q : State → Prop)
    (k : ∀ S', Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' afterVww j →
      S'.mem.readLE ((s.regs 4).toNat - 112) 8 = qhat →
      natVal S'.mem t vl = natVal s.mem vp vl * qhat % 2 ^ (64 * vl) →
      S'.mem.readLE ((s.regs 4).toNat - 160) 8 = natVal s.mem vp vl * qhat / 2 ^ (64 * vl) →
      MemFrame S.mem S'.mem (scr s ++ [(t, t + 8 * vl)]) →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, retAddrOf s = (r : W64) := ⟨(retAddrOf s).toNat, by simp⟩
  rw [hr] at k ⊢
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have ht48 := hl.t48; have hv48 := hl.v48
  have hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S.mem := Mem.frame hE hM0 (hA.fr.mono fun a n ho => by
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨by omega, by omega⟩)
  have hsp : (S.regs 4).toNat + 224 = (s.regs 4).toNat := by
    rw [hA.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hce := hE.pre.ce
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hvs : natVal S.mem vp vl = natVal s.mem vp vl := hM.vs _ _ (Nat.le_refl _) (Nat.le_refl _)
  have htl : TlsG S := by
    obtain ⟨hb, hacc, -⟩ := hce.2.2.2.2.2.2.2.2.2.1
    exact ⟨by rw [hA.fs]; exact hb, by rw [hA.fs, hMacc]; exact hacc, by rw [hA.fs, hA.r14]; exact hM.tls⟩
  have hty : Apart t (8 * vl) vp (8 * vl) := by unfold Apart; have := hl.tv; omega
  have htg : Apart t (8 * vl) ((S.regs 14).toNat + 16) 8 := by rw [hA.r14]; unfold Apart; have := hl.tg; omega
  have htt : Apart t (8 * vl) (S.fsBase.toNat - 8) 8 := by rw [hA.fs]; unfold Apart; have := hl.tlt; omega
  have htw : t + 8 * vl ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ t := by have := hl.tw; omega
  refine mulRun impl hap R b1 L1 r Q S (s.regs 4).toNat t vl vp vc qhat hA.pc hsp hsp0 hsp1
    (by rw [hMacc]; exact hce.2.1.2.2) hA.r8 hA.r10 hA.r1 hA.r7 hA.r6 hl.vb hq (by omega) (by omega) hM.s9
    (by rw [hMacc]; exact Janus.Arm64.Memory.accessible_mono _ hE.scr.acc (by omega) (by omega))
    (by rw [hMacc]; exact hE.pre.vacc) hty htw hl.vw (hl.theld.sub (by omega) (by omega))
    (by rw [hA.r14]; exact hM.inv) hce.2.2.2.2.1 (by rw [hA.r14]; exact hce.2.2.2.2.2.1) htg htl
    (by rw [hA.fs]; exact hce.2.2.2.2.2.2.2.2.2.2.2) htt ?_
  intro S' e0 e4 e5 e14 ex efs edf hv hc hq' hfr
  have hfs : MemFrame S.mem S'.mem (scr s ++ [(t, t + 8 * vl)]) := hfr.mono fun a n ho => by
    simp only [scr, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  refine k S' ⟨e0, e4.trans hA.sp, e5.trans hA.r5, e14.trans hA.r14, efs.trans hA.fs, ex, edf.trans hA.df,
    Mem.frame hE hM (hfs.mono fun a n ho => ?_), ?_⟩ hq' (hv.trans (by rw [hvs])) (hc.trans (by rw [hvs])) hfs
  · simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    omega
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hA.jj

end FvModexp.Amd64.DivBasic
