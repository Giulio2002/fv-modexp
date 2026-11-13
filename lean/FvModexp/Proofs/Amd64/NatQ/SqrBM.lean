import FvModexp.Proofs.Amd64.NatQ.SqrBMP
import FvModexp.Proofs.Amd64.Int.IntASCallH
import FvModexp.Proofs.Amd64.Nat.Callees2
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.DivmcMem

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/SqrBM.lean — TIGHT COSTS, divmc s38] `nat.sqr` (amd64), `2 ≤ n < 12`: `basicMul(z, x, x); return z.norm()` (natmul.go:90-93)

`bm`: the join (`0x5f1140`, both thresholds compared) → the `basicMul` entry `0x5f1b40` (return `0x5f1169`); the call via
`ReachesRet.call_regions` with `BasicMul.ens` (pre: `bm_pre`); then `MOVQ 0x68(SP), AX; MOVQ 0x58(SP), BX` → `normM` and
`post_of`. Twin of the arm64 module.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
/-- the return address `0x5f1169` (inside `nat.sqr` = `seg32`) is a return address of a program without `nat.sqr` -/
theorem ra_sqr {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x47f) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x5f0fe0 + i) := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg32) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5f0fe0 + i < 2 ^ 47; omega)
  rw [show Extracted.seg32.base = 0x5f0fe0 from rfl] at this; exact this

set_option maxRecDepth 20000 in
/-- a call of `basicMul` (`BasicMul.ens`) at its entry `0x5f1b40` returning to `0x5f1169` -/
theorem bmCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {a0 a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64} {S : State} {ret : W64}
    {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 0x5f1b40) (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f1169)
    (h0 : S.regs 0 = a0) (h3 : S.regs 3 = a1) (h1 : S.regs 1 = a2) (h7 : S.regs 7 = a3) (h6 : S.regs 6 = a4)
    (h8 : S.regs 8 = a5) (h9 : S.regs 9 = a6) (h10 : S.regs 10 = a7) (h11 : S.regs 11 = a8)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false) (hpre : BasicMul.Pre R b L a0 a1 a2 a3 a4 a6 a7 S)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f1169 → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → BasicMul.Post R b L a0 a3 a4 a6 a7 S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibSqr.program.link impl) ret s' Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  have hc : CodeIn64 ((Extracted.program.onlySegments BasicMul.names).link impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hBM := Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b L a0 a1 a2 a3 a4 a5 a6 a7 a8) (A64.noExit_restrict64 hap BasicMul.names) hc
  rw [show segAddr Extracted.program BasicMul.fn = 0x5f1b40 by decide] at hBM
  refine ReachesRet.call_regions hBM hpc ⟨?_, hx15, hdf, ?_⟩ fun s' hr ⟨⟨e4, e5, e14, e15⟩, hq⟩ hrg => ?_
  · simp only [regSP]; rw [hrd]
    exact ra_sqr (i := 0x189) hap (by decide) (by decide)
  · rw [h0, h3, h1, h7, h6, h9, h10]; exact hpre
  · rw [h0, h7, h6, h9, h10] at hq
    refine K s' ?_ e4 e5 e14 e15 hq hrg
    rw [hr, retAddrOf, hrd]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem bm (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc) (hx2 : 2 ≤ xl.toNat) (hsm : xl.toNat < 12)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  obtain ⟨h12, h80, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r3, r1, r7, r6, r8, r9, hsp, h14, h5, hfs, hdf, hx15, mra, mbp, m64, m80, m88, hreg, hpx, -⟩ := hA
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -, -, -, hxlc, hxc40, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, hal0, -, hout0, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hxl12 : xl.toNat < 2 ^ 13 := by omega
  have e168 : s.regs 4 - 176#64 + 8#64 = s.regs 4 - 168#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hwS : S.mem.accessible ((s.regs 4).toNat - W) (W + 64) true = true := by rw [hJ.F.accessible]; exact hw0
  janus64_run [h12, h80, BitVec.msb_eq_decide, toInt_small xl (by omega)] until [0x5f1b40]
  have hpx' : Apart p (8 * c) xp.toNat (8 * xl.toNat) := hpx
  have hP := bm_pre (S1 := { S with
      regs := setRegF (setRegF (setRegF (setRegF (setRegF (setRegF (setRegF S.regs 4 (s.regs 4 - 176#64)) 6 xl) 7 xp)
        8 xc) 9 xp) 10 xl) 11 xc,
      rip := 6232896#64, flags := (subFlags (80#64) xl false).snd,
      mem := Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 176) 8 6230377, df := false }) hJ hpx' hx2
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14) hfs
    (by simp only [win]; janus_frame) (by simp only [Arm64.Memory.regions_writeLE]; exact hreg)
  rw [IntAS.bv_ofNat_toNat, IntAS.bv_ofNat_toNat] at hP
  have e176 : (s.regs 4 - 176#64).toNat = (s.regs 4).toNat - 176 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine bmCall hap hmc (a0 := BitVec.ofNat 64 p) (a1 := BitVec.ofNat 64 (2 * xl.toNat)) (a2 := BitVec.ofNat 64 c)
    (a3 := xp) (a4 := xl) (a5 := xc) (a6 := xp) (a7 := xl) (a8 := xc) rfl
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e176, Arm64.Memory.readLE_writeLE_self])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact r0)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact r3)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact r1)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (hx15.trans hx150) rfl hP (fun s' hr e4 e5 e14 e15 hq hrg => ?_)
  simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] at e4 e5 e14 e15
  obtain ⟨qfs, qdf, hval, L2, b2, hext, hbb, hinv2, hF2, hLF2⟩ := hq
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hlive := hJ.live (by omega)
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hlive
  have tp : (BitVec.ofNat 64 p).toNat = p := IntAS.tN (by omega)
  simp only [win, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e176, tp] at hF2 hLF2 hval hinv2
  rw [h14] at hinv2
  have hS : MemFrame S.mem (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 176) 8 6230377) (win s W 64) := by simp only [win]; janus_frame
  have hrd : ∀ a, (s.regs 4).toNat - 104 ≤ a → a + 8 ≤ (s.regs 4).toNat + 8 → s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    rw [hF2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega⟩, by omega⟩),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have q64 := (hrd _ (by omega) (by omega)).trans m64
  have q80 := (hrd _ (by omega) (by omega)).trans m80
  have q88 := (hrd _ (by omega) (by omega)).trans m88
  have qra := (hrd _ (by omega) (by omega)).trans mra
  have qbp := (hrd _ (by omega) (by omega)).trans mbp
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hF2.accessible, hS.accessible]
  have hsacc : s'.mem.accessible ((s.regs 4).toNat - 168) 176 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp' : s'.regs 4 = s.regs 4 - 168#64 := by rw [e4]; exact e168
  have hxv := hJ.xv (by omega)
  have hxS : natVal (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 176) 8 6230377) xp.toNat xl.toNat = natVal S.mem xp.toNat xl.toNat := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hxw, -⟩ := hJ.pre
    have := hxw (by omega); simp only [win, outside_cons, outside_nil, and_true] at this
    exact natVal_frame hS (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hval' : natVal s'.mem p (2 * xl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [show 2 * xl.toNat = xl.toNat + xl.toNat by omega, hval, hxS, hxv]
  have hstkS : StkOK (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 176) 8 6230377) R L1 st.toNat := stkOK_frame hJ.stk hS (by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
    exact hstw)
  have hpst := hJ.pst (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hpst
  janus64_run [q64, q80, hsp', BitVec.msb_eq_decide] until [hnormM]
  have hsbk := stackBack_keepC hstkS (ws := [((s.regs 4).toNat - 176 - 4224, (s.regs 4).toNat - 176 + 72)] ++
          [(p, p + 8 * (xl.toNat + xl.toNat))])
        (by rw [← List.append_assoc]; exact hF2)
        (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by simp only [outside_append] at h; exact h.2)
        (by simp only [outside_append, outside_cons, outside_nil, and_true]; omega) hext
  refine normM impl s s'.mem p c (2 * xl.toNat) (natVal s'.mem p (2 * xl.toNat)) _
    (fun s3 n' hF3 q0 q1 q2 qfs3 qdf3 hn' hv' hnn => post_of hJ hS hval' hext (k := 0) (Or.inr ⟨by omega, hsbk.2⟩)
      (by unfold sqrCQ; rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; omega) hinv2
      hsbk.1
      (hF2.mono fun a n h => by
        simp only [stkWs, win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        exact ⟨⟨h.1.1, by omega⟩, by have := h.2.1; omega⟩)
      (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      (hF3.mono fun a n h => by simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega)
      qfs3 qdf3 q0 q1 q2 hn' hv' hnn)
    hcap (by omega) (by omega)
    (by rw [hacc2]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qra qbp q88 hal0 (by omega) (by omega) hsacc hra (2 * xl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  all_goals try janus64_simp
  all_goals exact qfs.trans hfs

end FvModexp.Amd64.Q.NatSqr
