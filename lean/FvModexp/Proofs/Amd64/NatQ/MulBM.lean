import FvModexp.Proofs.Amd64.NatQ.MulBMP
import FvModexp.Proofs.Amd64.NatQ.MulNorm
import FvModexp.Proofs.Amd64.Int.IntASCallH
import FvModexp.Proofs.Amd64.Nat.Callees2
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.DivmcMem

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulBM.lean — TIGHT COSTS] `nat.mul` (amd64), `2 ≤ n < 40`: `basicMul(z, x, y); return z.norm()` (natmul.go:37-39)

From the join (`0x5f09d5`, `CMPQ karatsubaThreshold, R10; JG` taken): `MOVQ SI, DI; MOVQ R8, SI; MOVQ R9, R8;
MOVQ DX, R9; CALL basicMul` (`0x5f0bc2`, entry `0x5f1b40`, return `0x5f0bc7` pushed at `RSP - 264`; `AX, BX, CX = z`,
`DI, SI, R8 = x`, `R9, R10, R11 = y`), then `MOVQ 0x90(SP), AX; MOVQ 0x70(SP), BX` → `normA` and `post_of`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (stackBack_keepC stkOK_frame)

set_option maxRecDepth 20000 in
/-- the return addresses inside `nat.mul` (`seg33`, base `0x5f0840`) are return addresses of a program without it -/
theorem ra_mul {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x705) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x5f0840 + i) := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg33) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5f0840 + i < 2 ^ 47; omega)
  rw [show Extracted.seg33.base = 0x5f0840 from rfl] at this; exact this

set_option maxRecDepth 20000 in
/-- a call of `basicMul` (`BasicMul.ens`) at its entry `0x5f1b40` returning to `0x5f0bc7` -/
theorem bmCallM {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {a0 a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64} {S : State} {ret : W64}
    {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 0x5f1b40) (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f0bc7)
    (h0 : S.regs 0 = a0) (h3 : S.regs 3 = a1) (h1 : S.regs 1 = a2) (h7 : S.regs 7 = a3) (h6 : S.regs 6 = a4)
    (h8 : S.regs 8 = a5) (h9 : S.regs 9 = a6) (h10 : S.regs 10 = a7) (h11 : S.regs 11 = a8)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false) (hpre : BasicMul.Pre R b L a0 a1 a2 a3 a4 a6 a7 S)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f0bc7 → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → BasicMul.Post R b L a0 a3 a4 a6 a7 S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibMul.program.link impl) ret s' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hc : CodeIn64 ((Extracted.program.onlySegments BasicMul.names).link impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hBM := Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b L a0 a1 a2 a3 a4 a5 a6 a7 a8) (A64.noExit_restrict64 hap BasicMul.names) hc
  rw [show segAddr Extracted.program BasicMul.fn = 0x5f1b40 by decide] at hBM
  refine ReachesRet.call_regions hBM hpc ⟨?_, hx15, hdf, ?_⟩ fun s' hr ⟨⟨e4, e5, e14, e15⟩, hq⟩ hrg => ?_
  · simp only [regSP]; rw [hrd]
    exact ra_mul (i := 0x387) hap (by decide) (by decide)
  · rw [h0, h3, h1, h7, h6, h9, h10]; exact hpre
  · rw [h0, h7, h6, h9, h10] at hq
    refine K s' ?_ e4 e5 e14 e15 hq hrg
    rw [hr, retAddrOf, hrd]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem bm (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hsm : yl.toNat < 40)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  obtain ⟨h40, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r3, r1, r7, r6, r8, r9, r2, r10, r11, hsp, h14, h5, hfs, hdf, hx15, mra, mbp, m112, m144, m168,
    m64, m72, m80, m8, m16, m24, hreg, hpx, hpy, -, -⟩ := hA
  have hpre := hJ.pre
  obtain ⟨hce, hmw, -, -, -, ⟨⟨hxlc, hxc40, hxl12, -⟩, ⟨hylc, hyc40, hyl12, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, hal0, -, hout0, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hcap := hJ.cap; have hc40 := hJ.c40
  have e256 : s.regs 4 - 264#64 + 8#64 = s.regs 4 - 256#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e264 : (s.regs 4 - 264#64).toNat = (s.regs 4).toNat - 264 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hwS : S.mem.accessible ((s.regs 4).toNat - W) (W + 88) true = true := by rw [hJ.F.accessible]; exact hw0
  janus64_run [h40, BitVec.msb_eq_decide, toInt_small yl (by omega)] until [0x5f1b40]
  refine bmCallM hap hmc (a0 := BitVec.ofNat 64 p) (a1 := BitVec.ofNat 64 (xl.toNat + yl.toNat))
    (a2 := BitVec.ofNat 64 c) (a3 := xp) (a4 := xl) (a5 := xc) (a6 := yp) (a7 := yl) (a8 := yc) rfl
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e264, Arm64.Memory.readLE_writeLE_self])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact r0 | exact r3 | exact r1 | exact r6 | exact r8 | exact r9 | exact r2 | exact r10 | exact r11)
    (hx15.trans hx150) rfl
    (bm_pre hJ hpx hpy hy2 hyx (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e264)
      (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14) hfs (by simp only [win]; janus_frame)
      (by simp only [Arm64.Memory.regions_writeLE]; exact hreg))
    (fun s' hr e4 e5 e14 e15 hq hrg => ?_)
  simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] at e4 e5 e14 e15
  obtain ⟨qfs, qdf, hval, L2, b2, hext, hbb, hinv2, hF2, hLF2⟩ := hq
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have tp : (BitVec.ofNat 64 p).toNat = p := IntAS.tN (by omega)
  simp only [win, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e264, tp] at hF2 hLF2 hval hinv2
  rw [h14] at hinv2
  have hS : MemFrame S.mem (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 264) 8 0x5f0bc7) (win s W 88) := by
    simp only [win]; janus_frame
  have hrd : ∀ a, (s.regs 4).toNat - 176 ≤ a → a + 8 ≤ (s.regs 4).toNat + 8 → s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    rw [hF2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega⟩, by omega⟩),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have q112 := (hrd _ (by omega) (by omega)).trans m112
  have q144 := (hrd _ (by omega) (by omega)).trans m144
  have q168 := (hrd _ (by omega) (by omega)).trans m168
  have qra := (hrd _ (by omega) (by omega)).trans mra
  have qbp := (hrd _ (by omega) (by omega)).trans mbp
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hF2.accessible, hS.accessible]
  have hsacc : s'.mem.accessible ((s.regs 4).toNat - 256) 264 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp' : s'.regs 4 = s.regs 4 - 256#64 := by rw [e4]; exact e256
  have hxv := hJ.xv (by omega)
  have hyv := hJ.yv (by omega)
  obtain ⟨-, -, -, -, -, ⟨⟨-, -, -, -, -, hxw⟩, ⟨-, -, -, -, -, hyw⟩, -⟩, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  have hxw' := (hxw (by omega)).1; have hyw' := (hyw (by omega)).1
  simp only [win, outside_cons, outside_nil, and_true] at hxw' hyw' hstw
  have hxS : natVal (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 264) 8 0x5f0bc7) xp.toNat xl.toNat =
      natVal S.mem xp.toNat xl.toNat :=
    natVal_frame hS (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hyS : natVal (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 264) 8 0x5f0bc7) yp.toNat yl.toNat =
      natVal S.mem yp.toNat yl.toNat :=
    natVal_frame hS (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hval' : natVal s'.mem p (xl.toNat + yl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat := by
    rw [hval, hxS, hyS, hxv, hyv]
  have hstkS : StkOK (Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 264) 8 0x5f0bc7) R L1 st.toNat :=
    stkOK_frame hJ.stk hS (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hpst := hJ.pst (by omega)
  unfold Apart at hpst
  janus64_run [q112, q144, hsp', BitVec.msb_eq_decide] until [hnormA]
  have hsbk := stackBack_keepC hstkS (ws := [((s.regs 4).toNat - 264 - 4224, (s.regs 4).toNat - 264 + 72)] ++
          [(p, p + 8 * (xl.toNat + yl.toNat))])
        (by rw [← List.append_assoc]; exact hF2)
        (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by simp only [outside_append] at h; exact h.2)
        (by simp only [outside_append, outside_cons, outside_nil, and_true]; omega) hext
  refine normA impl s s'.mem p c (xl.toNat + yl.toNat) (natVal s'.mem p (xl.toNat + yl.toNat)) _
    (fun s3 n' hF3 q0 q1 q2 qfs3 qdf3 hn' hv' hnn => post_of hJ hS hval' hext (k := 0) (Or.inr ⟨by omega, hsbk.2⟩)
      (by unfold mulCQ; rw [Nat.max_eq_left hyx, Nat.min_eq_right hyx]; have := MCQ_basic (m := xl.toNat) hy2; omega)
      hinv2 hsbk.1
      (hF2.mono fun a n h => by
        simp only [stkWs, win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        exact ⟨⟨h.1.1, by omega⟩, by have := h.2.1; omega⟩)
      (FvModexp.LiveFrame.mono_ws hLF2 fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      (hF3.mono fun a n h => by simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega)
      qfs3 qdf3 q0 q1 q2 hn' hv' hnn)
    hcap (by omega) (by omega)
    (by rw [hacc2]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qra qbp q168 hal0 (by omega) (by omega) hsacc hra (xl.toNat + yl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ rfl rfl
  all_goals try janus64_simp
  all_goals exact qfs.trans hfs

end FvModexp.Amd64.Q.NatMul
