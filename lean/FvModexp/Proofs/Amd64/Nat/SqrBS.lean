import FvModexp.Proofs.Amd64.Nat.SqrBM
import FvModexp.Proofs.Amd64.Nat.StackNat

set_option autoImplicit false

/-!
# `nat.sqr` (amd64), `12 ≤ n < 80`, `stk ≠ nil`: `basicSqr(stk, z, x); return z.norm()` (natmul.go:100-103)

`bs`: the join (`0x5f1140`, both thresholds compared; `TESTQ DI, DI` with `stk ≠ nil`; `XORL DX, DX`; `MOVB DL, 0x4f(SP)`
clears the defer bit; `CMPQ karatsubaSqrThreshold`) → `CALL basicSqr` (`0x5f1231`, entry `0x5f14a0`, return `0x5f1236`;
`AX = stk`, `BX = p`, `CX = 2n`, `DI = c`, `SI/R8/R9 = x`); the call via `ReachesRet.call_regions` with `BasicSqr.ens`
(`StackNat.hypL`; pre `bs_pre`); then `MOVQ 0x68(SP), BX; MOVQ 0x58(SP), CX` → `normS` and `post_of`. Twin of the arm64
module (divmc s32).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.NatSqr

set_option maxRecDepth 20000 in
/-- a call of `basicSqr` (`BasicSqr.ens`) at its entry `0x5f14a0` returning to `0x5f1236` -/
theorem bsCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {a0 a1 a2 a3 a4 a5 a6 : BitVec 64} {S : State} {ret : W64}
    {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 0x5f14a0) (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f1236)
    (h0 : S.regs 0 = a0) (h3 : S.regs 3 = a1) (h1 : S.regs 1 = a2) (h7 : S.regs 7 = a3) (h6 : S.regs 6 = a4)
    (h8 : S.regs 8 = a5) (h9 : S.regs 9 = a6)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hpre : BasicSqr.Pre R b L a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat a5.toNat S)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f1236 → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      BasicSqr.Post R b L a0.toNat a1.toNat a2.toNat a4.toNat a5.toNat S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibSqr.program.link impl) ret s' Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  have hc : CodeIn64 ((Extracted.program.onlySegments BasicSqr.names).link impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hBS := Ensures.toSummaryRegs7 (fun a0 a1 a2 a3 a4 a5 a6 =>
    BasicSqr.ens impl hap R hgr hmc hwb b L a0 a1 a2 a3 a4 a5 a6) (A64.noExit_restrict64 hap BasicSqr.names) hc
  rw [show segAddr Extracted.program BasicSqr.fn = 0x5f14a0 by decide] at hBS
  refine ReachesRet.call_regions hBS hpc ⟨?_, hx15, hdf, ?_⟩ fun s' hr ⟨⟨e4, e5, e14, e15⟩, hq⟩ hrg => ?_
  · simp only [regSP]; rw [hrd]
    exact ra_sqr (i := 0x256) hap (by decide) (by decide)
  · rw [h0, h3, h1, h7, h6, h8]; exact hpre
  · rw [h0, h3, h1, h6, h8] at hq
    refine K s' ?_ e4 e5 e14 e15 hq hrg
    rw [hr, retAddrOf, hrd]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `basicSqr` entry (`CALL` at `0x5f1231` done) to the return of `nat.sqr` -/
theorem bs2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hx12 : 12 ≤ xl.toNat) (hsm : xl.toNat < 80)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 0x5f14a0) (hsp : S.regs 4 = s.regs 4 - 176#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hfs : S.fsBase = s.fsBase)
    (hdf : S.df = false) (hx15 : S.xmm 15 = 0)
    (r0 : S.regs 0 = st) (r3 : S.regs 3 = BitVec.ofNat 64 p) (r1 : S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat))
    (r7 : S.regs 7 = BitVec.ofNat 64 c) (r6 : S.regs 6 = xp) (r8 : S.regs 8 = xl) (r9 : S.regs 9 = xc)
    (hF : MemFrame M S.mem (win s W 64)) (hreg : S.mem.regions = s.mem.regions)
    (mret : S.mem.readLE ((s.regs 4).toNat - 176) 8 = 0x5f1236)
    (mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m64 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = p) (m80 : S.mem.readLE ((s.regs 4).toNat - 80) 8 = 2 * xl.toNat)
    (m88 : S.mem.readLE ((s.regs 4).toNat - 88) 8 = c) (m89 : S.mem.readLE ((s.regs 4).toNat - 89) 1 = 0) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ SPost R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, hal0, -, hout0, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hp64 : p < 2 ^ 64 := by omega
  have e176 : (s.regs 4 - 176#64).toNat = (s.regs 4).toNat - 176 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 176 := by rw [hsp, e176]
  have tp : (BitVec.ofNat 64 p).toNat = p := IntAS.tN hp64
  have t2 : (BitVec.ofNat 64 (2 * xl.toNat)).toNat = 2 * xl.toNat := IntAS.tN (by omega)
  have tc : (BitVec.ofNat 64 c).toNat = c := IntAS.tN (by omega)
  refine bsCall hap hgr hmc hwb (a0 := st) (a1 := BitVec.ofNat 64 p) (a2 := BitVec.ofNat 64 (2 * xl.toNat))
    (a3 := BitVec.ofNat 64 c) (a4 := xp) (a5 := xl) (a6 := xc) hpc (by rw [hsp']; exact mret) r0 r3 r1 r7 r6 r8 r9
    hx15 hdf (by rw [tp, t2, tc]; exact bs_pre hJ hpx hx12 hsp' h14 hfs hF hreg)
    (fun s' hr e4 e5 e14 e15 hq hrg => ?_)
  obtain ⟨qfs, qdf, hval, L2, b2, hext, hbb, hinv2, hsb, hF2, hLF2⟩ := hq
  simp only [tp, t2] at hval hF2 hLF2
  rw [h14] at hinv2
  simp only [win, BasicSqr.ws, hsp'] at hF2
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -, -, -, hfw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfw
  have hrd' : ∀ a n, (s.regs 4).toNat - 104 ≤ a → a + n ≤ (s.regs 4).toNat + 8 →
      s'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    refine hF2.readLE _ _ ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [eW, eL, eC]
    refine ⟨⟨hout0.of_sub (by omega) (by omega), ?_⟩, ?_⟩
    · omega
    · and_intros <;> omega
  have q64 := (hrd' _ 8 (by omega) (by omega)).trans m64
  have q80 := (hrd' _ 8 (by omega) (by omega)).trans m80
  have q88 := (hrd' _ 8 (by omega) (by omega)).trans m88
  have q89 := (hrd' _ 1 (by omega) (by omega)).trans m89
  have qra := (hrd' _ 8 (by omega) (by omega)).trans mra
  have qbp := (hrd' _ 8 (by omega) (by omega)).trans mbp
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF.accessible]
  have hsacc : s'.mem.accessible ((s.regs 4).toNat - 168) 176 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp2 : s'.regs 4 = s.regs 4 - 168#64 := by
    rw [e4, hsp]; apply BitVec.eq_of_toNat_eq
    have e8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8]; omega
  have hxv := hJ.xv (by omega)
  have hxS : natVal S.mem xp.toNat xl.toNat = natVal M xp.toNat xl.toNat := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hxw, -⟩ := hJ.pre
    exact natVal_frame hF (hxw (by omega))
  have hval' : natVal s'.mem p (2 * xl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [hval, hxS, hxv]
  have hkc : stackNatCost (stLen s.mem st.toNat) (2 * xl.toNat) ≤ ksqrC (stLen s.mem st.toNat) xl.toNat := by
    rw [ksqrC_small hsm]; exact Nat.le_refl _
  have hsc : sqrC (stLen s.mem st.toNat) xl.toNat = makeB (2 * xl.toNat) + ksqrC (stLen s.mem st.toNat) xl.toNat := by
    unfold sqrC; rw [if_pos hx12]
  rw [eL] at hbb
  janus64_run [q64, q80, hsp2, BitVec.msb_eq_decide] until [hnormS]
  refine normS impl s s'.mem p c (2 * xl.toNat) (natVal s'.mem p (2 * xl.toNat)) _
    (fun s3 n' hF3 q0 q1 q2 qfs3 qdf3 hn' hv' hnn => post_of hJ hF hval' hext
      (k := stackNatCost (stLen s.mem st.toNat) (2 * xl.toNat)) hbb (by rw [hsc]; omega) hinv2 hsb
      (hF2.mono fun a n h => by
        simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        exact ⟨⟨h1, by omega⟩, h3⟩)
      hLF2
      (hF3.mono fun a n h => by simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega)
      qfs3 qdf3 q0 q1 q2 hn' hv' hnn)
    hcap (by omega) (by omega)
    (by rw [hacc2]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    qra qbp q88 q89 hal0 (by omega) (by omega) hsacc hra (2 * xl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  all_goals try janus64_simp
  all_goals first
    | exact qfs.trans hfs
    | exact (qdf.trans hdf).trans hdf0.symm
    | exact (e15.trans hx15).trans hx150.symm
    | exact e5.trans h5
    | exact e14.trans h14
    | fail "SHOW"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `basicSqr` path** (`12 ≤ n < 80`, `stk ≠ nil`) from the join `0x5f1140` -/
theorem bs (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc) (hx12 : 12 ≤ xl.toNat) (hsm : xl.toNat < 80)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ SPost R b L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  obtain ⟨h12, h80, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r3, r1, r7, r6, r8, r9, hsp, h14, h5, hfs, hdf, hx15, mra, mbp, m64, m80, m88, hreg, hpx, -⟩ := hA
  have hst0' : (st = 0#64) = False := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    simp only [eq_iff_iff, iff_false]; intro e; apply h; rw [e]; rfl
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hwS : S.mem.accessible ((s.regs 4).toNat - W) (W + 64) true = true := by rw [hJ.F.accessible]; exact hw0
  have hgw : 11841160 + 32 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 64 ≤ 11841160 := by
    obtain ⟨-, -, -, ⟨-, -, -, -, -, -, -, -, -, hgw, -⟩, -⟩ := hJ.pre
    have eg : RunIface.gA = 11841160 := rfl
    rw [eg] at hgw; simp only [win, outside_cons, outside_nil, and_true] at hgw; omega
  janus64_run [h12, h80, hst0', BitVec.msb_eq_decide, toInt_small xl (by omega)] until [0x5f14a0]
  refine bs2 impl hap R hgr hmc hwb hJ hpx hx12 hsm hra hx150 hdf0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [win]; janus_frame) ?qreg ?qret ?qra ?qbp ?q64 ?q80 ?q88 ?q89
  case qreg => janus64_simp <;> exact hreg
  case qra => janus64_simp <;> exact mra
  case qbp => janus64_simp <;> exact mbp
  case q64 => janus64_simp <;> exact m64
  case q80 => janus64_simp <;> exact m80
  case q88 => janus64_simp <;> exact m88
  all_goals try janus64_simp
  all_goals first
    | exact h14
    | exact hfs
    | exact (hx15.trans hx150)
    | exact r7
    | exact r6
    | exact r8
    | exact r9
    | fail "SHOW"

end FvModexp.Amd64.NatSqr
