import FvModexp.Proofs.Amd64.NatQ.SqrKPre
import FvModexp.Proofs.Amd64.NatQ.SqrBM

set_option autoImplicit false

/-!
# [TIGHT COSTS, divmc s38] `nat.sqr` (amd64), `80 ≤ n`, `stk ≠ nil`: `karatsubaSqr(stk, z, x); return z.norm()` (natmul.go:105-106)

Twin of Arm64/NatQ/SqrKS.lean on the amd64 layout of SqrBS: `ks` = the join (`0x5f1140`, both thresholds compared,
`TESTQ DI, DI` with `stk ≠ nil`, the defer bit cleared, `CMPQ karatsubaSqrThreshold` taken) → `CALL karatsubaSqr`
(`0x5f125a`, entry `0x5f2380`, return `0x5f125f`; `AX = stk`, `BX = p`, `CX = 2n`, `DI = c`, `SI/R8/R9 = x`); `ksCall`
= the call through the SCC's induction hypothesis (`IH … (true, a)`, measure `2n < 2n + 1`; pre `ks_pre`); `ks2` = the
return (`MOVQ 0x68(SP), BX; MOVQ 0x58(SP), CX`) → `normK` and `post_of`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
/-- a call of `karatsubaSqr` through the induction hypothesis at its entry `0x5f2380` returning to `0x5f125f` -/
theorem ksCall {impl : List Amd64.Segment} {R : RtInv} {n : Nat} (hih : ∀ a, IH impl R H n (true, a)) (a : Args)
    {S : State} {ret : W64} {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 0x5f2380) (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f125f)
    (h0 : S.regs 0 = a.a0) (h3 : S.regs 3 = a.a1) (h1 : S.regs 1 = a.a2) (h7 : S.regs 7 = a.a3) (h6 : S.regs 6 = a.a4)
    (h8 : S.regs 8 = a.a5) (h9 : S.regs 9 = a.a6)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hpre : KPre R a.b H a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat S)
    (hmu : 2 * a.a5.toNat < n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f125f → Kept S s' →
      KPost R a.b H a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a4.toNat a.a5.toNat S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibSqr.program.link impl) ret s' Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  have hS : Summary (LibSqr.program.link impl) 0x5f2380 (fun s => preOf R H (true, a) s ∧ μ (true, a) s < n)
      (postOf R H (true, a)) := hih a
  refine ReachesRet.call_regions hS hpc ⟨⟨⟨?_, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩, hpre⟩, hmu⟩
    fun s' hr ⟨hk, hq⟩ hrg => K s' ?_ hk hq hrg
  · rw [hrd]; decide
  · rw [hr, retAddrOf, hrd]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `karatsubaSqr` entry (`CALL` at `0x5f125a` done) to the return of `nat.sqr` -/
theorem ks2 (impl : List Amd64.Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 M)
    (hih : ∀ a, IH impl R H (2 * xl.toNat + 1) (true, a))
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hna : p + 8 * c ≠ xp.toNat + 8 * xc.toNat) (hx80 : 80 ≤ xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 0x5f2380) (hsp : S.regs 4 = s.regs 4 - 176#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hfs : S.fsBase = s.fsBase)
    (hdf : S.df = false) (hx15 : S.xmm 15 = 0)
    (r0 : S.regs 0 = st) (r3 : S.regs 3 = BitVec.ofNat 64 p) (r1 : S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat))
    (r7 : S.regs 7 = BitVec.ofNat 64 c) (r6 : S.regs 6 = xp) (r8 : S.regs 8 = xl) (r9 : S.regs 9 = xc)
    (hF : MemFrame M S.mem (win s W 64)) (hreg : S.mem.regions = s.mem.regions)
    (mret : S.mem.readLE ((s.regs 4).toNat - 176) 8 = 0x5f125f)
    (mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m64 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = p) (m80 : S.mem.readLE ((s.regs 4).toNat - 80) 8 = 2 * xl.toNat)
    (m88 : S.mem.readLE ((s.regs 4).toNat - 88) 8 = c) (m89 : S.mem.readLE ((s.regs 4).toNat - 89) 1 = 0) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
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
  have hK : KPre R b1 H L1 (W - 176) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * xl.toNat)).toNat
      (BitVec.ofNat 64 c).toNat xp.toNat xl.toNat xc.toNat S := by
    rw [tp, t2, tc]; exact ks_pre hJ hpx hna hx80 hsp' h14 hfs hF hreg
  refine ksCall hih ⟨b1, L1, W - 176, st, BitVec.ofNat 64 p, BitVec.ofNat 64 (2 * xl.toNat),
    BitVec.ofNat 64 c, xp, xl, xc⟩ hpc (by rw [hsp']; exact mret) r0 r3 r1 r7 r6 r8 r9
    hx15 hdf hK
    (show 2 * xl.toNat < 2 * xl.toNat + 1 by omega)
    (fun s' hr ⟨e4, e5, e14, e15⟩ hq hrg => ?_)
  obtain ⟨qfs, qdf, hval, L2, b2, hext, hbb, hinv2, hsb, hF2, hLF2⟩ := hq
  simp only [tp, t2] at hval hF2 hLF2
  rw [h14] at hinv2
  simp only [win, hsp'] at hF2
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
  have hsc : sqrCQ xl.toNat = makeB (2 * xl.toNat) + ksqrCQ xl.toNat := by
    unfold sqrCQ; rw [if_pos (by omega)]
  janus64_run [q64, q80, hsp2, BitVec.msb_eq_decide] until [hnormK]
  refine normK impl s s'.mem p c (2 * xl.toNat) (natVal s'.mem p (2 * xl.toNat)) _
    (fun s3 n' hF3 q0 q1 q2 qfs3 qdf3 hn' hv' hnn => post_of hJ hF hval' hext
      (k := ksqrCQ xl.toNat) (Or.inl hbb) (by rw [hsc]; omega) hinv2 hsb
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
/-- **the `karatsubaSqr` path** (`80 ≤ n`, `stk ≠ nil`) from the join `0x5f1140` -/
theorem ks (impl : List Amd64.Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem)
    (hih : ∀ a, IH impl R H (2 * xl.toNat + 1) (true, a))
    (hA : JoinAt s S p c st xp xl xc) (hx80 : 80 ≤ xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ SPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  obtain ⟨h12, h80, hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r3, r1, r7, r6, r8, r9, hsp, h14, h5, hfs, hdf, hx15, mra, mbp, m64, m80, m88, hreg, hpx, hna⟩ := hA
  have hst0' : (st = 0#64) = False := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    simp only [eq_iff_iff, iff_false]; intro e; apply h; rw [e]; rfl
  have hpre := hJ.pre
  obtain ⟨hce, hsw, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, -, -, -, -, -, -, hxl12, -⟩ := hJ.pre
  have hwS : S.mem.accessible ((s.regs 4).toNat - W) (W + 64) true = true := by rw [hJ.F.accessible]; exact hw0
  have hgw : 11841160 + 32 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 64 ≤ 11841160 := by
    obtain ⟨-, -, -, ⟨-, -, -, -, -, -, -, -, -, hgw, -⟩, -⟩ := hJ.pre
    have eg : RunIface.gA = 11841160 := rfl
    rw [eg] at hgw; simp only [win, outside_cons, outside_nil, and_true] at hgw; omega
  janus64_run [h12, h80, hst0', BitVec.msb_eq_decide, toInt_small xl (by omega)] until [0x5f2380]
  refine ks2 impl R hJ hih hpx hna hx80 hra hx150 hdf0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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

end FvModexp.Amd64.Q.NatSqr
