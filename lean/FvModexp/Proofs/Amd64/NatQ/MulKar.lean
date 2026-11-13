import FvModexp.Proofs.Amd64.NatQ.MulKPre
import FvModexp.Proofs.Amd64.NatQ.MulNorm
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.OmegaOnly

set_option autoImplicit false

/-!
# [amd64 port (divmc s45) of the Q-form Arm64/NatQ/MulKar.lean — TIGHT COSTS] `nat.mul` (amd64), `40 ≤ n = m`, `stk ≠ nil`: `karatsuba(stk, z[:2n], x[:n], y); return z.norm()` (natmul.go:42-55)

Layout (amd64 `nat.mul`, `SP' = RSP - 256`): the join `0x5f09d5` (`JoinAt`) → `CMPQ karatsubaThreshold, R10` (not
taken: `40 ≤ n`) → `TESTQ DI, DI` (`stk ≠ nil`: `R12 = 0`, `JMP 0x5f0a9f`) → `R13 = 2n` (`CMPQ CX, R13` bound check
passes: `2n ≤ c`), spills `2n` at `0x88(SP')`, the defer bit `0` at `0x56(SP')` (= `RSP - 170`), `stk` at `0xb8(SP')`,
`y` to the outgoing stack arguments `0/8/16(SP')` → `CALL karatsuba` (`0x5f0ae0`, entry `0x5f1da0`, return `0x5f0ae5`;
`AX = stk`, `BX = p`, `CX = 2n`, `DI = c`, `SI/R8/R9 = x[:n]`). `karCall` = the call through the SCC's induction
hypothesis (`IH … (.kar, a)`); `kar2` = the return: `CMPQ m, n` (`JG` not taken: `m = n`), `AX = 0x56(SP')`,
`JMP 0x5f0e02` (`SI = p`, `BX = m + n`) → `normB` (`bits = 0`) → `retB0` and `post_of`. `karEq` = the join → the call.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem rr_mono {p : Amd64.Program} {ret : W64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h; exact ⟨k, s', hs, hr, hQ s' hq⟩

set_option maxRecDepth 20000 in
/-- a call of `karatsuba` through the induction hypothesis at its entry `0x5f1da0` returning to `0x5f0ae5` -/
theorem karCall {impl : List Amd64.Segment} {R : RtInv} {n : Nat} (hih : ∀ a, IH impl R H n (.kar, a)) (a : Args)
    {S : State} {ret : W64} {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 0x5f1da0) (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f0ae5)
    (h0 : S.regs 0 = a.a0) (h3 : S.regs 3 = a.a1) (h1 : S.regs 1 = a.a2) (h7 : S.regs 7 = a.a3) (h6 : S.regs 6 = a.a4)
    (h8 : S.regs 8 = a.a5) (h9 : S.regs 9 = a.a6)
    (m8 : S.mem.readLE ((S.regs 4).toNat + 8) 8 = a.a7.toNat) (m16 : S.mem.readLE ((S.regs 4).toNat + 16) 8 = a.a8.toNat)
    (m24 : S.mem.readLE ((S.regs 4).toNat + 24) 8 = a.a9.toNat)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hpre : KPre R a.b H a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat
      a.a7.toNat a.a8.toNat a.a9.toNat S)
    (hmu : 8 * a.a8.toNat + 2 < n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f0ae5 → Kept S s' →
      KPost R a.b H a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a4.toNat a.a5.toNat a.a7.toNat a.a8.toNat S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibMul.program.link impl) ret s' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hS : Summary (LibMul.program.link impl) 0x5f1da0 (fun s => preOf R H (.kar, a) s ∧ μ (.kar, a) s < n)
      (postOf R H (.kar, a)) := hih a
  refine ReachesRet.call_regions hS hpc ⟨⟨⟨?_, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, m8, m16, m24⟩, hpre⟩, hmu⟩
    fun s' hr ⟨hk, hq⟩ hrg => K s' ?_ hk hq hrg
  · rw [hrd]; decide
  · rw [hr, retAddrOf, hrd]

/-- `win s W 88` covers `kar2`'s frame and `karatsuba`'s window (a small-context `omega`, kept out of `kar2`'s large
context: 13 s → 0) -/
theorem karWin {sp W a n : Nat} (h : a + n ≤ sp - W ∨ sp + 88 ≤ a) (hW : 4608 ≤ W) :
    a + n ≤ sp - 264 - (W - 264) ∨ sp - 264 + 72 ≤ a := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- from the `karatsuba` entry (`CALL` at `0x5f0ae0` done) to the return of `nat.mul` -/
theorem kar2 (impl : List Amd64.Segment) (R : RtInv) (n0 : Nat)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hih : ∀ a, IH impl R H n0 (.kar, a))
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hnx : p + 8 * c ≠ xp.toNat + 8 * xc.toNat) (hny : p + 8 * c ≠ yp.toNat + 8 * yc.toNat)
    (h40 : 40 ≤ yl.toNat) (hmn : xl.toNat = yl.toNat) (hμ : 8 * yl.toNat + 2 < n0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 0x5f1da0) (hsp : S.regs 4 = s.regs 4 - 264#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hfs : S.fsBase = s.fsBase)
    (hdf : S.df = false) (hx15 : S.xmm 15 = 0)
    (r0 : S.regs 0 = st) (r3 : S.regs 3 = BitVec.ofNat 64 p) (r1 : S.regs 1 = BitVec.ofNat 64 (2 * yl.toNat))
    (r7 : S.regs 7 = BitVec.ofNat 64 c) (r6 : S.regs 6 = xp) (r8 : S.regs 8 = yl) (r9 : S.regs 9 = xc)
    (hF : MemFrame M S.mem (win s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (mret : S.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0ae5)
    (my0 : S.mem.readLE ((s.regs 4).toNat - 256) 8 = yp.toNat)
    (my1 : S.mem.readLE ((s.regs 4).toNat - 248) 8 = yl.toNat)
    (my2 : S.mem.readLE ((s.regs 4).toNat - 240) 8 = yc.toNat)
    (mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m112 : S.mem.readLE ((s.regs 4).toNat - 112) 8 = p)
    (m144 : S.mem.readLE ((s.regs 4).toNat - 144) 8 = xl.toNat + yl.toNat)
    (m168 : S.mem.readLE ((s.regs 4).toNat - 168) 8 = c) (m170 : S.mem.readLE ((s.regs 4).toNat - 170) 1 = 0)
    (m72 : S.mem.readLE ((s.regs 4).toNat + 72) 8 = xl.toNat)
    (m16 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre := hJ.pre
  obtain ⟨hce, hmw, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, hal0, -, hout0, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hp64 : p < 2 ^ 64 := by omega
  have e264 : (s.regs 4 - 264#64).toNat = (s.regs 4).toNat - 264 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 264 := by rw [hsp, e264]
  have tp : (BitVec.ofNat 64 p).toNat = p := IntAS.tN hp64
  have t2 : (BitVec.ofNat 64 (2 * yl.toNat)).toNat = 2 * yl.toNat := IntAS.tN (by omega)
  have tc : (BitVec.ofNat 64 c).toNat = c := IntAS.tN (by omega)
  have hK : KPre R b1 H L1 (W - 264) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * yl.toNat)).toNat
      (BitVec.ofNat 64 c).toNat xp.toNat yl.toNat xc.toNat yp.toNat yl.toNat yc.toNat S := by
    rw [tp, t2, tc]; exact kpre_of hJ hpx hpy hnx hny h40 (Nat.le_of_eq hmn.symm) hsp' h14 hfs hF hreg
  refine karCall hih ⟨b1, L1, W - 264, st, BitVec.ofNat 64 p, BitVec.ofNat 64 (2 * yl.toNat),
    BitVec.ofNat 64 c, xp, yl, xc, yp, yl, yc⟩ hpc (by rw [hsp']; exact mret) r0 r3 r1 r7 r6 r8 r9
    (by rw [hsp', show (s.regs 4).toNat - 264 + 8 = (s.regs 4).toNat - 256 by omega]; exact my0)
    (by rw [hsp', show (s.regs 4).toNat - 264 + 16 = (s.regs 4).toNat - 248 by omega]; exact my1)
    (by rw [hsp', show (s.regs 4).toNat - 264 + 24 = (s.regs 4).toNat - 240 by omega]; exact my2)
    hx15 hdf hK hμ (fun s' hr ⟨e4, e5, e14, e15⟩ hq hrg => ?_)
  obtain ⟨qfs, qdf, hval, L2, b2, hext, hbb, hinv2, hsb, hF2, hLF2⟩ := hq
  simp only [tp, t2] at hval hF2 hLF2
  rw [h14] at hinv2
  simp only [win, hsp'] at hF2
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hstw, -, -, -, hfw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfw
  have h264 : 264 ≤ (s.regs 4).toNat := by omega
  have hrd' : ∀ a n, (s.regs 4).toNat - 184 ≤ a → a + n ≤ (s.regs 4).toNat + 88 →
      s'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    clear mret my0 my1 my2 mra mbp m112 m144 m168 m170 m72 m16 hra hih
    refine hF2.readLE _ _ ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [eW, eL, eC]
    refine ⟨⟨hout0.of_sub (by omega) (by omega), ?_⟩, ?_⟩
    · omega
    · and_intros <;> omega
  have q112 := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans m112
  have q144 := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans m144
  have q168 := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans m168
  have q170 := (hrd' _ 1 (by omega_only [h264]) (by omega_only [h264])).trans m170
  have q72 := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans (m72.trans hmn)
  have q16 := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans m16
  have qra := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans mra
  have qbp := (hrd' _ 8 (by omega_only [h264]) (by omega_only [h264])).trans mbp
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF.accessible]
  have hsacc8 : s'.mem.accessible ((s.regs 4).toNat - 256) 344 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsacc : s'.mem.accessible ((s.regs 4).toNat - 256) 264 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hsacc8 (by omega) (by omega)
  have hsp2 : s'.regs 4 = s.regs 4 - 256#64 := by
    rw [e4, hsp]; apply BitVec.eq_of_toNat_eq
    have e8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8]; omega
  obtain ⟨-, -, -, -, -, ⟨⟨-, -, -, -, -, hxw⟩, ⟨-, -, -, -, -, hyw⟩, -⟩, -⟩ := hJ.pre
  have hxS : natVal S.mem xp.toNat yl.toNat = natVal M xp.toNat xl.toNat := by
    rw [← hmn]; exact natVal_frame hF (hxw (by omega)).1
  have hyS : natVal S.mem yp.toNat yl.toNat = natVal M yp.toNat yl.toNat := natVal_frame hF (hyw (by omega)).1
  have hval' : natVal s'.mem p (xl.toNat + yl.toNat) =
      natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat := by
    rw [show xl.toNat + yl.toNat = 2 * yl.toNat by omega, hval, hxS, hyS, hJ.xv (by omega), hJ.yv (by omega)]
  have hk : makeB (xl.toNat + yl.toNat) + KCQ yl.toNat ≤ mulCQ xl.toNat yl.toNat := by
    unfold mulCQ; rw [hmn, Nat.max_self, Nat.min_self]; exact MCQ_kar h40
  clear mret my0 my1 my2 mra mbp m112 m144 m168 m170 m72 m16 hrd' hxS hyS hxw hyw hih hpx hpy
  have hF2' : MemFrame S.mem s'.mem (R.rt ++ win s W 88 ++ (p, p + 8 * (xl.toNat + yl.toNat)) :: stkWs S.mem st.toNat) :=
    hF2.mono fun a n h => by
      rw [show 2 * yl.toNat = xl.toNat + yl.toNat by omega]
      simp only [stkWs, win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      exact ⟨⟨h1, karWin h2 hW⟩, h3⟩
  have hLF2' : LiveFrame S.mem s'.mem L1 ((p, p + 8 * (xl.toNat + yl.toNat)) :: stkWs S.mem st.toNat) := by
    rw [show xl.toNat + yl.toNat = 2 * yl.toNat by omega]; exact hLF2
  clear hpw hstw hfw
  janus64_run [q72, q16, q170, q112, q144, hsp2, BitVec.msb_eq_decide] until [hnormB]
  refine normB impl s s'.mem p c (xl.toNat + yl.toNat) (natVal s'.mem p (xl.toNat + yl.toNat)) 0
    (fun s3 => Kept s s3 ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s3)
    (fun S' n' hB hn' hv hnn => by
      have F3 : MemFrame s'.mem S'.mem (win s W 88) := hB.fr.mono fun a n h => by
        simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega
      refine rr_mono (retB0 impl s S' s'.mem p c n' hB qra qbp hal0 (by omega) (by omega) hsacc hra (by omega)
        (by omega) (by omega)) fun s3 ⟨hk3, hm3, q0, q1, q2, qfs3, qdf3⟩ => ⟨hk3, ?_⟩
      exact post_of hJ hF hval' hext (k := KCQ yl.toNat) (Or.inl hbb) hk hinv2 hsb hF2' hLF2'
        (by rw [hm3]; exact F3) qfs3 qdf3 q0 q1 q2 hn' hv hnn)
    hcap (by omega) (by omega)
    (by rw [hacc2]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    q168 (by decide) hal0 (by omega) (by omega) hsacc (xl.toNat + yl.toNat) _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ rfl rfl
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
/-- **the `karatsuba` path** (`40 ≤ n = m`, `stk ≠ nil`) from the join `0x5f09d5` -/
theorem karEq (impl : List Amd64.Segment) (R : RtInv) (n0 : Nat)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hih : ∀ a, IH impl R H n0 (.kar, a))
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (h40 : 40 ≤ yl.toNat) (hmn : xl.toNat = yl.toNat)
    (hμ : 8 * yl.toNat + 2 < n0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  obtain ⟨h40', hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r3, r1, r7, r6, r8, r9, r2, r10, r11, hsp, h14, h5, hfs, hdf, hx15, mra, mbp, m112, m144, m168,
    m64, m72, m80, m8, m16, m24, hreg, hpx, hpy, hnx, hny⟩ := hA
  have hst0' : (st = 0#64) = False := by
    obtain ⟨-, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    simp only [eq_iff_iff, iff_false]; intro e; apply h; rw [e]; rfl
  have hpre := hJ.pre
  obtain ⟨hce, hmw, -, -, -, ⟨-, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hc2 : (BitVec.ofNat 64 c).toNat = c := IntAS.tN (by omega)
  have hwS : S.mem.accessible ((s.regs 4).toNat - W) (W + 88) true = true := by rw [hJ.F.accessible]; exact hw0
  janus64_run [h40', hst0', hc2, BitVec.msb_eq_decide, toInt_small yl (by omega)] until [0x5f1da0]
  refine kar2 impl R n0 hJ hih hpx hpy hnx hny h40 hmn hμ hra hx150 hdf0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [win]; janus_frame) ?qreg ?qret ?qy0 ?qy1 ?qy2 ?qra ?qbp ?q112 ?q144 ?q168 ?q170 ?q72 ?q16
  case qreg => janus64_simp <;> exact hreg
  case qra => janus64_simp <;> exact mra
  case qbp => janus64_simp <;> exact mbp
  case q112 => janus64_simp <;> exact m112
  case q144 => janus64_simp <;> exact m144
  case q168 => janus64_simp <;> exact m168
  case q72 => janus64_simp <;> exact m72
  case q16 => janus64_simp <;> exact m16
  all_goals try janus64_simp
  all_goals first
    | exact h14
    | exact hfs
    | exact (hx15.trans hx150)
    | exact r7
    | exact r6
    | exact r9
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
