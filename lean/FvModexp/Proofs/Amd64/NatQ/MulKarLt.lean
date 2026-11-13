import FvModexp.Proofs.Amd64.NatQ.MulKPre
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Amd64.NatQ.MulLoopClr

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulKarLt.lean — TIGHT COSTS] `nat.mul` (amd64), `40 ≤ n < m`: `karatsuba(stk, z[:2n], x[:n], y)` (natmul.go:51) → `KA` at `0x5f0b05`

`kaOf` (pure): `KA` from `karatsuba`'s post. `karLt2`: from `karatsuba`'s entry `0x5f1da0` (the SCC induction
hypothesis of member `.kar`, as `MulKar.kar2`; `karCallL` = `MulKar.karCall`, copied for a flat chain), the return `0x5f0ae5` and `CMPQ m, n; JG` taken (`n < m`) → `KA`.
`karLt`: the join `0x5f09d5` → the call (as `MulKar.karEq`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (StkPre stackBack_keep')

theorem ws_kar {R : RtInv} {s S1 : State} {W p yl xl st : Nat} {M : Memory}
    (hs1 : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hW : 4608 ≤ W) (hWs : W ≤ (s.regs 4).toNat) (hyx : yl < xl) :
    ∀ a n, Outside a n (R.rt ++ win s W 88 ++ lws M st p (xl + yl)) →
      Outside a n (R.rt ++ win S1 (W - 264) 72 ++ (p, p + 8 * (2 * yl)) :: stkWs M st) := by
  intro a n h
  rw [outside_append, outside_append] at h
  obtain ⟨⟨hr, hw⟩, hl⟩ := h
  simp only [win, outside_cons, outside_nil, and_true] at hw
  simp only [lws, outside_cons] at hl
  obtain ⟨hp, hs⟩ := hl
  rw [outside_append, outside_append]
  simp only [win, outside_cons, outside_nil, and_true]
  rw [hs1]
  simp only [outside_nil, and_true] at hs
  exact ⟨⟨hr, by omega⟩, by omega, hs⟩

theorem lf_kar {M : Memory} {st p yl xl : Nat} (hyx : yl < xl) :
    ∀ a n, Outside a n (lws M st p (xl + yl)) → Outside a n ((p, p + 8 * (2 * yl)) :: stkWs M st) := by
  intro a n h
  simp only [lws, outside_cons] at h ⊢
  obtain ⟨hp, hs⟩ := h
  exact ⟨by omega, hs⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KA` from `karatsuba`'s post** (pure; `S` the callee's entry state, `S2` its return, `S'` at `0x5f0b05`) -/
theorem kaOf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp (8 * xl)) (hpy : Apart p (8 * c) yp (8 * yl)) (h40 : 40 ≤ yl) (hyx : yl < xl)
    {S S2 : State} (hF : MemFrame M S.mem (win s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (hs1 : (S.regs 4).toNat = (s.regs 4).toNat - 264) (hg1 : S.regs 14 = s.regs 14)
    (hq : KPost R b1 H L1 (W - 264) st p (2 * yl) xp yl yp yl S S2) (hreg2 : S2.mem.regions = S.mem.regions)
    (era : S2.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (ebp : S2.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (e168 : S2.mem.readLE ((s.regs 4).toNat - 168) 8 = c)
    (e144 : S2.mem.readLE ((s.regs 4).toNat - 144) 8 = xl + yl)
    (e120 : S2.mem.readLE ((s.regs 4).toNat - 120) 8 = 2 * yl)
    (e112 : S2.mem.readLE ((s.regs 4).toNat - 112) 8 = p)
    (e72 : S2.mem.readLE ((s.regs 4).toNat - 72) 8 = st)
    (e170 : S2.mem.readLE ((s.regs 4).toNat - 170) 1 = 0)
    (x64 : S2.mem.readLE ((s.regs 4).toNat + 64) 8 = xp) (x72 : S2.mem.readLE ((s.regs 4).toNat + 72) 8 = xl)
    (x80 : S2.mem.readLE ((s.regs 4).toNat + 80) 8 = xc) (y8 : S2.mem.readLE ((s.regs 4).toNat + 8) 8 = yp)
    (y16 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = yl) (y24 : S2.mem.readLE ((s.regs 4).toNat + 24) 8 = yc) :
    ∃ (Lk : List (Nat × Nat)) (bk : Nat), ∀ S' : State, S'.mem = S2.mem → S'.rip = BitVec.ofNat 64 0x5f0b05 →
      S'.regs 4 = s.regs 4 - 256#64 → S'.regs 14 = s.regs 14 → S'.regs 5 = s.regs 4 - 8#64 →
      S'.fsBase = s.fsBase → S'.df = s.df → S'.xmm 15 = s.xmm 15 →
      S'.regs 10 = BitVec.ofNat 64 yl → KA R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S' := by
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  obtain ⟨⟨-, ⟨hb0, ha0, hw0⟩, -⟩, hmw, -⟩ := hJ.pre
  simp only [regSP] at hb0 ha0 hw0
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  obtain ⟨-, -, hval, L2, b2, hext, hbud, hinv2, hsb, hMF, hLF⟩ := hq
  rw [hg1] at hinv2
  obtain ⟨-, -, -, -, -, ⟨⟨hxlc, -, -, -, hxh, hxw⟩, ⟨hylc, -, -, -, hyh, hyw⟩, -⟩, -⟩ := hJ.pre
  have hLs := hJ.lsep
  have hxv : natVal S.mem xp yl = natVal s.mem xp yl := by
    rw [natVal_frame hF ((hxw (by omega)).1.of_sub (Nat.le_refl _) (by omega))]; unfold natVal
    exact hJ.rd ((hxh (by omega)).1.sub (Nat.le_refl _) (by omega)) ((hxw (by omega)).1.of_sub (Nat.le_refl _) (by omega))
  have hyv : natVal S.mem yp yl = natVal s.mem yp yl := by
    rw [natVal_frame hF (hyw (by omega)).1, hJ.yv (by omega)]
  have hval' : natVal S2.mem p (2 * yl) = natVal s.mem xp yl * natVal s.mem yp yl := by
    rw [hval, hxv, hyv]
  have eM := hJ.hdr 0 (by omega); have eM8 := hJ.hdr 8 (by omega); have eM16 := hJ.hdr 16 (by omega)
  simp only [Nat.add_zero] at eM
  have eMW : stW M st = stW S.mem st := by simp only [stW]; rw [eM]; exact eW.symm
  have eML : stLen M st = stLen S.mem st := by simp only [stLen]; rw [eM8]; exact eL.symm
  have eMC : stCap M st = stCap S.mem st := by simp only [stCap]; rw [eM16]; exact eC.symm
  have ews : stkWs S.mem st = stkWs M st := by simp only [stkWs]; rw [eMW, eML, eMC]
  rw [ews] at hMF hLF
  rw [stkR_congr eC] at hbud
  have hsb0 : StackBackL R L1 L1 st M S.mem := by
    obtain ⟨-, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
    exact stackBack_keep' hJ.stk (ws := win s W 88) (hF.widen R.rt) (lf_win' _ hF hLs) hstw (LiveExt.refl R L1)
  have hsb2 := sbl_trans hsb0 hsb (LiveExt.refl R L1) hext
  have hws := ws_kar (R := R) (M := M) (st := st) (p := p) hs1 hW hb0 hyx
  have hfr : MemFrame M S2.mem (R.rt ++ win s W 88 ++ lws M st p (xl + yl)) :=
    hF.trans (hMF.mono hws) fun a n h => ⟨by simp only [outside_append] at h; exact h.1.2, h⟩
  have hlf : LiveFrame M S2.mem L1 (lws M st p (xl + yl)) :=
    LiveFrame.trans (lf_win' _ hF hLs) (FvModexp.LiveFrame.mono_ws hLF (lf_kar hyx)) fun _ _ h => h
  refine ⟨L2, b2, fun S' hm hpc hsp h14 h5 hfs hdf hx15 h10 => ?_⟩
  rw [← hm] at hval' hsb2 hfr hlf hinv2 hbud hreg2 era ebp e168 e144 e120 e112 e72 e170 x64 x72 x80 y8 y16 y24
  have hspk : makeB (xl + yl) + KCQ yl ≤ mulCQ xl yl := by
    have hk0 := lsp_end h40 hyx (k := 0) (by omega); simp only [lsp, chunkSum, Nat.add_zero] at hk0; exact hk0
  have hlq : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M L2 b2 (KCQ yl) S'.mem :=
    { core := hJ, h40 := h40, hlt := hyx, ext := hext, bud := hbud, spk := hspk, inv := hinv2,
      reg := hreg2.trans hreg, fr := hfr, lf := hlf, sok := hsb2.1.1, sb := hsb2,
      ra := era, bp := ebp, c58 := e168, n70 := e144, n88 := e120, p90 := e112, sb8 := e72,
      x140 := x64, x148 := x72, x150 := x80, y108 := y8, y110 := y16, y118 := y24, px := hpx, py := hpy }
  exact ⟨hlq, hpc, hsp, h14, h5, hfs, hdf, hx15, h10, e170, hval'⟩

set_option maxRecDepth 20000 in
/-- `MulKar.karCall` (copied so that this module does not import `MulKar`: flat chain) -/
theorem karCallL {impl : List Amd64.Segment} {R : RtInv} {n : Nat} (hih : ∀ a, IH impl R H n (.kar, a)) (a : Args)
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `n < m`, `n ≥ 40`: from `karatsuba`'s entry (`CALL` at `0x5f0ae0` done) through the return `0x5f0ae5` and
`JG` (`n < m`) to `0x5f0b05` (`KA`) -/
theorem karLt2 (impl : List Amd64.Segment) (R : RtInv) (n0 : Nat)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hih : ∀ a, IH impl R H n0 (.kar, a))
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hnx : p + 8 * c ≠ xp.toNat + 8 * xc.toNat) (hny : p + 8 * c ≠ yp.toNat + 8 * yc.toNat)
    (h40 : 40 ≤ yl.toNat) (hyx : yl.toNat < xl.toNat) (hμ : 8 * yl.toNat + 2 < n0)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
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
    (m120 : S.mem.readLE ((s.regs 4).toNat - 120) 8 = 2 * yl.toNat)
    (m144 : S.mem.readLE ((s.regs 4).toNat - 144) 8 = xl.toNat + yl.toNat)
    (m168 : S.mem.readLE ((s.regs 4).toNat - 168) 8 = c) (m170 : S.mem.readLE ((s.regs 4).toNat - 170) 1 = 0)
    (m72s : S.mem.readLE ((s.regs 4).toNat - 72) 8 = st.toNat)
    (m64 : S.mem.readLE ((s.regs 4).toNat + 64) 8 = xp.toNat) (m72 : S.mem.readLE ((s.regs 4).toNat + 72) 8 = xl.toNat)
    (m80 : S.mem.readLE ((s.regs 4).toNat + 80) 8 = xc.toNat) (m8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat)
    (m16 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat) (m24 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (Lk : List (Nat × Nat)) (bk : Nat) (S' : State),
      KA R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M Lk bk S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
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
  have hKp : KPre R b1 H L1 (W - 264) st.toNat (BitVec.ofNat 64 p).toNat (BitVec.ofNat 64 (2 * yl.toNat)).toNat
      (BitVec.ofNat 64 c).toNat xp.toNat yl.toNat xc.toNat yp.toNat yl.toNat yc.toNat S := by
    rw [tp, t2, tc]; exact kpre_of hJ hpx hpy hnx hny h40 (Nat.le_of_lt hyx) hsp' h14 hfs hF hreg
  refine karCallL hih ⟨b1, L1, W - 264, st, BitVec.ofNat 64 p, BitVec.ofNat 64 (2 * yl.toNat),
    BitVec.ofNat 64 c, xp, yl, xc, yp, yl, yc⟩ hpc (by rw [hsp']; exact mret) r0 r3 r1 r7 r6 r8 r9
    (by rw [hsp', show (s.regs 4).toNat - 264 + 8 = (s.regs 4).toNat - 256 by omega]; exact my0)
    (by rw [hsp', show (s.regs 4).toNat - 264 + 16 = (s.regs 4).toNat - 248 by omega]; exact my1)
    (by rw [hsp', show (s.regs 4).toNat - 264 + 24 = (s.regs 4).toNat - 240 by omega]; exact my2)
    hx15 hdf hKp hμ (fun s' hr ⟨e4, e5, e14, e15⟩ hq hrg => ?_)
  have hq' : KPost R b1 H L1 (W - 264) st.toNat p (2 * yl.toNat) xp.toNat yl.toNat yp.toNat yl.toNat S s' := by
    have := hq; simp only [tp, t2] at this; exact this
  have hq'' := hq'
  obtain ⟨qfs, qdf, -, -, -, -, -, -, -, hF2, -⟩ := hq''
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hstw, -, -, -, hfw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfw
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  simp only [win, hsp'] at hF2
  have hrd' : ∀ a n, (s.regs 4).toNat - 184 ≤ a → a + n ≤ (s.regs 4).toNat + 88 →
      s'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    refine hF2.readLE _ _ ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [eW, eL, eC]
    refine ⟨⟨hout0.of_sub (by omega) (by omega), ?_⟩, ?_⟩
    · omega
    · and_intros <;> omega
  have q112 := (hrd' _ 8 (by omega) (by omega)).trans m112
  have q120 := (hrd' _ 8 (by omega) (by omega)).trans m120
  have q144 := (hrd' _ 8 (by omega) (by omega)).trans m144
  have q168 := (hrd' _ 8 (by omega) (by omega)).trans m168
  have q170 := (hrd' _ 1 (by omega) (by omega)).trans m170
  have q72s := (hrd' _ 8 (by omega) (by omega)).trans m72s
  have q64 := (hrd' _ 8 (by omega) (by omega)).trans m64
  have q72 := (hrd' _ 8 (by omega) (by omega)).trans m72
  have q80 := (hrd' _ 8 (by omega) (by omega)).trans m80
  have q8 := (hrd' _ 8 (by omega) (by omega)).trans m8
  have q16 := (hrd' _ 8 (by omega) (by omega)).trans m16
  have q24 := (hrd' _ 8 (by omega) (by omega)).trans m24
  have qra := (hrd' _ 8 (by omega) (by omega)).trans mra
  have qbp := (hrd' _ 8 (by omega) (by omega)).trans mbp
  have hsp2 : s'.regs 4 = s.regs 4 - 256#64 := by
    rw [e4, hsp]; apply BitVec.eq_of_toNat_eq
    have e8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8]; omega
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF.accessible]
  have hsacc8 : s'.mem.accessible ((s.regs 4).toNat - 256) 344 true = true := by
    rw [hacc2, hJ.F.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  obtain ⟨Lk, bk, hka⟩ := kaOf hJ hpx hpy h40 hyx hF hreg hsp' h14 hq' hrg qra qbp q168 q144 q120 q112 q72s q170
    q64 q72 q80 q8 q16 q24
  obtain ⟨-, -, -, -, -, ⟨⟨-, -, hxl12, -⟩, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hJ.pre
  janus64_run [q72, q16, hsp2, BitVec.msb_eq_decide] until [0x5f0b05]
  refine hK Lk bk _ (hka _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals try janus64_simp
  all_goals first
    | exact qfs.trans hfs
    | exact qdf.trans (hdf.trans hdf0.symm)
    | exact (e15.trans hx15).trans hx150.symm
    | exact e5.trans h5
    | exact e14.trans h14
    | fail "SHOW"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `karatsuba` call** (`40 ≤ n < m`, `stk ≠ nil`) from the join `0x5f09d5` to `KA` at `0x5f0b05` -/
theorem karLt (impl : List Amd64.Segment) (R : RtInv) (n0 : Nat)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hih : ∀ a, IH impl R H n0 (.kar, a))
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (h40 : 40 ≤ yl.toNat) (hyx : yl.toNat < xl.toNat)
    (hμ : 8 * yl.toNat + 2 < n0) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (Lk : List (Nat × Nat)) (bk : Nat) (S' : State),
      KA R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem Lk bk S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
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
  refine karLt2 impl R n0 hJ hih hpx hpy hnx hny h40 hyx hμ hx150 hdf0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [win]; janus_frame) ?qreg ?qret ?qy0 ?qy1 ?qy2 ?qra ?qbp ?q112 ?q120 ?q144 ?q168 ?q170 ?q72s
    ?q64 ?q72 ?q80 ?q8 ?q16 ?q24 hK
  case qreg => janus64_simp <;> exact hreg
  case qra => janus64_simp <;> exact mra
  case qbp => janus64_simp <;> exact mbp
  case q112 => janus64_simp <;> exact m112
  case q144 => janus64_simp <;> exact m144
  case q168 => janus64_simp <;> exact m168
  case q64 => janus64_simp <;> exact m64
  case q72 => janus64_simp <;> exact m72
  case q80 => janus64_simp <;> exact m80
  case q8 => janus64_simp <;> exact m8
  case q16 => janus64_simp <;> exact m16
  case q24 => janus64_simp <;> exact m24
  all_goals try janus64_simp
  all_goals first
    | exact h14
    | exact hfs
    | exact (hx15.trans hx150)
    | exact r7
    | exact r6
    | exact r9
    | omega
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
