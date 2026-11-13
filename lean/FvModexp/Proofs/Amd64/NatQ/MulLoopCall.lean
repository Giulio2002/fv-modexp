import FvModexp.Proofs.Amd64.NatQ.MulLoopLM
import FvModexp.Proofs.Common.DivmcBits

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopCall.lean — TIGHT COSTS] `nat.mul` (amd64), chunk loop: the chunk product `t = t.mul(stk, x[i:i+cc], y)` (natmul.go:57)

`LB.localP`: `LB.local` with the return-address slot `RSP - 264` of the call. `mulCallL`: a call of `nat.mul`
through the SCC induction hypothesis of member `.mul` (entry `0x5f0840`, return `0x5f0de5`). `lcall2`: at the entry
(arguments loaded, `μ_chunk`), the call, the return and `lm_of` ⟹ `LM`. `lcall`: the head `0x5f0d39` (`i < m`) →
the call (both cases of `cc = min(n, m - i)`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep
  inv_frame_win)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

set_option maxRecDepth 20000 in
/-- `LB.local` including the return-address slot of a call at `RSP - 264` -/
theorem LB.localP (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    (hF0 : MemFrame Mi Mi' [((s.regs 4).toNat - 264, (s.regs 4).toNat - 232), ((s.regs 4).toNat - 160,
      (s.regs 4).toNat - 144), ((s.regs 4).toNat - 136, (s.regs 4).toNat - 112), ((s.regs 4).toNat - 80,
      (s.regs 4).toNat - 72)]) (hreg : Mi'.regions = Mi.regions) :
    LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi' := by
  have hW0 : 4608 ≤ W ∧ W ≤ (s.regs 4).toNat := ⟨h.lay.1, h.lay.2.1⟩
  have hF : MemFrame Mi Mi' (win s W 88) := hF0.mono fun a n ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hrd : ∀ x m, (s.regs 4).toNat - 232 ≤ x → (x + m ≤ (s.regs 4).toNat - 160 ∨ (s.regs 4).toNat - 144 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 112 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 80 ∨ (s.regs 4).toNat - 72 ≤ x) → Mi'.readLE x m = Mi.readLE x m :=
    fun x m h0 h1 h2 h3 => hF0.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hko := h.lwsOut
  have hLs := h.wsep
  have hst : Outside st 24 (win s W 88) := by
    have := hko _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [win, outside_cons, outside_nil, and_true]; simp only at this; omega
  have eW : stW Mi' st = stW Mi st := hF.readLE _ _ (hst.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen Mi' st = stLen Mi st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap Mi' st = stCap Mi st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  refine
    { core := h.core, h40 := h.h40, hlt := h.hlt, ext := h.ext, bud := by rw [stkR_congr eC]; exact h.bud,
      spk := h.spk, inv := inv_frame_win hF hout (by omega) (by decide) h.inv, reg := hreg.trans h.reg,
      fr := h.fr.trans hF fun x m ho => ⟨ho, by simp only [outside_append] at ho; exact ho.1.2⟩,
      lf := LiveFrame.trans h.lf ⟨fun x m hin _ => hF.readLE x m (outside_of_liveSep hin hLs)⟩
        fun _ _ h => h,
      sok := stkOK_frame h.sok hF hst, slen := by rw [eL]; exact h.slen,
      sarr := by rw [eW, eC]; exact h.sarr, smem := h.smem.congr eW eC fun _ h => h,
      ra := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.ra,
      bp := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.bp,
      b56 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.b56,
      b57 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.b57,
      c58 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.c58,
      n70 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.n70,
      p90 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.p90,
      sb8 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.sb8,
      dfn := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dfn,
      dst := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dst,
      dln := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dln,
      dpt := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dpt,
      x140 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.x140,
      x148 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.x148,
      x150 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.x150,
      y108 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.y108,
      y110 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.y110,
      y118 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.y118 }

end

set_option maxRecDepth 20000 in
/-- a call of `nat.mul` through the induction hypothesis at its entry `0x5f0840` returning to `0x5f0de5` -/
theorem mulCallL {impl : List Amd64.Segment} {R : RtInv} {n : Nat} (hih : ∀ a, IH impl R H n (.mul, a)) (a : Args)
    {S : State} {ret : W64} {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 0x5f0840) (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f0de5)
    (h0 : S.regs 0 = a.a0) (h3 : S.regs 3 = a.a1) (h1 : S.regs 1 = a.a2) (h7 : S.regs 7 = a.a3) (h6 : S.regs 6 = a.a4)
    (h8 : S.regs 8 = a.a5) (h9 : S.regs 9 = a.a6)
    (m8 : S.mem.readLE ((S.regs 4).toNat + 8) 8 = a.a7.toNat) (m16 : S.mem.readLE ((S.regs 4).toNat + 16) 8 = a.a8.toNat)
    (m24 : S.mem.readLE ((S.regs 4).toNat + 24) 8 = a.a9.toNat)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hpre : MPre R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat
      a.a8.toNat a.a9.toNat S)
    (hmu : μl a.a5.toNat a.a8.toNat + 3 < n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f0de5 → Kept S s' →
      MPost R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat
        a.a9.toNat S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibMul.program.link impl) ret s' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hS : Summary (LibMul.program.link impl) 0x5f0840 (fun s => preOf R H (.mul, a) s ∧ μ (.mul, a) s < n)
      (postOf R H (.mul, a)) := hih a
  refine ReachesRet.call_regions hS hpc ⟨⟨⟨?_, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, m8, m16, m24⟩, hpre⟩, hmu⟩
    fun s' hr ⟨hk, hq⟩ hrg => K s' ?_ hk hq hrg
  · rw [hrd]; decide
  · rw [hr, retAddrOf, hrd]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the call of the chunk product at `nat.mul`'s entry (`CALL 0x5f0de0` done) and its return -/
theorem lcall2 (impl : List Amd64.Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tc cc : Nat}
    (hμ : μl xl yl + 3 ≤ n0) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp xl yl k) S.mem)
    (ht : TOK R L1 Lk M S.mem st tp tc) (hpx : Apart p (8 * c) xp (8 * xl)) (hpy : Apart p (8 * c) yp (8 * yl))
    (hilt : (k + 1) * yl < xl) (hcc : cc = min yl (xl - (k + 1) * yl))
    (hv : natVal S.mem p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl)
    (m78 : S.mem.readLE ((s.regs 4).toNat - 136) 8 = (k + 1) * yl)
    (m80 : S.mem.readLE ((s.regs 4).toNat - 128) 8 = 8 * ((k + 1) * yl))
    (m88 : S.mem.readLE ((s.regs 4).toNat - 120) 8 = (k + 1) * yl + yl)
    (hpc : S.rip = BitVec.ofNat 64 0x5f0840) (hsp : S.regs 4 = s.regs 4 - 264#64) (h14 : S.regs 14 = s.regs 14)
    (h5 : S.regs 5 = s.regs 4 - 8#64) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = s.xmm 15)
    (mret : S.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0de5)
    (r0 : S.regs 0 = BitVec.ofNat 64 tp) (r1 : S.regs 1 = BitVec.ofNat 64 tc) (r7 : S.regs 7 = BitVec.ofNat 64 st)
    (r6 : S.regs 6 = BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl))) (r8 : S.regs 8 = BitVec.ofNat 64 cc)
    (r9 : S.regs 9 = BitVec.ofNat 64 (xc - (k + 1) * yl))
    (y0 : S.mem.readLE ((s.regs 4).toNat - 256) 8 = yp) (y1 : S.mem.readLE ((s.regs 4).toNat - 248) 8 = yl)
    (y2 : S.mem.readLE ((s.regs 4).toNat - 240) 8 = yc)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' tp' tl' tc' : Nat) (S' : State),
      LM R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' k tp' tl' tc' S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  obtain ⟨hW, hWs, hal, -, -, -, -, hcap, -, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have h40 := h.h40
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 264 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcy : cc ≤ yl := by rw [hcc]; exact Nat.min_le_left _ _
  have hc0 : 0 < cc := by rw [hcc]; omega
  have hcx : (k + 1) * yl + cc ≤ xl := by
    have : cc ≤ xl - (k + 1) * yl := by rw [hcc]; exact Nat.min_le_right _ _
    omega
  have ht0 := ht.1
  have ht40 := ht.2.1
  have hst48 : st < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt S.mem ((s.regs 4).toNat - 72) 8; rw [h.sb8] at this; omega
  have hxp48 : xp + 8 * xc ≤ 2 ^ 48 := (h.core.pre.2.2.2.2.2.1.1.2.2.2.2.1 (by omega)).2
  have hyp48 : yp + 8 * yc ≤ 2 ^ 48 := (h.core.pre.2.2.2.2.2.1.2.1.2.2.2.2.1 (by omega)).2
  have htp48 : tp + 8 * tc ≤ 2 ^ 48 := (ht.2.2.1 ht0).2.2.2
  have e0 : (BitVec.ofNat 64 tp).toNat = tp := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 tc).toNat = tc := by simp only [BitVec.toNat_ofNat]; omega
  have e3 : (BitVec.ofNat 64 st).toNat = st := by simp only [BitVec.toNat_ofNat]; omega
  have e4 : (BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl))).toNat = xp + 8 * ((k + 1) * yl) := by
    simp only [BitVec.toNat_ofNat]; omega
  have e5 : (BitVec.ofNat 64 cc).toNat = cc := by simp only [BitVec.toNat_ofNat]; omega
  have e6 : (BitVec.ofNat 64 (xc - (k + 1) * yl)).toNat = xc - (k + 1) * yl := by simp only [BitVec.toNat_ofNat]; omega
  have e7 : (BitVec.ofNat 64 yp).toNat = yp := by simp only [BitVec.toNat_ofNat]; omega
  have e8 : (BitVec.ofNat 64 yl).toNat = yl := by simp only [BitVec.toNat_ofNat]; omega
  have e9 : (BitVec.ofNat 64 yc).toNat = yc := by simp only [BitVec.toNat_ofNat]; omega
  have hbk := h.bud
  have hb1 := h.core.bud
  have hc0' := h.core.pre.2.2.2.2.2.2.2.1.2
  have hlsp := lsp_call h40 hilt
  have hmc : mulCQ cc yl = MCQ yl (min yl (xl - (k + 1) * yl)) := by
    rw [mulCQ_chunk hcy, hcc, Nat.min_eq_right (Nat.min_le_left _ _)]
  have hcost : mulCQ cc yl + stkR H S.mem st ≤ bk := by rw [hmc]; omega
  have hyx : yl < xl := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left yl (by omega)) hilt
  have hμc : μl cc yl + 3 < n0 := Nat.lt_of_lt_of_le (μ_chunk hcy hyx) hμ
  have hpre : MPre R bk H Lk (W - 264) tp tc st (xp + 8 * ((k + 1) * yl)) cc (xc - (k + 1) * yl) yp yl yc S :=
    h.mpreT ht hsp' h14 rfl hfs (i := (k + 1) * yl) (cc := cc) (Nat.le_mul_of_pos_left yl (by omega)) hc0 hcy hcx hcost
  refine mulCallL ih ⟨bk, Lk, W - 264, BitVec.ofNat 64 tp, S.regs 3, BitVec.ofNat 64 tc, BitVec.ofNat 64 st,
    BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl)), BitVec.ofNat 64 cc, BitVec.ofNat 64 (xc - (k + 1) * yl),
    BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc⟩ hpc (by rw [hsp']; exact mret) r0 rfl r1 r7 r6 r8 r9
    (by rw [hsp', show (s.regs 4).toNat - 264 + 8 = (s.regs 4).toNat - 256 by omega, e7]; exact y0)
    (by rw [hsp', show (s.regs 4).toNat - 264 + 16 = (s.regs 4).toNat - 248 by omega, e8]; exact y1)
    (by rw [hsp', show (s.regs 4).toNat - 264 + 24 = (s.regs 4).toNat - 240 by omega, e9]; exact y2)
    (hx15.trans hx150) (hdf.trans hdf0) (by simp only; rw [e0, e2, e3, e4, e5, e6, e7, e8, e9]; exact hpre)
    (by simp only; rw [e5, e8]; exact hμc) (fun s' hr ⟨e4', e5', e14', e15'⟩ hq hrg => ?_)
  simp only [e0, e2, e3, e4, e5, e6, e7, e8, e9] at hq
  have q2 : s'.regs 4 = s.regs 4 - 256#64 := by
    rw [e4', hsp]; apply BitVec.eq_of_toNat_eq
    have e8' : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8']; omega
  obtain ⟨Lk', bk', tp', tl', tc', hlm⟩ := lm_of h ht hpx hpy hilt hv m78 m80 m88 hcc hsp' h14 rfl hfs hdf hq hrg
    hr q2 (e14'.trans h14) (e5'.trans h5) (e15'.trans hx15)
  exact hK _ _ _ _ _ _ hlm

theorem toIntN {a : Nat} (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **one chunk product**: the head (`i < m`) → the call → `LM` -/
theorem lcall (impl : List Amd64.Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tl tc : Nat}
    (hμ : μl xl yl + 3 ≤ n0) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hH : LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S) (hilt : (k + 1) * yl < xl)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' tp' tl' tc' : Nat) (S' : State),
      LM R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' k tp' tl' tc' S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have h := hH.lb
  obtain ⟨hW, hWs, hal, ha48, -, -, -, hcap, -, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have h40 := h.h40
  have hpc := hH.pc; have hsp := hH.sp; have h14 := hH.g; have h5 := hH.bp
  have r0 := hH.r0; have r1 := hH.r1; have r2 := hH.r2; have r3 := hH.r3
  have x140 := h.x140; have x148 := h.x148; have x150 := h.x150; have y108 := h.y108; have y110 := h.y110
  have y118 := h.y118; have sb8 := h.sb8
  have hyx : yl < xl := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left yl (by omega)) hilt
  have hyp48 : yp + 8 * yc ≤ 2 ^ 48 := (h.core.pre.2.2.2.2.2.1.2.1.2.2.2.2.1 (by omega)).2
  obtain ⟨⟨-, ⟨-, -, hw0⟩, -⟩, -⟩ := h.core.pre
  simp only [regSP] at hw0
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 264) 352 true = true := by
    rw [h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 256 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have i1 := toIntN (a := (k + 1) * yl) (by omega)
  have i2 := toIntN (a := xl) (by omega)
  have i3 := toIntN (a := (k + 1) * yl + yl) (by omega)
  have hadd : BitVec.ofNat 64 yl + BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 ((k + 1) * yl + yl) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd1 : BitVec.ofNat 64 yl + BitVec.ofNat 64 ((k + 1) * yl) * 1#64 = BitVec.ofNat 64 ((k + 1) * yl + yl) := by
    rw [BitVec.mul_one]; exact hadd
  have hsx : BitVec.ofNat 64 xc - BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 (xc - (k + 1) * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs1 : BitVec.ofNat 64 xl - BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 (xl - (k + 1) * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs2 : BitVec.ofNat 64 ((k + 1) * yl + yl) - BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 yl := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsl : BitVec.ofNat 64 ((k + 1) * yl) <<< 3 = BitVec.ofNat 64 (8 * ((k + 1) * yl)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hm : ((0#64 - BitVec.ofNat 64 (xc - (k + 1) * yl)).sshiftRight 63 &&& BitVec.ofNat 64 (8 * ((k + 1) * yl))) =
      BitVec.ofNat 64 (8 * ((k + 1) * yl)) :=
    neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hm' : (BitVec.ofNat 64 (8 * ((k + 1) * yl)) &&& (0#64 - BitVec.ofNat 64 (xc - (k + 1) * yl)).sshiftRight 63) =
      BitVec.ofNat 64 (8 * ((k + 1) * yl)) := by rw [BitVec.and_comm]; exact hm
  have hxa : BitVec.ofNat 64 xp + BitVec.ofNat 64 (8 * ((k + 1) * yl)) = BitVec.ofNat 64 (xp + 8 * ((k + 1) * yl)) := by
    rw [← BitVec.ofNat_add]
  by_cases hlast : xl < (k + 1) * yl + yl
  · have hI : ((xl : Nat) : Int) < (((k + 1) * yl + yl : Nat) : Int) := by omega
    janus64_run [x140, x148, x150, y108, y110, y118, sb8, i1, i2, i3, hadd, hadd1, hsx, hs1, hs2, hsl, hm, hm', hxa,
      hI, hsp', BitVec.msb_eq_decide] until [0x5f0840]
    refine lcall2 impl R n0 ih hμ hx150 hdf0 _ (h.localP ?fr0 ?reg) (hH.tok.winKeep h ?frW) hH.px hH.py hilt
      (cc := xl - (k + 1) * yl) ?hcc ?hv ?m78 ?m80 ?m88 ?pc ?sp ?g ?bp ?fs ?df ?x15 ?mret ?r0 ?r1 ?r7 ?r6 ?r8 ?r9
      ?y0 ?y1 ?y2 hK
    case fr0 => janus_frame
    case frW => simp only [win]; janus_frame
    case hcc => omega
    case hv =>
      rw [(h.winVal hH.tok (tl := 0) (Nat.zero_le _) (by simp only [win]; janus_frame)).1, hH.val,
        Nat.min_eq_left (by omega)]
    all_goals try janus64_simp
    all_goals first
      | exact hH.fs
      | exact hH.df
      | exact hH.x15
      | exact hH.df.trans hdf0
      | exact hH.x15.trans hx150
      | exact Nat.mod_eq_of_lt (by omega)
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
      | fail "SHOW"
  · have hI : ¬ (((xl : Nat) : Int) < (((k + 1) * yl + yl : Nat) : Int)) := by omega
    janus64_run [x140, x148, x150, y108, y110, y118, sb8, i1, i2, i3, hadd, hadd1, hsx, hs1, hs2, hsl, hm, hm', hxa,
      hI, hsp', BitVec.msb_eq_decide] until [0x5f0840]
    refine lcall2 impl R n0 ih hμ hx150 hdf0 _ (h.localP ?fr0B ?regB) (hH.tok.winKeep h ?frWB) hH.px hH.py hilt
      (cc := yl) ?hccB ?hvB ?m78B ?m80B ?m88B ?pcB ?spB ?gB ?bpB ?fsB ?dfB ?x15B ?mretB ?r0B ?r1B ?r7B ?r6B ?r8B ?r9B
      ?y0B ?y1B ?y2B hK
    case fr0B => janus_frame
    case frWB => simp only [win]; janus_frame
    case hccB => omega
    case hvB =>
      rw [(h.winVal hH.tok (tl := 0) (Nat.zero_le _) (by simp only [win]; janus_frame)).1, hH.val,
        Nat.min_eq_left (by omega)]
    all_goals try janus64_simp
    all_goals first
      | exact hH.fs
      | exact hH.df
      | exact hH.x15
      | exact hH.df.trans hdf0
      | exact hH.x15.trans hx150
      | exact Nat.mod_eq_of_lt (by omega)
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
      | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
