import FvModexp.Proofs.Amd64.Exp.P2DWinR
import FvModexp.Proofs.Amd64.Exp.P2DWS
import FvModexp.Proofs.Amd64.Exp.P2DOne

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): odd `x`, `logM ≥ 2` — the window call (agent asm s68; amd64 twin of infra's arm64
`P2DWin`)

`winCall`: from a window entry (`RSP_S = RSP - 0x78`, memory `Mw (W0 …)`) with a window summary `hW : WSum …`
(applied at `stk - 0x78`), back at the return site (`w2R` / `w4R`), through the epilogue (`epiW`) to the return;
post `PostD` (transport: `cpre_sub` / `in_sub` / `natOne_sub` / `cpost_pre`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

theorem mw_frame (M : Memory) {sp : Nat} (yp yl r : Nat) (h : 8 ≤ sp) :
    MemFrame M (Mw M sp yp yl r) [(sp - 8, sp + 0x18)] := by
  simp only [Mw]
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega)
  exact MemFrame.refl _ _

theorem mw_rd {M : Memory} {sp yp yl r a k : Nat} (h8 : 8 ≤ sp) (h : a + k ≤ sp - 8 ∨ sp + 0x18 ≤ a) :
    (Mw M sp yp yl r).readLE a k = M.readLE a k := by
  simp (disch := omega) only [Mw, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]

theorem mw_ra {M : Memory} {sp yp yl r : Nat} (h : r < 2 ^ 64) : (Mw M sp yp yl r).readLE (sp - 8) 8 = r := by
  simp only [Mw, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt h

theorem mw_y0 {M : Memory} {sp yp yl r : Nat} (h8 : 8 ≤ sp) (h : yp < 2 ^ 64) : (Mw M sp yp yl r).readLE sp 8 = yp := by
  simp (disch := omega) only [Mw, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h

theorem mw_y1 {M : Memory} {sp yp yl r : Nat} (h8 : 8 ≤ sp) (h : yl < 2 ^ 64) :
    (Mw M sp yp yl r).readLE (sp + 8) 8 = yl := by
  simp (disch := omega) only [Mw, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h

theorem mw_y2 {M : Memory} {sp yp yl r : Nat} (h8 : 8 ≤ sp) :
    (Mw M sp yp yl r).readLE (sp + 16) 8 = M.readLE (sp + 0x88) 8 := by
  simp (disch := omega) only [Mw, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)

theorem w0_88 {M : Memory} {sp bp zp xp : Nat} : (W0 M sp bp zp xp).readLE (sp + 0x88) 8 = M.readLE (sp + 0x88) 8 := by
  simp (disch := omega) only [W0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]

theorem nW {SP : Nat} (h : 4320 ≤ SP) : SP - 8 ≤ SP - 0x70 + 0x68 ∧ SP - 0x70 + 0x68 + 8 ≤ SP + 8 ∧
    SP - 8 ≤ SP - 0x70 + 0x70 ∧ SP - 0x70 + 0x70 + 8 ≤ SP + 8 ∧ SP - 0x70 + 0x18 ≤ SP - 0x70 + 0x68 ∧
    SP - 0x70 + 0x18 ≤ SP - 0x70 + 0x70 ∧ SP - 0x70 + 0x70 = SP := by omega

theorem nK {stk : Nat} (h : 0x78 ≤ stk) : stk - 0x78 + 0x78 ≤ stk := by omega

theorem nB {b cst c : Nat} (h : c ≤ cst) : b - cst ≤ b - c := by omega

theorem nS {SP : Nat} (h1 : 0x78 ≤ SP) (h2 : SP < 2 ^ 64) :
    BitVec.ofNat 64 (SP - 0x78) + 8#64 = BitVec.ofNat 64 (SP - 0x70) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {sp bp : Nat} {S : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the epilogue after a window call (`ADDQ $0x68, SP; POPQ BP; RET`) -/
theorem epiW {r : Nat} (hr : r = w2R ∨ r = w4R) (hpc : S.rip = BitVec.ofNat 64 r)
    (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hsp : sp + 0x78 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hra : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 0 → s'.regs 3 = S.regs 3 → s'.regs 1 = S.regs 1 →
      s'.mem = S.mem → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e := sp78 hsp
  rcases hr with rfl | rfl
  · janus64_run [hbp, hra]
    exact K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
      (by janus64_simp) rfl
  · janus64_run [hbp, hra]
    exact K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
      (by janus64_simp) rfl

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the window call** (see the module doc) -/
theorem winCall {impl : List Amd64.Segment} {e kW r : Nat} {cW : Nat → Nat → Nat → Nat}
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hXo : natVal s.mem xp xl % 2 = 1) (hlm2 : 2 ≤ lm) (hcW : cW (stLen s.mem st) yl lm ≤ cst)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hxl : xl ≤ xc) (hxc : xc < 2 ^ 40)
    (hEX : (0 < xl → Apart xp (8 * xl) RunIface.gA 32) ∧ Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32 ∧
      s.mem.accessible Callees.adxAddr 1 false = true)
    (hzp : zp < 2 ^ 64) (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hy : NHyp.StkArg s 0 yp yl yc)
    (hW : WSum impl R e kW cW) (hkW : kW + 0x78 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x78)
    (hr : r ∈ [w2R, w4R])
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 e) (esp : S1.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x78))
    (e0 : S1.regs 0 = BitVec.ofNat 64 zp) (e3 : S1.regs 3 = BitVec.ofNat 64 zl) (e1 : S1.regs 1 = BitVec.ofNat 64 zc)
    (e7 : S1.regs 7 = BitVec.ofNat 64 st) (e6 : S1.regs 6 = BitVec.ofNat 64 xp) (e8 : S1.regs 8 = BitVec.ofNat 64 xl)
    (e9 : S1.regs 9 = BitVec.ofNat 64 xc) (e10 : S1.regs 10 = BitVec.ofNat 64 lm)
    (e14 : S1.regs 14 = s.regs 14) (efs : S1.fsBase = s.fsBase) (ex : S1.xmm 15 = s.xmm 15) (edf : S1.df = s.df)
    (hm : S1.mem = Mw (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) ((s.regs 4).toNat - 0x70) yp yl r) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S1
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  have hP0 := hP
  obtain ⟨q1, q2, q3, q4, q5⟩ := epi_of hP hk hA hra
  obtain ⟨hC, hX, hY, -, hlm, hst0, op, hone, hsa⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hle, h48, hacc⟩, -, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, ⟨-, -, hzW⟩, hins, hsok, hstw, -, harr,
    hcap0, hneed, -, -, -, -, -, -, -, hcst, -, -, hinv⟩ := hC'
  simp only [regSP] at hle h48 hacc
  have hrv : r < 2 ^ 47 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  have hsp0 : 0x70 ≤ (s.regs 4).toNat := by omega
  have hFW := w0_own (zp := zp) (xp := xp) (by omega : 8 ≤ stk) hA hsp0
  have hSsp : (S1.regs 4).toNat + 0x78 = (s.regs 4).toNat := by rw [esp, BitVec.toNat_ofNat]; omega
  obtain ⟨hy1, hy2, hy3⟩ := hy
  obtain ⟨hEX1, hEX2, hEX3⟩ := hEX
  generalize hSP : (s.regs 4).toNat = SP at *
  have hsp1 : 8 ≤ SP - 0x70 := by omega
  have h120 : 4320 ≤ SP := by omega
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hF0 : MemFrame s.mem S1.mem (ownW s stk A) := by
    rw [hm]
    exact hFW.trans (mw_frame _ yp yl r hsp1) fun a k ho => ⟨ho, by
      simp only [ownW, hSP, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
  have hF0' : MemFrame s.mem S1.mem (R.rt ++ ownW s stk A) := hF0.mono fun a k ho => by
    rw [outside_append] at ho; exact ho.2
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF0 : LiveFrame s.mem S1.mem L [] := LiveFrame.of_win hF0 hLs'
  have hrg : S1.mem.regions = s.mem.regions := by
    rw [hm]; simp only [Mw, W0, Janus.Arm64.Memory.regions_writeLE]
  have hinv1 : R.inv b L (s.regs 14).toNat (view R.rt L S1.mem) := by
    refine Expmc.inv_frame hF0 (fun r hr => Or.inr ?_) hinv
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact hwin.of_sub (by omega) (by omega)
  have hstO : Outside st 24 (ownW s stk A) := by
    simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF0' hLF0 hstO
  have hval : ∀ {p n : Nat}, (p, n) ∈ [(xp, xl), (yp, yl)] → natVal S1.mem p n = natVal s.mem p n := by
    intro p n hpn
    obtain ⟨⟨-, -, -, -, hw⟩, -⟩ := hins p n hpn
    exact hF0.readLE _ _ (by simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hw ⊢; omega)
  have hvx := hval (p := xp) (n := xl) (by simp)
  have hvy := hval (p := yp) (n := yl) (by simp)
  obtain ⟨⟨-, -, hyp48, -, -⟩, hyl9, -⟩ := hins yp yl (by simp)
  have hnone := natOne_sub hone hsa hF0 (LiveExt.refl R L) (by rw [hSP]; exact hSsp) (stk' := stk - 0x78)
    (A' := 0x60) (by omega) (by omega) ew el ec
  have hS1 : (S1.regs 4).toNat = SP - 0x78 := by omega
  have hone1 : S1.mem.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 := by
    rw [hnone.1.1, hone.1]
  have hpre : WPre R b L (stk - 0x78) 0x60 (cW (stLen S1.mem st) yl lm) zp zl zc st xp xl xc yp yl yc lm S1 := by
    refine ⟨⟨e0, e3, e1, e7, e6, e8, e9, e10, ?_, ?_, ?_⟩, ⟨ex.trans hx15, edf.trans hdf, hzp⟩,
      cpre_sub hC hF0' hLF0 hrg (LiveExt.refl R L) hinv1 (by rw [hSP]; exact hSsp) e14 efs (by omega) (by omega)
        (fun p n hpn => in_sub hC hpn hF0' hLF0 (LiveExt.refl R L) (by rw [hSP]; exact hSsp) (by omega) (by omega))
        (by omega) (by rw [el]; omega),
      by rw [hvx]; exact hX, by rw [hvx]; exact hXo, by rw [hvy]; exact hY, hlm2, hlm, hst0, ⟨op, hnone⟩, hxl, hxc,
      ⟨hEX1, by rw [hone1]; exact hEX2, by rw [hF0.accessible]; exact hEX3⟩, ?_⟩
    · rw [hS1, show SP - 0x78 + 0 + 8 = SP - 0x70 by omega, hm]; exact mw_y0 hsp1 (by omega)
    · rw [hS1, show SP - 0x78 + 0 + 16 = SP - 0x70 + 8 by omega, hm]; exact mw_y1 hsp1 (by omega)
    · rw [hS1, show SP - 0x78 + 0 + 24 = SP - 0x70 + 16 by omega, hm, mw_y2 hsp1,
        w0_88, show SP - 0x70 + 0x88 = SP + 0 + 24 by omega]; exact hy3
    · rw [hS1, show SP - 0x78 = SP - 0x70 - 8 by omega, hm, mw_ra (by omega)]; exact hrv
  have hraS : S1.mem.readLE (S1.regs 4).toNat 8 = r := by
    rw [hS1, show SP - 0x78 = SP - 0x70 - 8 by omega, hm, mw_ra (by omega)]
  refine ReachesRet.call_regions (hW b L (stk - 0x78) zp zl zc st xp xl xc yp yl yc lm (by omega) (by omega)) hpc hpre
    fun T hT hq hrg' => ?_
  obtain ⟨⟨q4', q5', q14, qx⟩, hcp⟩ := hq
  rw [hvx, hvy, el] at hcp
  have hcp' := hcp
  obtain ⟨qfs, qdf, -, -, -, -, -, -, -, -, -, -, -, hFc, -⟩ := hcp'
  simp only [win, hS1, stWs, stkWs, ew, el, ec] at hFc
  have hkeep : ∀ {a : Nat}, SP - 8 ≤ a → a + 8 ≤ SP + 8 → T.mem.readLE a 8 = S1.mem.readLE a 8 := by
    intro a h1 h2
    refine rd_frame hFc fun q hq => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with ((hq | rfl) | rfl) | (rfl | rfl)
    · have ho : Outside a 8 R.rt := hwin.of_sub (by omega) (by omega)
      have := MemFrame.outside_mem ho hq; omega
    · simp only; omega
    · simp only; rcases Nat.eq_zero_or_pos zc with h0 | h0
      · left; omega
      · have := (hzW h0).1; simp only [win, hSP, outside_cons, outside_nil, and_true] at this; right; omega
    · simp only [win, hSP, outside_cons, outside_nil, and_true] at hstw; simp only; omega
    · simp only
      rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
      · have := hcap0 h0; left; rw [this, h0]; have := hsok.2.2.2.2.2.1; omega
      · have := (harr h0).1
        simp only [win, hSP, outside_cons, outside_nil, and_true] at this
        right; omega
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := nW h120
  have hk78 := nK (Nat.le_trans (by decide) hk)
  have hbb := nB (b := b) hcW
  have hS64 : SP < 2 ^ 64 := hSP ▸ (s.regs 4).isLt
  have hS78 : 0x78 ≤ SP := Nat.le_trans (by decide) h120
  have rbp : T.mem.readLE (SP - 0x70 + 0x68) 8 = (s.regs 5).toNat := by
    rw [hkeep w1 w2, hm, mw_rd (M := W0 s.mem (SP - 0x70) (s.regs 5).toNat zp xp) (yp := yp) (yl := yl) (r := r)
      (a := SP - 0x70 + 0x68) (k := 8) hsp1 (Or.inr w5)]
    exact q3
  have rra : T.mem.readLE (SP - 0x70 + 0x70) 8 = (retAddrOf s).toNat := by
    rw [hkeep w3 w4, hm, mw_rd (M := W0 s.mem (SP - 0x70) (s.regs 5).toNat zp xp) (yp := yp) (yl := yl) (r := r)
      (a := SP - 0x70 + 0x70) (k := 8) hsp1 (Or.inr w6)]
    exact q4
  have hacc' : T.mem.accessible (SP - 0x70 + 0x68) 16 false = true := by
    rw [hFc.accessible, hm]; simp only [Mw, Janus.Arm64.Memory.accessible_writeLE]; exact q2
  have hT' : T.rip = BitVec.ofNat 64 r := by rw [hT]; simp only [retAddrOf, hraS]
  have hT4 : T.regs 4 = BitVec.ofNat 64 (SP - 0x70) := by rw [q4', esp]; exact nS hS78 hS64
  refine epiW (by simpa using hr) hT' hT4 q1 hacc' rbp rra q5 fun s' hE a0 a3 a1 am => ?_
  refine postD_of hP0 (by rw [hSP]; exact w7) hE (q14.trans e14) (qfs.trans efs) (qx.trans ex) (qdf.trans edf)
    fun hfs' hdf' => ?_
  exact cpost_pre hC hF0' hLF0 (LiveExt.refl R L) (by rw [hSP]; exact hSsp) e14 efs edf (stk' := stk - 0x78)
    (A' := 0x60) hk78 (by decide) hbb hcp am a0 a3 a1 (hE.2.2.2.1) (hE.2.2.2.2.2)

end

end FvModexp.Amd64.P2D
