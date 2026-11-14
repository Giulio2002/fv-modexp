import FvModexp.Proofs.Amd64.Exp.P2DRecH
import FvModexp.Proofs.Amd64.Exp.P2DRecR
import FvModexp.Proofs.Amd64.Exp.P2DSumO

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): the recursive call `z.expNNPowerOfTwo(xOdd, y, logM - lo)` (nat.go:953; agent asm
s70; twin of infra's arm64 `P2DRec.recCall`)

From `rsh`'s return (`rshR`, its `RshPost`, `z = nil` so `xOdd` is FRESH) through `runRec` and the callee summary
`hO` (the odd-base `sumO`, instantiated by the caller at `stk - 0x78`, window top `72`) to `recR`, handing the
continuation the callee's `CPostR` lifted to our frame (`cpost_pre`) and our slots `lo` / saved BP / return address.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the recursive call** (see the module doc) -/
theorem recCall {impl : List Amd64.Segment} {cf : Nat → Nat → Nat} {lm' : Nat}
    (hO : ∀ (b1 : Nat) (L1 : List (Nat × Nat)) (p1 l1 c1 : Nat),
      Summary (LibW.program.link impl) fnE
        (fun s1 => Regs s1 zp zl zc st p1 l1 c1 yp yl yc lm' ∧
          PreD R b1 L1 (stk - 0x78) 72 (cf (stLen s1.mem st) lm') zp zl zc st p1 l1 yp yl lm' s1 ∧ OX s1 zp p1 l1 c1)
        (fun s1 s' => PostD R b1 L1 (stk - 0x78) 72 (cf (stLen s1.mem st) lm') zp zc st
          (natVal s1.mem p1 l1 ^ natVal s1.mem yp yl % 2 ^ lm') s1 s'))
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    (hy : NHyp.StkArg s 0 yp yl yc) (hzp : zp < 2 ^ 64) (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (hone2A : Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32)
    {tz lo : Nat} (hlo : lo < lm) (hlm' : lm' = lm - lo) (htz : tz = Exp.tz (natVal s.mem xp xl))
    (hbud : makeCost (Rsh.need xl tz) + cf (stLen s.mem st) lm' ≤ cst)
    {stkR aboveR : Nat} (hkR : stkR + 0x78 ≤ stk) (haR : aboveR ≤ 0x60) {Q : State → Prop}
    (S : State) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x78)) (r14 : S.regs 14 = s.regs 14)
    (rfs : S.fsBase = s.fsBase) (rx : S.xmm 15 = s.xmm 15) (rdf : S.df = s.df)
    (hm : S.mem = M1 s zp zl zc st lm xp lo)
    (S1 : State) (h1pc : S1.rip = BitVec.ofNat 64 rshR) (h1sp : S1.regs 4 = S.regs 4 + 8)
    (h114 : S1.regs 14 = S.regs 14) (h1x : S1.xmm 15 = S.xmm 15) (h1rg : S1.mem.regions = S.mem.regions)
    (hq : Rsh.RshPost R b L stkR aboveR 0 0 xp xl tz S S1)
    (K : ∀ S3 : State, S3.rip = BitVec.ofNat 64 recR → S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x70) →
      S3.regs 14 = s.regs 14 → S3.xmm 15 = s.xmm 15 → S3.mem.regions = s.mem.regions →
      S3.mem.readLE ((s.regs 4).toNat - 0x70 + 0x58) 8 = lo →
      S3.mem.readLE ((s.regs 4).toNat - 0x70 + 0x68) 8 = (s.regs 5).toNat →
      S3.mem.readLE ((s.regs 4).toNat - 0x70 + 0x70) 8 = (retAddrOf s).toNat →
      NHyp.CPostR R b L stk A zp zc st ((natVal s.mem xp xl / 2 ^ tz) ^ natVal s.mem yp yl % 2 ^ lm')
        (makeCost (Rsh.need xl tz) + cf (stLen s.mem st) lm') s S3 →
      ReachesRet (LibW.program.link impl) (retAddrOf s) S3 Q) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S1 Q := by
  have hrt : (retAddrOf s).toNat = s.mem.readLE (s.regs 4).toNat 8 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 4).toNat 8
    simp only [retAddrOf, BitVec.toNat_ofNat]; omega
  obtain ⟨hC, hX, hY, -, hlm, hst0, op, hone, hsa⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hle, h48, hacc⟩, -, -, hwrt, -, -, hLs, -⟩, -, hgl, -, -, hzlc, ⟨hzc40, hzL, hzW⟩, hins, hsok, hstw,
    -, harr, hcap0, hneed, -, -, -, -, -, -, -, hcb, hadx, -, hinv⟩ := hC'
  simp only [regSP] at hle h48 hacc
  have hgrt : Outside RunIface.gA 32 R.rt := hgl.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨-, hxa, hx48, hxH, hxw⟩, hxl9, -⟩ := hins xp xl (by simp)
  obtain ⟨⟨-, hya, hy48, hyH, hyw⟩, hyl9, -⟩ := hins yp yl (by simp)
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have h5 := BitVec.isLt (s.regs 5)
  have hst64 : st < 2 ^ 64 := by have := hsok.2.2.2.1; omega
  have hm' : S.mem = W1 (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) ((s.regs 4).toNat - 0x70)
      st lm zc zl zp lo := hm
  generalize hSP : (s.regs 4).toNat = SP at *
  have hSs : (S.regs 4).toNat = SP - 0x78 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hsp1 : 8 ≤ SP - 0x70 := by omega
  -- frames from the entry
  have hF0 : MemFrame s.mem S.mem (ownW s stk A) := by
    rw [hm]; exact m1_frame s (stk := stk) (A := A) (by omega) (by omega) hA
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF0 : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hF0 hLs'
  obtain ⟨efs1, edf1, p1, l1, c1, q0, q1, q2, L1, b1, hres, hcap, ⟨hx, hb1, hinv1⟩, hF, hLF⟩ := hq
  simp only [win, hSs] at hF
  have hFs : MemFrame s.mem S1.mem (R.rt ++ ownW s stk A) := hF0.trans hF fun a k ho => by
    simp only [ownW, hSP, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1, h2⟩ := ho
    exact ⟨⟨h1, h2⟩, ⟨hrt, by omega⟩, by omega⟩
  have hLFs : LiveFrame s.mem S1.mem L [] :=
    hLF0.trans ⟨fun a n hin _ => hLF.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
      fun _ _ h => h
  have hrgS : S.mem.regions = s.mem.regions := by rw [hm]; exact m1_regions s _ _ _ _ _ _ _
  -- the slots after `rsh`
  have slot : ∀ a, SP - 0x18 ≤ a → a + 8 ≤ SP + A → S1.mem.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 =>
    rshSlot hF hwin hkR haR hle h1 h2
  have hlo64 : lo < 2 ^ 64 := by omega
  have hM1 := m1_rd (M := s.mem) (sp := SP - 0x70) (bp := (s.regs 5).toNat) (zp := zp) (zl := zl) (zc := zc)
    (st := st) (lm := lm) (xp := xp) (lo := lo) hsp1
    ⟨h5, hzp, by omega, by omega, hst64, by omega, hlo64⟩
  obtain ⟨m58, m60, m98, ma0, ma8, mc8, m68, m70, m78, m80, m88⟩ := hM1
  have sv : ∀ {o : Nat}, 0x58 ≤ o → o + 8 ≤ 0xd0 →
      S1.mem.readLE (SP - 0x70 + o) 8 = (W1 (W0 s.mem (SP - 0x70) (s.regs 5).toNat zp xp) (SP - 0x70) st lm zc zl
        zp lo).readLE (SP - 0x70 + o) 8 := fun h1 h2 => by
    rw [slot _ (nSv (by omega) hle hA h1 h2).1 (nSv (by omega) hle hA h1 h2).2, hm']
  -- the fresh `xOdd`
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  obtain ⟨hts, hto⟩ := Exp.tz_spec hX
  rw [← htz] at hts hto
  have h2tz : 2 ^ tz ≤ natVal s.mem xp xl := Nat.le_of_dvd hX ⟨_, hts⟩
  have htzl : tz < 64 * xl := by
    have := Nat.lt_of_le_of_lt h2tz (natVal_lt s.mem xp xl)
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
  have hneed0 : 0 < Rsh.need xl tz := by simp only [Rsh.need]; omega
  obtain ⟨hv1, hn1, hlc1, hc140, hlive1, -, hfr1⟩ := hres
  have hc1 : Rsh.need xl tz ≤ c1 := hcap hneed0
  obtain ⟨hin1, hap1⟩ := hfr1 hneed0 (by omega)
  obtain ⟨hp8, hH1, hacc1, hp48⟩ := hlive1 (by omega)
  have hvxS : natVal S.mem xp xl = natVal s.mem xp xl :=
    hxH.readLE (hF0.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) (LiveFrame.of_nil' hLF0 _) (by
      simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hxw ⊢; omega)
  rw [hvxS] at hv1
  have hl1 : l1 ≤ xl := lenLe hn1 (by
    rw [hv1]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (natVal_lt s.mem xp xl))
  -- the run to the recursive entry
  have hacc2 : S1.mem.accessible (SP - 0x70 - 8) 0xd8 true = true := by
    rw [hFs.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  refine runRec (retAddrOf s) Q (SP - 0x70) zp zl zc st yp yl lm lo S1.mem hsp1 (by omega) hacc2
    (by rw [sv (by omega) (by omega), m78, show SP - 0x70 + 0x78 = SP + 0 + 8 by omega]; exact hy1)
    (by rw [sv (by omega) (by omega), m80, show SP - 0x70 + 0x80 = SP + 0 + 16 by omega]; exact hy2)
    (by rw [sv (by omega) (by omega), mc8]) (by rw [sv (by omega) (by omega), m58])
    (by rw [sv (by omega) (by omega), ma8]) (by rw [sv (by omega) (by omega), m60])
    (by rw [sv (by omega) (by omega), m98]) (by rw [sv (by omega) (by omega), ma0]) (by omega) S1 h1pc
    (by rw [h1sp, hsp]; exact nS (by omega) (hSP ▸ (s.regs 4).isLt)) rfl ?_
  intro S2 f0 fsp a0 a3 a1 a7 a6 a8 a9 a10 a5 a14 afs ax adf fm
  have hS2s : (S2.regs 4).toNat = SP - 0x78 := by
    rw [fsp, BitVec.toNat_ofNat]; omega
  have hSsp2 : (S2.regs 4).toNat + 0x78 = (s.regs 4).toNat := by rw [hS2s, hSP]; omega
  have e14 : S2.regs 14 = s.regs 14 := by rw [a14, h114, r14]
  have efs : S2.fsBase = s.fsBase := by rw [afs, efs1, rfs]
  have edf : S2.df = s.df := by rw [adf, edf1, rdf]
  have ex : S2.xmm 15 = s.xmm 15 := by rw [ax, h1x, rx]
  have hF2 : MemFrame s.mem S2.mem (R.rt ++ ownW s stk A) := by
    rw [fm]
    exact hFs.trans (mw_frame _ yp yl recR hsp1) fun a k ho => ⟨ho, by
      simp only [ownW, hSP, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
  have hLsw : LiveSep L [(SP - 0x70 - 8, SP - 0x70 + 0x18)] := fun r hr => by
    have := hLs r hr; simp only [win, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF2 : LiveFrame s.mem S2.mem L [] := by
    rw [fm]; exact hLFs.trans (LiveFrame.of_win (mw_frame S1.mem yp yl recR hsp1) hLsw) fun _ _ h => h
  have hrg2 : S2.mem.regions = s.mem.regions := by
    rw [fm]; simp only [Mw, Janus.Arm64.Memory.regions_writeLE]; rw [h1rg, hrgS]
  have hstO : Outside st 24 (ownW s stk A) := by
    simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF2 hLF2 hstO
  have hvy : natVal S2.mem yp yl = natVal s.mem yp yl :=
    hyH.readLE hF2 (LiveFrame.of_nil' hLF2 _) (by
      simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hyw ⊢; omega)
  have hpo : Outside p1 (8 * l1) [(SP - 0x70 - 8, SP - 0x70 + 0x18)] := by
    have := apart_sub (n' := 8 * l1) (hin1.apart hwin).symm (Nat.le_refl p1) (by omega)
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at this; omega
  have hvx : natVal S2.mem p1 l1 = natVal s.mem xp xl / 2 ^ tz := by
    rw [fm, ← hv1]; exact (mw_frame S1.mem yp yl recR hsp1).readLE _ _ hpo
  -- the fresh input's facts at the callee entry
  have hAw : ∀ {a n : Nat}, Held R L a n → Apart p1 (8 * l1) a n := fun h =>
    apart_sub (apF hin1 hap1 h) (Nat.le_refl _) (by omega)
  have hin : ∀ p n, (p, n) ∈ [(p1, l1), (yp, yl)] → EvenHyp.RdIn R L1 S2 (stk - 0x78) 72 p n ∧ n ≤ 2 ^ 9 ∧
      NatNorm S2.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (NHyp.freeOf S2.mem st).1 (NHyp.freeOf S2.mem st).2 ∧
      (0 < zc → Apart zp (8 * zc) p (8 * n)) := by
    intro p n hpn
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpn
    rcases hpn with ⟨hp, hn⟩ | ⟨hp, hn⟩ <;> rw [hp, hn]
    · have hnm : NatNorm S2.mem p1 l1 := by rw [fm]; exact nnFrame (mw_frame S1.mem yp yl recR hsp1) hpo hn1
      refine ⟨⟨by omega, by
          rw [fm]; simp only [Mw, Janus.Arm64.Memory.accessible_writeLE]
          exact Janus.Arm64.Memory.accessible_weaken _
            (Janus.Arm64.Memory.accessible_mono _ hacc1 (Nat.le_refl _) (by omega)),
        by omega, hH1.sub (Nat.le_refl _) (by omega), ?_⟩, by omega, hnm, hAw hsok.2.1, ?_, ?_⟩
      · have := (hin1.apart hwin)
        simp only [win, hS2s, outside_cons, outside_nil, and_true]; unfold Apart at this; omega
      · show Apart p1 (8 * l1) (stW S2.mem st + 8 * stLen S2.mem st) (8 * (stCap S2.mem st - stLen S2.mem st))
        rw [ew, el, ec]
        rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
        · have := hcap0 h0; have := hsok.2.2.2.2.2.1; unfold Apart; omega
        · have := hAw (hsok.2.2.2.2.1 h0).2.1; unfold Apart at this ⊢; omega
      · intro h0; exact (hAw (hzL h0).2.1).symm
    · exact in_sub hC (p := yp) (n := yl) (by simp) hF2 hLF2 hx hSsp2 (by omega) (by omega)
  have hk0 : 0x78 ≤ stk := Nat.le_trans (by decide) hk
  have hk78 : stk - 0x78 + 0x78 ≤ stk := nK hk0
  have hS78 : 0x78 ≤ SP := Nat.le_trans hk0 hle
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := nR1 hS78
  have hone2 := natOne_subR hone hsa hF2 hLF2 hx hSsp2 (stk' := stk - 0x78) (A' := 72) hk78 (by decide)
    ew el ec
  have hone1 : S2.mem.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 := by rw [hone2.1.1, hone.1]
  have hcf : cf (stLen S2.mem st) lm' ≤ b1 := by rw [el]; exact nCf hb1 hbud hcb
  have hinv2 : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S2.mem) := by
    rw [fm, ← r14]
    refine Expmc.inv_frame (mw_frame S1.mem yp yl recR hsp1) (fun r hr => Or.inr ?_) hinv1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hwin.of_sub (nI hk0 hle hA).1 (nI hk0 hle hA).2
  have hpre : PreD R b1 L1 (stk - 0x78) 72 (cf (stLen S2.mem st) lm') zp zl zc st p1 l1 yp yl lm' S2 :=
    ⟨cpre_sub hC hF2 hLF2 hrg2 hx hinv2 hSsp2 e14 efs hk78 (by decide) hin hneed hcf,
      by rw [hvx]; exact pos_odd hto, by rw [hvy]; exact hY, (nLm hlo hlm' hlm).1, (nLm hlo hlm' hlm).2, hst0, op,
      hone2⟩
  have hyp64 : yp < 2 ^ 64 := by rw [← hy1]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hyl64 : yl < 2 ^ 64 := by rw [← hy2]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hR2 : Regs S2 zp zl zc st p1 l1 c1 yp yl yc lm' := by
    refine ⟨a0, a3, a1, a7, a6.trans q0, a8.trans q1, a9.trans q2, by rw [a10, hlm'], ?_, ?_, ?_⟩
    · rw [hS2s, n1, fm]; exact mw_y0 hsp1 hyp64
    · rw [hS2s, n2, fm]; exact mw_y1 hsp1 hyl64
    · rw [hS2s, n3, fm, mw_y2 hsp1, sv (by decide) (by decide), m88, n4]; exact hy3
  have hraS : S2.mem.readLE (S2.regs 4).toNat 8 = recR := by
    rw [hS2s, n5, fm, mw_ra (by decide)]
  have hOX : OX S2 zp p1 l1 c1 :=
    ⟨⟨ex.trans hx15, edf.trans hdf, hzp⟩, by rw [hvx]; exact hto, hlc1, hc140,
      ⟨fun _ => apart_sub (n' := 8 * l1) (hin1.apart hgrt).symm (Nat.le_refl _) (nL hlc1),
        by rw [hone1]; exact hone2A, by rw [hF2.accessible]; exact hadx⟩, by rw [hraS]; decide⟩
  refine ReachesRet.call_regions (hO b1 L1 p1 l1 c1) f0 ⟨hR2, hpre, hOX⟩ fun S3 h3pc hq3 h3rg => ?_
  obtain ⟨⟨g4, -, g14, gx⟩, hcp⟩ := hq3
  rw [hvx, hvy, el] at hcp
  have hcp' := hcp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hFc, -⟩ := hcp'
  simp only [win, hS2s, stWs, stkWs, ew, el, ec] at hFc
  have hstw' : Outside st 24 [(SP - stk, SP + A)] := by simpa only [win, hSP] using hstw
  have harr' : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) [(SP - stk, SP + A)] := fun h => by
    have := (harr h).1; simpa only [win, hSP] using this
  have hzW' : 0 < zc → Outside zp (8 * zc) [(SP - stk, SP + A)] := fun h => by
    have := (hzW h).1; simpa only [win, hSP] using this
  have keep : ∀ {o : Nat}, 0x58 ≤ o → o + 8 ≤ 0x78 → S3.mem.readLE (SP - 0x70 + o) 8 = S1.mem.readLE (SP - 0x70 + o) 8 :=
    fun h1 h2 => by
      rw [keepS hFc hk0 hle hwin hstw' harr' hcap0 hsok.2.2.2.2.2.1 hzW' (nO hk0 hle hA h1 h2).1
        (nO hk0 hle hA h1 h2).2.1, fm, mw_rd hsp1 (Or.inr (nO hk0 hle hA h1 h2).2.2)]
  have k58 : S3.mem.readLE (SP - 0x70 + 0x58) 8 = lo := by
    rw [keep (by decide) (by decide), sv (by decide) (by decide), m58]
  have k68 : S3.mem.readLE (SP - 0x70 + 0x68) 8 = (s.regs 5).toNat := by
    rw [keep (by decide) (by decide), sv (by decide) (by decide), m68]
  have k70 : S3.mem.readLE (SP - 0x70 + 0x70) 8 = (retAddrOf s).toNat := by
    rw [keep (by decide) (by decide), sv (by decide) (by decide), m70, hrt, n6]
  have hbb := bud_sub (c := cf (stLen s.mem st) lm') hb1
  refine K S3 (by rw [h3pc]; simp only [retAddrOf, hraS]) ?_ (g14.trans e14) (gx.trans ex) (h3rg.trans hrg2) k58 k68
    k70 ?_
  · rw [g4, fsp, n7]; exact nS hS78 (hSP ▸ (s.regs 4).isLt)
  · exact cpost_pre (cpre_cst hC hbud) hF2 hLF2 hx hSsp2 e14 efs edf (stk' := stk - 0x78) (A' := 72) hk78
      (by decide) hbb hcp rfl rfl rfl rfl rfl rfl

end

end FvModexp.Amd64.P2D
