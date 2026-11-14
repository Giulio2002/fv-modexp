import FvModexp.Proofs.Amd64.Exp.EvNP
import FvModexp.Proofs.Amd64.Exp.EvJ2
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `nat3R` → `z1 = z1.expNN(stk, x, y, m1, false)` → `exp1R` (asm s59; twin of infra's
arm64 `EvE1`)

`runE1`: the stack arguments `y` (caller area `0x150 … 0x160`) and `m1` (slots `0x118/0xc8/0xd0`) to `sp + 0 …
sp + 0x28`, `RDI = stk`, `RSI/R8/R9 = x` (spills `0x198 … 0x1b0`), `R10 = 0`, `CALL nat.expNN` (`RAX/RBX/RCX` = the
scratch `z1` from `stk.nat`). `segE1` (`J5 → J6`): the premise `EvenHyp.ExpNNHypNE1` (`m1 = 2^n`: the power-of-two
disjunct), `ExpN.NPre` from `npre_of`; `m1`, `m2` survive (`stepC`, apart from `z1`'s array); the result is located
(`LN.of_expN`); an empty result (possibly `nil`) is `EL`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `nat.expNN`'s entry -/
abbrev expNE : Nat := 0x5e6fa0

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `nat3R` → `nat.expNN`'s entry -/
theorem runE1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp st xp xl xc yp yl yc p1 l1 c1 : Nat) (M : Memory)
    (h50 : M.readLE (sp + 0x150) 8 = yp) (h58 : M.readLE (sp + 0x158) 8 = yl) (h60 : M.readLE (sp + 0x160) 8 = yc)
    (h18 : M.readLE (sp + 0x118) 8 = p1) (hc8 : M.readLE (sp + 0xc8) 8 = l1) (hd0 : M.readLE (sp + 0xd0) 8 = c1)
    (h98 : M.readLE (sp + 0x198) 8 = st) (ha0 : M.readLE (sp + 0x1a0) 8 = xp) (ha8 : M.readLE (sp + 0x1a8) 8 = xl)
    (hb0 : M.readLE (sp + 0x1b0) 8 = xc)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 nat3R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 expNE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 0x30)] → M'.regions = M.regions → M'.readLE (sp - 8) 8 = exp1R →
      M'.readLE sp 8 = yp → M'.readLE (sp + 8) 8 = yl → M'.readLE (sp + 0x10) 8 = yc →
      M'.readLE (sp + 0x18) 8 = p1 → M'.readLE (sp + 0x20) 8 = l1 → M'.readLE (sp + 0x28) 8 = c1 →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = BitVec.ofNat 64 st →
      S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 8 = BitVec.ofNat 64 xl → S'.regs 9 = BitVec.ofNat 64 xc →
      S'.regs 10 = BitVec.ofNat 64 0 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have b1 : yp < 2 ^ 64 := h50 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b2 : yl < 2 ^ 64 := h58 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b3 : yc < 2 ^ 64 := h60 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b4 : p1 < 2 ^ 64 := h18 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b5 : l1 < 2 ^ 64 := hc8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b6 : c1 < 2 ^ 64 := hd0 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at KN
  generalize x3 : S.regs 3 = r3 at KN
  generalize x1 : S.regs 1 = r1 at KN
  generalize x5 : S.regs 5 = r5 at KN
  generalize x14 : S.regs 14 = r14 at KN
  generalize xf : S.fsBase = rf at KN
  generalize xx : S.xmm 15 = rx at KN
  generalize xd : S.df = rd at KN
  janus64_run [h50, h58, h60, h18, hc8, hd0, h98, ha0, ha8, hb0, e4] until [expNE]
  refine KN _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat
      refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x30)) (by simp) (by simp only; omega)
        (by simp only; omega)
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | skip

/-- the keep range of the stores `[sp - 8, sp + 0x30)` plus a callee with `above ≤ 0x7f` -/
theorem kk_args {sp : Nat} {M0 M M' : Memory} {ab : Nat} (hsp : 8 ≤ sp) (hab : ab ≤ 0x7f)
    (hF : MemFrame M0 M [(sp - 8, sp + 0x30)])
    (hkc : ∀ a k, sp - 8 + ab ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) :
    ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k := fun a k h1 h2 => by
  rw [hkc a k (by omega) h2, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J5` → `J6`** (see the module doc) -/
theorem segE1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {cDl : Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : ∀ costD, EvenHyp.ExpNNHypNE1 impl R KN costF costD needR costR needS needP costS costP)
    (hKN : 41640 ≤ KN) (hKN1 : KN + 0x498 ≤ K) (hKN2 : KN + 0x98 ≤ 2 ^ 20)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) (hX : NHyp.XFacts R L xp xl xc) (hXC : XC R L sp K st s.mem xp xc)
    (hXG : ExpN.XG s.mem st xp xl xc)
    (hst : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → NStkE needR needS needP xl yl l1 (lvl3 s st mp ml l1 l2) (nE s mp ml))
    {rk rk' : Nat}
    (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml →
      NBudE costR costS costP xl yl l1 (lvl3 s st mp ml l1 l2) (nE s mp ml) ≤ rk ∧
      ExpOdd.OBud costF l1 (cDl l1 (lvl3 s st mp ml l1 l2))
        xl yl (lvl3 s st mp ml l1 l2) (rk - makeCost l1) ∧
      ExpN.NCost (cDl l1 (lvl3 s st mp ml l1 l2))
        costR costS costP xl yl l1 (lvl3 s st mp ml l1 l2) (nE s mp ml) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K6 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz : Nat),
      J6 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 t : Nat}
    (h : J5 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 t) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hml := hP.2.2.2.2.2.1
  have ha2 : 0 < a2 ml (nE s mp ml) ∧ a2 ml (nE s mp ml) ≤ ml := by simp only [a2]; omega
  have hsp8 : 8 ≤ sp := by omega
  have hsp64 : sp < 2 ^ 64 := by omega
  have h4a0 : sp - 8 - 0x498 = sp - 0x4a0 := by omega
  have hsp2 : sp + 0x1b8 ≤ 2 ^ 48 := by omega
  have hw := h.jx.wc
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hown : ∀ q ∈ [(sp - 8, sp + 0x30)], OwnR sp K q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [OwnR]; omega
  have hs8 : (BitVec.ofNat 64 (sp - 8)).toNat = sp - 8 := by rw [BitVec.toNat_ofNat]; omega
  have hg' : (BitVec.ofNat 64 g).toNat = g := by rw [← hP.1.2.1]; exact EEnv.g hP.1
  have hm1 := h.m1
  have hm2 := h.m2
  have hd3 := h.d3
  have hb1 := h.jx.bud
  have hl1m : l1 ≤ ml := by
    have hv : natVal S.mem p1 l1 < 2 ^ (64 * ml) := by
      rw [hm1.2.2.1]; exact Nat.pow_lt_pow_right (by decide) hnl
    exact nlen_bd' hm1.2.2.2 hv
  have hl2m : l2 ≤ ml := Nat.le_trans hm2.2.1 ha2.2
  have hl1p : 0 < l1 := by
    rcases Nat.eq_zero_or_pos l1 with h0 | h0
    · have hv := hm1.2.2.1
      rw [h0, natVal_zero] at hv
      exact absurd hv.symm (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
    · exact h0
  have hk0 : 0 < 2 * max l1 l2 :=
    Nat.mul_pos (by decide) (Nat.lt_of_lt_of_le hl1p (Nat.le_max_left _ _))
  have hrl := (hd3.2.2 hk0).1
  obtain ⟨dw, -, -, -, -⟩ := Loc.ap hP hrl
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hst l1 l2 hl1m hl2m
  obtain ⟨hrk1, hrk2, hrk3⟩ := hrk l1 l2 hl1m hl2m
  have hesl := h.jx.esl
  refine runE1 ret0 Q sp st xp xl xc yp yl yc p1 l1 c1 S.mem hesl.2.2.2.2.2.2.2.2.2.2.2.2.1
    hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.s118 h.sc8 h.sd0
    hesl.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.2.1
    hacc0 hsp8 hsp2 S h.pc h.jx.esp rfl ?_
  intro S' M' f0 f4 fm hFp hrgp frd w0 w8 w10 w18 w20 w28 r0 r3 r1 r7 r6 r8 r9 r10 r5 r14 rfs rx15 rdf
  obtain ⟨hwp, hlnp⟩ := WC.own hP hw hFp hrgp hown
  have hd := DL.own hP hd3 hFp hown
  have hm1p := hlnp _ _ _ _ hm1
  have hm2p := hlnp _ _ _ _ hm2
  have tsp : (S'.regs 4).toNat = sp - 8 := by rw [f4]; exact hs8
  have tg : (S'.regs 14).toNat = g := by rw [r14, h.jx.e14]; exact hg'
  have tfs : S'.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  have hv1 : natVal M' p1 l1 = 2 ^ nE s mp ml := hm1p.2.2.1
  have hlg : Nat.log2 (natVal M' p1 l1) = nE s mp ml := by rw [hv1, Nat.log2_two_pow]
  have hlen : stLen M' st = lvl3 s st mp ml l1 l2 := hwp.len
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, hoy, hay, hy48, hyN, -, hyl, hox, hax, hx48, hxN, hxl, -, -, -, -, hz, -⟩ := hP'
  obtain ⟨-, -, -, xv⟩ := obj_at hP hwp hox hax hx48 hxN (Nat.le_trans hxl (by decide))
    (fun h0 => (hz h0).2.2.2.2.2.2.1) tsp fm (stk := 0) (above := 0) (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨-, -, -, yv⟩ := obj_at hP hwp hoy hay hy48 hyN (Nat.le_trans hyl (by decide))
    (fun h0 => (hz h0).2.2.2.2.2.2.2.1) tsp fm (stk := 0) (above := 0) (Nat.zero_le _) (Nat.zero_le _)
  have hnp := npre_of hP hwp hXC hXG hX (S := S') (f4) (r14.trans h.jx.e14) tfs (rx15.trans h.jx.ex15)
    (rdf.trans h.jx.edf) fm hKN hKN1 hKN2 (costF := costF)
    (costD := cDl l1 (lvl3 s st mp ml l1 l2)) (needR := needR) (costR := costR)
    (needS := needS) (needP := needP) (costS := costS) (costP := costP) hm1p hl1p (Nat.le_trans hl1m hml) hd hk0 h.ap1
    w0 w8 w10 w18 w20 w28 (by rw [hlen]; exact hs1) (by rw [hlen]; exact hs2) (by rw [hlen]; exact hs3)
    (by rw [hlen, hlg]; exact hs4) (by rw [hlen, hlg]; exact Nat.le_trans hrk1 hb1)
    (by rw [hlen]; exact OBud.mono hrk2 (Nat.sub_le_sub_right hb1 _))
  have hS := Ensures.toSummaryIn (hE (cDl l1 (lvl3 s st mp ml l1 l2))
      b1 L1 t (2 * max l1 l2) (2 * max l1 l2) st xp xl xc yp yl yc p1 l1 c1 0)
    (A64.noExit_restrict64 hap ExpN.names) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap libN_sub)
  rw [expN_a] at hS
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, ?pre⟩
    (fun s' hr hq hrg => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap libN_nf 556 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0.trans h.r0, r3.trans h.r3, r1.trans h.r1, r7, r6, r8, r9, r10, trivial⟩
  case pre =>
    refine ⟨by rw [tsp, tg, tfs, h4a0]; exact hnp,
      Or.inr ⟨nE s mp ml, by rw [fm]; exact hv1⟩, NHyp.XFacts.ext hw.le hX⟩
  obtain ⟨⟨e4, -, e14, ex15⟩, efs, edf, p, l, c, g0, g3, g1, hv, hN, hlc, ⟨hc40, hp64⟩, L2, b2, hx, hb, hinv, hlv,
    hres, hsb, hF, hLF, hrs⟩ := hq
  simp only [win, tsp] at hF
  rw [fm] at hF hLF hrg hsb hrs hv hb
  rw [tg] at hinv
  rw [hlen, hlg] at hb
  rw [xv, yv, hv1] at hv
  obtain ⟨hw', hkc, hkeep⟩ := stepC hP hwp (Loc.sub hrl) (Loc.subL hrl) dw (stk := KN + 0x498) (above := 0x78)
    hKN1 (by decide) hF hLF hrg hx hinv hsb
  have hz1 := LN.of_expN hP hwp hd hv hN hlc hc40 hlv hres hx hsb hrs
  have hm1' := hkeep _ _ _ _ hm1p fun _ => h.ap1.symm
  have hm2' := hkeep _ _ _ _ hm2p fun _ => h.ap2.symm
  have hS4 : s'.regs 4 = S.regs 4 := by rw [e4, f4, h.jx.esp]; exact bv_add8 hsp8 hsp64
  have hkk := kk_args hsp8 (by decide) hFp hkc
  have hza : ∀ (t' n : Nat), Held R L1 t' n → Apart t (8 * (2 * max l1 l2)) t' n → 0 < c → Apart p (8 * c) t' n := by
    intro t' n hh ht hc0
    rcases hres with ⟨e, -⟩ | ⟨rfl, rfl⟩ | ⟨hin, hap'⟩
    · omega
    · exact ht
    · exact hfresh hh hap' hin
  refine K6 s' L2 b2 p1 l1 c1 q l2 p l c ⟨h.jx.call hS4 (e14.trans r14) (efs.trans rfs) (ex15.trans rx15)
    (edf.trans rdf) hw' hkk (bud_step hb1 hrk3 hb), by rw [hr, retAddrOf_eq, tsp, fm, frd], g0, g3, g1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm1', h.c1p, hm2', h.ap, hz1, hp64, ?_,
    fun hc0 => hza _ _ (hm1p.1.2.1 h.c1p).2.1 h.ap1 hc0, fun hc0 => hza _ _ (hm2p.1.2.1 ha2.1).2.1 h.ap2 hc0⟩
  · rw [kk_off hkk 0x118 8 (by decide) (by decide)]; exact h.s118
  · rw [kk_off hkk 0xc8 8 (by decide) (by decide)]; exact h.sc8
  · rw [kk_off hkk 0xd0 8 (by decide) (by decide)]; exact h.sd0
  · rw [kk_off hkk 0x110 8 (by decide) (by decide)]; exact h.s110
  · rw [kk_off hkk 0xb8 8 (by decide) (by decide)]; exact h.sb8
  · rw [kk_off hkk 0xc0 8 (by decide) (by decide)]; exact h.sc0
  · rw [kk_off hkk 0xd8 8 (by decide) (by decide)]; exact h.sd8
  · intro hc0
    rcases hres with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hin, hap'⟩
    · exact Or.inl e
    · omega
    · rw [hc0, Nat.mul_zero] at hin hap'
      exact Or.inr ⟨hin, fun r hr => hap' r (hw.le.mem_old hr)⟩

end

end FvModexp.Amd64.ExpEven
