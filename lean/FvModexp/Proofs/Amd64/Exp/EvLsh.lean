import FvModexp.Proofs.Amd64.Exp.EvJ
import FvModexp.Proofs.Amd64.Exp.EvCall
import FvModexp.Proofs.Amd64.Nat.LshDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `m1 = m1.lsh(natOne, n)` (nat.go:808), `J1` → `J2` (asm s57; twin of infra's arm64 `EvLsh`)

`runL`: `nat1R` → `nat.lsh`'s entry (the `natOne` header from `.data` into RDI/RSI/R8, `n` from slot `0xb0` into R9,
the return address `lshR` pushed). `segL`: the call through `Lsh.Hyp2` (callee window `stk ≤ K`, `above ≤ 0x7f`),
`m1 = 2^n` as a live local in its own scratch array.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `nat.lsh`'s entry -/
abbrev lshE : Nat := 0x5e6620

/-- a one-range `Outside` on a sub-range -/
theorem out1_mono {a n lo hi lo' hi' : Nat} (h : Outside a n [(lo, hi)]) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    Outside a n [(lo', hi')] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

theorem lsh_a : segAddr Extracted.program Lsh.fn = lshE := by decide
theorem natOneA_v : EvenHyp.natOneA = 12050400 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `nat1R` → `nat.lsh`'s entry -/
theorem runL {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp n op : Nat) (M : Memory)
    (h0 : M.readLE 12050400 8 = op) (h8 : M.readLE (12050400 + 8) 8 = 1) (h16 : M.readLE (12050400 + 16) 8 = 1)
    (hacc : M.accessible 12050400 24 false = true) (hb0 : M.readLE (sp + 0xb0) 8 = n)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 nat1R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 lshE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp)] → M'.regions = M.regions → M'.readLE (sp - 8) 8 = lshR →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = BitVec.ofNat 64 op →
      S'.regs 6 = BitVec.ofNat 64 1 → S'.regs 8 = BitVec.ofNat 64 1 → S'.regs 9 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hop : M.readLE 12050400 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hn : M.readLE (sp + 0xb0) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
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
  janus64_run [h0, h8, h16, hb0, e4] until [lshE]
  refine KN _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod]
  all_goals first | omega | rfl | skip

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J1` → `J2`** (see the module doc) -/
theorem segL {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ K) (haL : aboveL ≤ 0x7f)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : makeCost (a1 (nE s mp ml) + 1) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K2 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 : Nat),
      J2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p : Nat}
    (h : J1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hml := hP.2.2.2.2.2.1
  have hw := h.jx.wc
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  obtain ⟨op, ⟨o0, o8, o16, o1, oA, -, -, oa, o48, oh, ow⟩, -, ⟨-, -, -, -, -, -, -, -, -, ohE, -⟩, hsaE⟩ :=
    natOne_at hP hw (stk := stkL) (above := aboveL) (lo := sp - 8) (hi := sp + 8) hkL (by omega) (by omega)
      (by omega)
  rw [natOneA_v] at o0 o8 o16 oA
  have hb0 : S.mem.readLE (sp + 0xb0) 8 = nE s mp ml := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hd0 := h.d1
  have ha10 : 0 < a1 (nE s mp ml) := by simp only [a1]; omega
  obtain ⟨dw, dh, -, -, -⟩ := Loc.ap hP (hd0.2.2 ha10).1
  have hdo : Apart p (8 * a1 (nE s mp ml)) op (8 * 1) :=
    Loc.apart (hd0.2.2 ha10).1 ha10 ohE (hsaE (by omega)).2
  have hp48 : p < 2 ^ 64 := by have := (hd0.2.1 ha10).2.2.2; omega
  have hop : op < 2 ^ 64 := by omega
  refine runL ret0 Q sp (nE s mp ml) op S.mem o0 o8 o16 oA hb0 hacc0 (by omega) (by omega) S h.pc h.jx.esp rfl ?_
  intro S' M' f0 f4 fm hFp hrgp frd r0 r3 r1 r7 r6 r8 r9 r5 r14 rfs rx15 rdf
  -- the context after the push
  have hown : ∀ q ∈ [(sp - 8, sp)], OwnR sp K q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [OwnR]; omega
  obtain ⟨hwp, -⟩ := WC.own hP hw hFp hrgp hown
  have hd := DL.own hP hd0 hFp hown
  have tsp : (S'.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S'.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S'.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  rw [outside_append, outside_append] at ow
  obtain ⟨ow1, ow2, -⟩ := ow
  have owp : Outside op 8 [(sp - 8, sp)] := out1_mono ow2 (Nat.le_refl _) (by omega)
  have oww : Outside op (8 * 1) (win S' stkL aboveL) := by
    simp only [win, tsp]; exact out1_mono ow1 (by omega) (by omega)
  have hv1 : natVal M' op 1 = 1 := by
    simp only [natVal, Nat.mul_one]; rw [hFp.readLE _ _ owp]; exact o1
  have hS := Ensures.toSummaryIn (hlh b1 L1 (BitVec.ofNat 64 p) (BitVec.ofNat 64 (a1 (nE s mp ml)))
    (BitVec.ofNat 64 (a1 (nE s mp ml))) (BitVec.ofNat 64 op) (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
    (BitVec.ofNat 64 (nE s mp ml)))
    (A64.noExit_restrict64 hap ns) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap hns)
  rw [lsh_a] at hS
  have tp : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have ta : (BitVec.ofNat 64 (a1 (nE s mp ml))).toNat = a1 (nE s mp ml) := by
    simp only [BitVec.toNat_ofNat, a1]; omega
  have to : (BitVec.ofNat 64 op).toNat = op := by simp only [BitVec.toNat_ofNat]; omega
  have t1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have tn : (BitVec.ofNat 64 (nE s mp ml)).toNat = nE s mp ml := by simp only [BitVec.toNat_ofNat]; omega
  have ema : 1 + nE s mp ml / 64 + 1 = a1 (nE s mp ml) + 1 := by simp only [a1]; omega
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, ?pre⟩
    (fun s' hr hq hrg => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap hnf 293 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0.trans h.r0, r3.trans h.r3, r1.trans h.r1, r7, r6, r8, r9, trivial⟩
  case pre =>
    rw [tp, ta, to, t1, tn]
    refine ⟨⟨CallW.callEnv_of (hwp.cenv hP) tsp tg tfs fm hkL (by omega) (by omega), hsv, Nat.le_refl _,
      hd.wr hP tsp tg tfs fm hkL haL, ⟨by omega, by rw [fm, hFp.accessible]; exact oa, o48, oh, ?_⟩, by omega,
      Or.inr fun _ _ => hdo, ?_, by rw [tg, fm]; exact hwp.inv⟩, hn0, by omega⟩
    · exact oww
    · rw [ema]; exact bud_pre h.jx.bud hrk
  obtain ⟨⟨e4, -, e14, ex15⟩, hq⟩ := hq
  rw [tp, ta, to, t1, tn] at hq
  obtain ⟨efs, edf, p', l', c', g0, g3, g1, L2, b2, hres, hcap, ⟨hx, hb, hinv⟩, hF, hLF⟩ := hq
  rw [ema] at hb hcap hres
  simp only [win, tsp] at hF
  rw [fm] at hF hLF hres hrg
  rw [tg] at hinv
  obtain ⟨hF', hLF', hsb, ehd⟩ := nonStk hwp.sok hx hF hLF (hP.st_cw hkL haL) (out1_of_apart dh)
  obtain ⟨hw', hkc, -⟩ := stepC hP hwp (Loc.sub (hd.2.2 ha10).1) (Loc.subL (hd.2.2 ha10).1) dw hkL (by omega)
    hF' hLF' hrg hx hinv hsb
  have hm1 := LN.of_res hP hwp hd hres hx hsb (fun _ hne => absurd ehd hne)
  rw [hv1, Nat.one_mul] at hm1
  have hc1 : 0 < c' := Nat.lt_of_lt_of_le (Nat.succ_pos _) (hcap (Nat.lt_succ_self _))
  have hS4 : s'.regs 4 = S.regs 4 := by rw [e4, f4, h.jx.esp]; exact bv_add8 (by omega) (by omega)
  have hkk : ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → s'.mem.readLE a k = S.mem.readLE a k := fun a k h1 h2 => by
    rw [hkc a k (by omega) h2, hFp.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  refine K2 s' L2 b2 p' l' c' ⟨?_, by rw [hr, retAddrOf_eq, tsp, fm, frd], g0, g3, g1, ?_, hm1, hc1⟩
  · exact h.jx.call hS4 (e14.trans r14) (efs.trans rfs) (ex15.trans rx15) (edf.trans rdf) hw' hkk
      (bud_step h.jx.bud hrk hb)
  · rw [hkk _ _ (by omega) (by omega)]; exact h.sd8

end

end FvModexp.Amd64.ExpEven
