import FvModexp.Proofs.Amd64.Exp.EvJ
import FvModexp.Proofs.Amd64.Exp.EvCall
import FvModexp.Proofs.Amd64.Nat.RshDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `m2 = m2.rsh(m, n)` (nat.go:811), `J3` → `J4` (asm s58; twin of infra's arm64 `EvRsh`)

`runR`: `nat2R` → `nat.rsh`'s entry (`m = (mp, ml, mc)` from the caller area `0x168/0x170/0x178` into RDI/RSI/R8, `n`
from slot `0xb0` into R9, the return address `rshR` pushed). `segR`: the call through `Rsh.Hyp` (callee window
`stk ≤ K`, `above ≤ 0x7f`); `need = ml - n/64 = a2 = cap m2`, so the result stays in the scratch array `q`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `nat.rsh`'s entry -/
abbrev rshE : Nat := 0x5e69c0

theorem rsh_a : segAddr Extracted.program Rsh.fn = rshE := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `nat2R` → `nat.rsh`'s entry -/
theorem runR {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp mp ml mc n : Nat) (M : Memory)
    (h68 : M.readLE (sp + 0x168) 8 = mp) (h70 : M.readLE (sp + 0x170) 8 = ml) (h78 : M.readLE (sp + 0x178) 8 = mc)
    (hb0 : M.readLE (sp + 0xb0) 8 = n)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 nat2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 rshE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp)] → M'.regions = M.regions → M'.readLE (sp - 8) 8 = rshR →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = BitVec.ofNat 64 mp →
      S'.regs 6 = BitVec.ofNat 64 ml → S'.regs 8 = BitVec.ofNat 64 mc → S'.regs 9 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hmp : M.readLE (sp + 0x168) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hml : M.readLE (sp + 0x170) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : M.readLE (sp + 0x178) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
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
  janus64_run [h68, h70, h78, hb0, e4] until [rshE]
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

/-- the `m` operand facts of the entry -/
theorem EPre.mOp (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    OE R L sp K st s.mem mp (8 * ml) ∧ s.mem.accessible mp (8 * ml) false = true ∧ mp + 8 * ml ≤ 2 ^ 48 ∧
      NatNorm s.mem mp ml ∧ (0 < zc → Apart zp (8 * zc) mp (8 * ml)) ∧ mp < 2 ^ 64 ∧ mc < 2 ^ 40 ∧ ml ≤ mc ∧
      ml ≤ 128 := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨o1, o2, o3, o4, o5, -, -, o8, ⟨o9, o10⟩, -⟩, -⟩ := hP
  exact ⟨o1, o2, o3, o4, o5, o8, o9, o10, h6⟩

/-- the keep range of the push plus a callee with `above ≤ 0x7f` -/
theorem kk_push {M0 M M' : Memory} {ab : Nat} (hsp : 8 ≤ sp) (hab : ab ≤ 0x7f)
    (hF : MemFrame M0 M [(sp - 8, sp)])
    (hkc : ∀ a k, sp - 8 + ab ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) :
    ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k := fun a k h1 h2 => by
  rw [hkc a k (by omega) h2, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]

theorem need_a2 : Rsh.need ml (nE s mp ml) = a2 ml (nE s mp ml) := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J3` → `J4`** (see the module doc) -/
theorem segR {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (hkR : stkR ≤ K) (haR : aboveR ≤ 0x7f)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : makeCost (a2 ml (nE s mp ml)) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K4 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 : Nat),
      J4 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q l2 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q : Nat}
    (h : J3 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  obtain ⟨mOE, macc, m48, mN, mza, mp64, mc40, mlc, ml128⟩ := hP.mOp
  have ha2 : 0 < a2 ml (nE s mp ml) ∧ a2 ml (nE s mp ml) ≤ 128 := by simp only [a2]; omega
  have hsp8 : 8 ≤ sp := by omega
  have hw := h.jx.wc
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hesl := h.jx.esl
  have h68 : S.mem.readLE (sp + 0x168) 8 = mp := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h70 : S.mem.readLE (sp + 0x170) 8 = ml := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h78 : S.mem.readLE (sp + 0x178) 8 = mc := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb0 : S.mem.readLE (sp + 0xb0) 8 = nE s mp ml := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hd0 := h.d2
  obtain ⟨dw, dh, -, -, -⟩ := Loc.ap hP (hd0.2.2 ha2.1).1
  have hdm : Apart q (8 * a2 ml (nE s mp ml)) mp (8 * ml) :=
    Loc.apart (hd0.2.2 ha2.1).1 ha2.1 mOE.1 (fun _ => mOE.2.2.2)
  refine runR ret0 Q sp mp ml mc (nE s mp ml) S.mem h68 h70 h78 hb0 hacc0 (by omega) (by omega) S h.pc h.jx.esp
    rfl ?_
  intro S' M' f0 f4 fm hFp hrgp frd r0 r3 r1 r7 r6 r8 r9 r5 r14 rfs rx15 rdf
  have hown : ∀ q ∈ [(sp - 8, sp)], OwnR sp K q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [OwnR]; omega
  obtain ⟨hwp, hlnp⟩ := WC.own hP hw hFp hrgp hown
  have hd := DL.own hP hd0 hFp hown
  have hm1 := hlnp _ _ _ _ h.m1
  have tsp : (S'.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S'.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S'.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  obtain ⟨hrd, hNm, -, hv⟩ := obj_at (above := aboveR) hP hwp mOE macc m48 mN (by omega) mza tsp fm hkR (by omega)
  have hS := Ensures.toSummaryIn (hrh b1 L1 (BitVec.ofNat 64 q) (BitVec.ofNat 64 (a2 ml (nE s mp ml)))
    (BitVec.ofNat 64 (a2 ml (nE s mp ml))) (BitVec.ofNat 64 mp) (BitVec.ofNat 64 ml) (BitVec.ofNat 64 mc)
    (BitVec.ofNat 64 (nE s mp ml)))
    (A64.noExit_restrict64 hap ns) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap hns)
  rw [rsh_a] at hS
  have tq : (BitVec.ofNat 64 q).toNat = q := by have := (hd0.2.1 ha2.1).2.2.2; simp only [BitVec.toNat_ofNat]; omega
  have ta : (BitVec.ofNat 64 (a2 ml (nE s mp ml))).toNat = a2 ml (nE s mp ml) := by
    simp only [BitVec.toNat_ofNat]; omega
  have tm : (BitVec.ofNat 64 mp).toNat = mp := by simp only [BitVec.toNat_ofNat]; omega
  have tl : (BitVec.ofNat 64 ml).toNat = ml := by simp only [BitVec.toNat_ofNat]; omega
  have tc : (BitVec.ofNat 64 mc).toNat = mc := by simp only [BitVec.toNat_ofNat]; omega
  have tn : (BitVec.ofNat 64 (nE s mp ml)).toNat = nE s mp ml := by simp only [BitVec.toNat_ofNat]; omega
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, ?pre⟩
    (fun s' hr hq hrg => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap hnf 375 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0.trans h.r0, r3.trans h.r3, r1.trans h.r1, r7, r6, r8, r9, trivial⟩
  case pre =>
    rw [tq, ta, tm, tl, tc, tn]
    refine ⟨⟨CallW.callEnv_of (hwp.cenv hP) tsp tg tfs fm hkR (by omega) (by omega), hsv, Nat.le_refl _,
      hd.wr hP tsp tg tfs fm hkR haR, hrd, by omega, fun _ => hdm, ?_, by omega, Or.inl hn0,
      bud_pre h.jx.bud hrk, by rw [tg, fm]; exact hwp.inv⟩, mlc, mc40⟩
    rw [fm]; exact hNm
  obtain ⟨⟨e4, -, e14, ex15⟩, hq⟩ := hq
  rw [tq, ta, tm, tl, tn] at hq
  obtain ⟨efs, edf, p', l', c', g0, g3, g1, L2, b2, hres, -, ⟨hx, hb, hinv⟩, hF, hLF⟩ := hq
  simp only [win, tsp] at hF
  rw [fm] at hF hLF hres hrg
  rw [tg] at hinv
  obtain ⟨hF', hLF', hsb, ehd⟩ := nonStk hwp.sok hx hF hLF (hP.st_cw hkR haR) (out1_of_apart dh)
  obtain ⟨hw', hkc, hln⟩ := stepC hP hwp (Loc.sub (hd.2.2 ha2.1).1) (Loc.subL (hd.2.2 ha2.1).1) dw hkR (by omega)
    hF' hLF' hrg hx hinv hsb
  obtain ⟨ep, ec⟩ := hres.2.2.2.2.2.1 (Nat.le_refl _)
  have hm2 := LN.of_res hP hwp hd hres hx hsb (fun _ hne => absurd ehd hne)
  rw [hv, ep, ec] at hm2
  rw [ep] at g0
  rw [ec] at g1
  have hm1' := hln _ _ _ _ hm1 (fun _ => h.ap.symm)
  have hS4 : s'.regs 4 = S.regs 4 := by rw [e4, f4, h.jx.esp]; exact bv_add8 (by omega) (by omega)
  have hkk := kk_push hsp8 haR hFp hkc
  refine K4 s' L2 b2 p1 l1 c1 q l' ⟨?_, by rw [hr, retAddrOf_eq, tsp, fm, frd], g0, g3, g1, ?_, ?_, ?_, hm1', h.c1p,
    hm2, h.ap⟩
  · exact h.jx.call hS4 (e14.trans r14) (efs.trans rfs) (ex15.trans rx15) (edf.trans rdf) hw' hkk
      (bud_step h.jx.bud hrk hb)
  · rw [kk_off hkk 0x118 8 (by decide) (by decide)]; exact h.s118
  · rw [kk_off hkk 0xc8 8 (by decide) (by decide)]; exact h.sc8
  · rw [kk_off hkk 0xd0 8 (by decide) (by decide)]; exact h.sd0

end

end FvModexp.Amd64.ExpEven
