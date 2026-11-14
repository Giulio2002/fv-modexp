import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.Exp.SlowMuP
import FvModexp.Proofs.Amd64.Exp.SlowPM

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the loop's generic `zz = zz.mul(stk, z, x)` step (agent expmc s81; twin of arm64
`Q.ExpSlow.mulSQ`)

`mulS`: at the `nat.mul` entry `T` (`RSP = sp - 8`, `[sp - 8] = fnE + idx`), reached from `S0` with `JC` through the
caller's own stores, `zz` in `(AX, BX, CX)`, `stk` in `DI`, `z` in `(SI, R8, R9)`, `x` at `sp + 0 / 8 / 0x10`
(`Q.DivRec.MulHypQE`, `LibCalls.mulCallQ`): the continuation gets `JC` at the return, the slots `[sp + 0x68, sp + 0x220)`
kept and the buffers ROTATED (`z := result` of value `Zv·X`, `len ≤ len z + len x`; `zz := old z`; `r`, `q` kept).
Used by both loops (`ml1R`, `ml2R`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `zz = zz.mul(stk, z, x)` step** (see the module doc) -/
theorem mulS {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} (hml : Q.DivRec.MulHypQE impl R ns W) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {S0 : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hj : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S0 L1 b1)
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hB : BB R L st zp zc S0.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl)
    (hzl : zl ≤ 2 ^ 12) (hmW : mulW64 zl xl ≤ W) (hs16 : stLen s.mem st + 4 * (zl + xl) + 64 ≤ 2 ^ 16)
    (hH : stLen s.mem st + 4 * (zl + xl) + 64 ≤ H) (hcost : mulCQ zl xl + stkR H S0.mem st ≤ b1)
    {ret0 : W64} {Q : State → Prop} {idx : Nat} (hidx : idx < 0x84d)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6228032) (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = S0.regs 14) (hfs : T.fsBase = S0.fsBase) (hx15 : T.xmm 15 = S0.xmm 15)
    (hdf : T.df = S0.df) {ws : List (Nat × Nat)} (hF : MemFrame S0.mem T.mem ws)
    (hrg : T.mem.regions = S0.mem.regions) (hws : ∀ r ∈ ws, OwnR sp K r)
    (hkw : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → T.mem.readLE a k = S0.mem.readLE a k)
    (hrd : T.mem.readLE (sp - 8) 8 = fnE + idx)
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h3 : T.regs 3 = BitVec.ofNat 64 zzl) (h1 : T.regs 1 = BitVec.ofNat 64 zzc)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 z) (h8 : T.regs 8 = BitVec.ofNat 64 zl)
    (h9 : T.regs 9 = BitVec.ofNat 64 zc') (hy0 : T.mem.readLE sp 8 = xp) (hy1 : T.mem.readLE (sp + 8) 8 = xl)
    (hy2 : T.mem.readLE (sp + 16) 8 = xc)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat), s'.rip = BitVec.ofNat 64 (fnE + idx) →
      JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s s' L2 b2 →
      (∀ a k, sp + 0x68 ≤ a → a + k ≤ sp + 0x220 → s'.mem.readLE a k = T.mem.readLE a k) →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c' →
      BB R L st zp zc s'.mem L2 p' l' c' (Zv * natVal s.mem xp xl) z zl zc' rr rl rc q ql qc → l' ≤ zl + xl →
      b1 - (mulCQ zl xl + stkR H S0.mem st) + stkR H s'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hsp64 : sp < 2 ^ 64 := by omega
  obtain ⟨hw, hdl, hln⟩ := WC.own hP hj.wc hF hrg hws
  have hzz := hdl _ _ hB.bzz
  have hz := hln _ _ _ _ hB.bz
  have hr := hdl _ _ hB.br
  have hq := hdl _ _ hB.bq
  have hce := hw.cenv hP
  obtain ⟨-, -, -, -, hg1, -⟩ := hce
  have tsp : (T.regs 4).toNat = sp - 8 := by rw [h4, BitVec.toNat_ofNat]; omega
  have tg : (T.regs 14).toNat = g := by rw [h14, hj.e14, BitVec.toNat_ofNat]; omega
  have tfs : T.fsBase.toNat = fs := by rw [hfs]; exact hj.efs
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  have hhd : Outside st 24 ws := by
    refine outside_of_forall ?_
    intro r hr; have := hws r hr; omega
  have hcap : stCap T.mem st = stCap S0.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have eR : stkR H T.mem st = stkR H S0.mem st := stkR_congr hcap
  have hpre := mulPreS hP hw hWK tsp tg tfs rfl hzz hz hB.p1 hX hzl hmW hs16 hH (by rw [eR]; exact hcost)
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  have bst : st < 2 ^ 64 := by have := hw.sok.2.2.2.1; omega
  have hzlc := hB.bz.2.1
  have bx := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bxc := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxv : natVal T.mem xp xl = natVal s.mem xp xl := by
    show T.mem.readLE xp (8 * xl) = s.mem.readLE xp (8 * xl)
    simpa using x_rd hP hw (j := 0) (k := 8 * xl) (by omega)
  have s8 : (T.regs 4).toNat + 8 = sp := by rw [tsp]; omega
  refine LibCalls.mulCallQ hap hns hml H (b := b1) (L := L1) (ra_slow hap hnf idx hidx) hpc (by rw [tsp]; exact hrd)
    h0 h3 h1 h7 h6 h8 h9 (hx15.trans hj.ex15) (hdf.trans hj.edf) bzz bzzc bst bz (by omega) bzc
    (by rw [s8]; exact hy0) (by rw [tsp, show sp - 8 + 16 = sp + 8 by omega]; exact hy1)
    (by rw [tsp, show sp - 8 + 24 = sp + 16 by omega]; exact hy2) hpre ?_
  intro s' hpc' hsp' _ h14' hx' hrg' hpost
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, hval, hnorm, hlc, hl2, hc40, L2, b2, hLE, hbud, hinv', hlive, hdisj,
    hfrS, -, hsb, hF', hLF'⟩ := hpost
  simp only [win, tsp] at hF'
  rw [tg] at hinv'
  obtain ⟨hw', hk, -, hkD⟩ := stepC1 hP hw hzz.2.2.1 hWK (by decide : 88 ≤ 0x70) hF' hLF' hrg' hLE hinv' hsb
  have hof : ExpHyp.NatOF R L1 L2 s'.mem zz zzc (zl + xl) p' l' c' (Zv * natVal s.mem xp xl) :=
    ⟨by rw [hval, hz.2.2.1, hxv], hnorm, hlc, hc40, hlive, hdisj⟩
  have hE' : c' = 0 → ¬ (p' = zz ∧ c' = zzc) → BitVec.ofNat 64 p' = BitVec.ofNat 64 zz ∧ c' = zzc := by
    intro c0 hn
    have := (hdisj.resolve_left hn).1; omega
  obtain ⟨p'', hp'', hof'', h00, hpp, -⟩ := res_norm hzz hof hE'
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => hw.le.mem_old hr
  have hrs : ¬ (p'' = zz ∧ c' = zzc) → ResSep T.mem s'.mem st p'' c' := by
    intro hn
    have e := hpp hn
    subst e
    exact rs_of (WC.cap0 hP hw') hfrS hn
  have hres := LN.of_res hzz hLL hw.sok (WC.cap0 hP hw) hof'' hLE hsb hrs h00
  have hj' := hj.call (S' := s') (by rw [hsp', h4, hj.esp]; exact bv_add8 (by omega) hsp64) (h14'.trans h14)
    (hfs'.trans hfs) (hx'.trans hx15) (hdf'.trans hdf) hw'
    (fun a k h1 h2 => (hk a k (by omega) h2).trans (hkw a k h1 h2))
  rw [eR] at hbud
  exact KC s' L2 b2 p'' l' c' hpc' hj' hk (e0.trans hp''.symm) e3 e1
    ⟨hres, hkD _ _ hz.1, hzlc, hkD _ _ hr, hB.lr, hkD _ _ hq, hB.lq, pw_res hof'' hz.1 hB.p1.symm,
      pw_res hof'' hr hB.p4, pw_res hof'' hq hB.p5, hB.p2, hB.p3, hB.p6⟩ hl2 hbud

end

end FvModexp.Amd64.ExpSlow
