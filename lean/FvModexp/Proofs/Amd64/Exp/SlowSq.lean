import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.Exp.SlowCP
import FvModexp.Proofs.Amd64.Exp.SlowSqG

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the loop's generic `zz = zz.sqr(stk, z)` step (agent expmc s81; twin of arm64
`Q.ExpSlow.sqrSQ`)

* `sqrCall0`: a call of the empty-tolerant `nat.sqr` (`SqrE0`) from its entry (as `LibCalls.sqrCallQ`).
* `sqrS`: at the `nat.sqr` entry `T` (`RSP = sp - 8`, `[sp - 8] = fnE + idx`), reached from a state `S0` with `JC`
  through the caller's own stores `ws` (`OwnR`, the slots `[sp + 0x1a8, sp + 0x220)` kept), with `zz` in
  `(AX, BX, CX)`, `stk` in `DI`, `z` in `(SI, R8, R9)`: the callee, then the continuation with `JC` at the return,
  the slots `[sp + 0x68, sp + 0x220)` kept and the buffers ROTATED (`z := result` of value `Zv²`, `len ≤ 2·len z`;
  `zz := old z`; `r`, `q` kept). Used by both loops (`sq1R`, `sq2R`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.Q.NatSqr (SPre SPost)

set_option maxRecDepth 20000 in
/-- a call of the empty-tolerant `nat.sqr` (`SqrE0`, window `W`, reserve level `H`) from its entry -/
theorem sqrCall0 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    (hsq : SqrE0 impl R ns W) (H : Nat) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6229984) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64)
    (hpre : (0 < xl → SPre R b H L W zp zc st xp xl xc S) ∧ (xl = 0 → SPre0 R b H L W zp zc st S))
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      SPost R b H L W zp zc st xp xl xc S s' →
      (xl = 0 → s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 1 = BitVec.ofNat 64 zc) →
      ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := LibCalls.hypSumW hap hns (by simp [numIntRegs]) (hsq H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc))
  rw [LibCalls.sqr_addr] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hz⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [LibCalls.tN bz, LibCalls.tN bzc, LibCalls.tN bst, LibCalls.tN bx, LibCalls.tN bxl, LibCalls.tN bxc]
    exact hpre
  · rw [LibCalls.tN bz, LibCalls.tN bzc, LibCalls.tN bst, LibCalls.tN bx, LibCalls.tN bxl, LibCalls.tN bxc] at hq
    rw [LibCalls.tN bxl] at hz
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq hz

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `zz = zz.sqr(stk, z)` step** (see the module doc) -/
theorem sqrS {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} (hsq : SqrE0 impl R ns W) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {S0 : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hj : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S0 L1 b1)
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hB : BB R L st zp zc S0.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc)
    (hzl : zl ≤ 2 ^ 12) (hsW : sqrW zl ≤ W) (hs16 : stLen s.mem st + 4 * (2 * zl) + 64 ≤ 2 ^ 16)
    (hH : stLen s.mem st + 4 * (2 * zl) + 64 ≤ H) (hcost : sqrCQ zl + stkR H S0.mem st ≤ b1)
    {ret0 : W64} {Q : State → Prop} {idx : Nat} (hidx : idx < 0x84d)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6229984) (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = S0.regs 14) (hfs : T.fsBase = S0.fsBase) (hx15 : T.xmm 15 = S0.xmm 15)
    (hdf : T.df = S0.df) {ws : List (Nat × Nat)} (hF : MemFrame S0.mem T.mem ws)
    (hrg : T.mem.regions = S0.mem.regions) (hws : ∀ r ∈ ws, OwnR sp K r)
    (hkw : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → T.mem.readLE a k = S0.mem.readLE a k)
    (hrd : T.mem.readLE (sp - 8) 8 = fnE + idx)
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h3 : T.regs 3 = BitVec.ofNat 64 zzl) (h1 : T.regs 1 = BitVec.ofNat 64 zzc)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 z) (h8 : T.regs 8 = BitVec.ofNat 64 zl)
    (h9 : T.regs 9 = BitVec.ofNat 64 zc')
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat), s'.rip = BitVec.ofNat 64 (fnE + idx) →
      JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s s' L2 b2 →
      (∀ a k, sp + 0x68 ≤ a → a + k ≤ sp + 0x220 → s'.mem.readLE a k = T.mem.readLE a k) →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c' →
      BB R L st zp zc s'.mem L2 p' l' c' (Zv * Zv) z zl zc' rr rl rc q ql qc → l' ≤ 2 * zl →
      b1 - (sqrCQ zl + stkR H S0.mem st) + stkR H s'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
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
  have hsk := stkS hP hw tsp tg tfs rfl (W := W) (A := 64) hWK (by decide)
  have hpre : (0 < zl → SPre R b1 H L1 W zz zzc st z zl zc' T) ∧ (zl = 0 → SPre0 R b1 H L1 W zz zzc st T) := by
    refine ⟨fun hl0 => sqrPreS hP hw hWK tsp tg tfs rfl hzz hz hB.p1 hl0 hzl hsW hs16 hH (by rw [eR]; exact hcost),
      fun hl0 => ?_⟩
    subst hl0
    exact ⟨CallW.callEnv_of (hw.cenv hP) tsp tg tfs rfl hWK (by decide) (by omega), hsW, hzz.1, hzz.2.1,
      hsk.2.1, hsk.2.2.1, by rw [eR]; exact hcost, by rw [tg]; exact hw.inv⟩
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  have bst : st < 2 ^ 64 := by have := hw.sok.2.2.2.1; omega
  have hzlc := hB.bz.2.1
  refine sqrCall0 hap hns hsq H (b := b1) (L := L1) (ra_slow hap hnf idx hidx) hpc (by rw [tsp]; exact hrd)
    h0 h3 h1 h7 h6 h8 h9 (hx15.trans hj.ex15) (hdf.trans hj.edf) bzz bzzc bst bz (by omega) bzc hpre ?_
  intro s' hpc' hsp' _ h14' hx' hrg' hpost hE
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, hval, hnorm, hlc, hl2, hc40, L2, b2, hLE, hbud, hinv', hlive, hdisj,
    hfrS, -, hsb, hF', hLF'⟩ := hpost
  simp only [win, tsp] at hF'
  rw [tg] at hinv'
  obtain ⟨hw', hk, -, hkD⟩ := stepC1 hP hw hzz.2.2.1 hWK (by decide : 64 ≤ 0x70) hF' hLF' hrg' hLE hinv' hsb
  have hof : ExpHyp.NatOF R L1 L2 s'.mem zz zzc (2 * zl) p' l' c' (Zv * Zv) :=
    ⟨by rw [hval, hz.2.2.1], hnorm, hlc, hc40, hlive, hdisj⟩
  have hE' : c' = 0 → ¬ (p' = zz ∧ c' = zzc) → BitVec.ofNat 64 p' = BitVec.ofNat 64 zz ∧ c' = zzc := by
    intro c0 hn
    have hz0 : zl = 0 := by have := (hdisj.resolve_left hn).1; omega
    obtain ⟨r0, r1⟩ := hE hz0
    exact ⟨e0.symm.trans r0, ofNat_inj (by omega) bzzc (e1.symm.trans r1)⟩
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
