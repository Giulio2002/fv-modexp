import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.Exp.SlowDvP

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the loop's generic `zz, r = zz.div(stk, r, z, m)` step (agent expmc s81; twin of arm64
`Q.ExpSlow.divSQ`)

* `divCallG`: a call of `nat.div` (`DivHypLGQ`, entry `0x5edf20`) from its entry.
* `divS`: at the `nat.div` entry `T` (`RSP = sp - 8`, `[sp - 8] = fnE + idx`), reached from `S0` with `JC` through the
  caller's own stores; `zz` in `(AX, BX, CX)`, `stk` in `DI`, `r` in `(SI, R8, R9)`, `u = z` at `sp + 0/8/0x10`, `v = m`
  at `sp + 0x18/0x20/0x28`: the continuation gets `JC` at the return, the slots `[sp + 0x68, sp + 0x220)` kept, the
  quotient in `(AX, BX, CX)`, the remainder in `(DI, SI, R8)`, and the buffers ROTATED as nat.go:760
  (`zz, r, q, z = q, z, zz, r`): `z := remainder` (value `Zv % M`, `len ≤ len m`), `zz := old q`, `r := old z`,
  `q := quotient`. Used by both loops (`dv1R`, `dv2R`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem div_addr : segAddr Extracted.program ExpHyp.fnDiv = 6217504 := by decide

theorem len_bdS {M : Memory} {p l n : Nat} (hN : NatNorm M p l) (hv : natVal M p l < 2 ^ (64 * n)) : l ≤ n := by
  rw [← SubMod2N.norm_nlen M p l hN]
  exact Exp.nlen_le_iff.2 (by simp only [Exp.B]; rw [← Nat.pow_mul]; exact hv)

set_option maxRecDepth 20000 in
/-- a call of `nat.div` (`DivHypLGQ`, window `W`, above `0x70`, reserve level `H`) from its entry -/
theorem divCallG {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    {dvC : Nat → Nat → Nat} (hdv : DivHypLGQ impl R ns W 0x70 dvC) (H : Nat) {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6217504) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 z2) (h8 : S.regs 8 = BitVec.ofNat 64 z2l)
    (h9 : S.regs 9 = BitVec.ofNat 64 z2c) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (b2 : z2 < 2 ^ 64)
    (b2l : z2l < 2 ^ 64) (b2c : z2c < 2 ^ 64)
    (hpre : DivPreGQ R b H (dvC ul vl + stkR H S.mem st) L W 0x70 zp zl zc st z2 z2l z2c u ul uc v vl vc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      DivPostLGQ R b (dvC ul vl + stkR H S.mem st) (stkR H s'.mem st) L W 0x70 zp zc st z2 z2c u ul v vl S s' →
      ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := LibCalls.hypSumW hap hns (by simp [numIntRegs]) (hdv H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 z2) (BitVec.ofNat 64 z2l) (BitVec.ofNat 64 z2c)
    u ul uc v vl vc)
  rw [div_addr] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · simp only [LibCalls.tN bz, LibCalls.tN bzl, LibCalls.tN bzc, LibCalls.tN bst, LibCalls.tN b2, LibCalls.tN b2l,
      LibCalls.tN b2c]
    exact hpre
  · simp only [LibCalls.tN bz, LibCalls.tN bzc, LibCalls.tN bst, LibCalls.tN b2, LibCalls.tN b2c] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `zz, r = zz.div(stk, r, z, m)` step** (see the module doc) -/
theorem divS {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} {dvC : Nat → Nat → Nat} (hdv : DivHypLGQ impl R ns W 0x70 dvC) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {S0 : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hj : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S0 L1 b1)
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hB : BB R L st zp zc S0.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc)
    (hM : 0 < natVal s.mem mp ml)
    (hzl : zl ≤ 2 ^ 9) (hs16 : stLen s.mem st + 16 * zl + 64 ≤ 2 ^ 16)
    (hH : stLen s.mem st + 16 * zl + 64 ≤ H) (hcost : dvC zl ml + stkR H S0.mem st ≤ b1)
    {ret0 : W64} {Q : State → Prop} {idx : Nat} (hidx : idx < 0x84d)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6217504) (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = S0.regs 14) (hfs : T.fsBase = S0.fsBase) (hx15 : T.xmm 15 = S0.xmm 15)
    (hdf : T.df = S0.df) {ws : List (Nat × Nat)} (hF : MemFrame S0.mem T.mem ws)
    (hrg : T.mem.regions = S0.mem.regions) (hws : ∀ r ∈ ws, OwnR sp K r)
    (hkw : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → T.mem.readLE a k = S0.mem.readLE a k)
    (hrd : T.mem.readLE (sp - 8) 8 = fnE + idx)
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h3 : T.regs 3 = BitVec.ofNat 64 zzl) (h1 : T.regs 1 = BitVec.ofNat 64 zzc)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 rr) (h8 : T.regs 8 = BitVec.ofNat 64 rl)
    (h9 : T.regs 9 = BitVec.ofNat 64 rc) (r1 : T.mem.readLE sp 8 = z) (r2 : T.mem.readLE (sp + 8) 8 = zl)
    (r3 : T.mem.readLE (sp + 16) 8 = zc') (r4 : T.mem.readLE (sp + 24) 8 = mp) (r5 : T.mem.readLE (sp + 32) 8 = ml)
    (r6 : T.mem.readLE (sp + 40) 8 = mc)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 pq lq cq pr lr cr : Nat), s'.rip = BitVec.ofNat 64 (fnE + idx) →
      JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s s' L2 b2 →
      (∀ a k, sp + 0x68 ≤ a → a + k ≤ sp + 0x220 → s'.mem.readLE a k = T.mem.readLE a k) →
      s'.regs 0 = BitVec.ofNat 64 pq → s'.regs 3 = BitVec.ofNat 64 lq → s'.regs 1 = BitVec.ofNat 64 cq →
      s'.regs 7 = BitVec.ofNat 64 pr → s'.regs 6 = BitVec.ofNat 64 lr → s'.regs 8 = BitVec.ofNat 64 cr →
      BB R L st zp zc s'.mem L2 pr lr cr (Zv % natVal s.mem mp ml) q ql qc z zl zc' pq lq cq → lr ≤ ml →
      b1 - (dvC zl ml + stkR H S0.mem st) + stkR H s'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
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
  have hpre := divPreS hP hw hWK tsp tg tfs rfl hzz hB.lzz hr hB.lr hz hB.p4 hB.p1 hB.p2 hzl hs16 hH
    (c := dvC zl ml + stkR H T.mem st) (by rw [eR]; exact hcost) r1 r2 r3 r4 r5 r6
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  have bst : st < 2 ^ 64 := by have := hw.sok.2.2.2.1; omega
  have hzlc := hB.bz.2.1
  obtain ⟨br, brc⟩ := hB.br.lt64
  have hzzl := hB.lzz
  have hrl := hB.lr
  refine divCallG hap hns hdv H (b := b1) (L := L1) (ra_slow hap hnf idx hidx) hpc (by rw [tsp]; exact hrd)
    h0 h3 h1 h7 h6 h8 h9 (hx15.trans hj.ex15) (hdf.trans hj.edf) bzz (by omega) bzzc bst br (by omega) brc hpre ?_
  intro s' hpc' hsp' _ h14' hx' hrg' hpost
  obtain ⟨hfs', hdf', pq, lq, cq, pr, lr, cr, e0, e3, e1, e7, e6, e8, L2, b2, hofQ, hofR, ⟨hLE, hbud, hinv'⟩, hsb,
    hnewR, hF', hLF', hqr, hnewQ⟩ := hpost
  simp only [win, tsp, ExpHyp.stWs] at hF' hLF'
  rw [tg] at hinv'
  obtain ⟨hw', hk, -, hkD⟩ := stepC2 hP hw hzz.2.2.1 hr.2.2.1 hWK (Nat.le_refl _) hF' hLF' hrg' hLE hinv' hsb
  obtain ⟨pq', hpq', hofQ', hq0, hqq, hqp⟩ := res_norm hzz hofQ
    (fun c0 hn => by have := (hofQ.2.2.2.2.2.resolve_left hn).1; omega)
  obtain ⟨pr', hpr', hofR', hr0, hrr, hrp⟩ := res_norm hr hofR
    (fun c0 hn => by have := (hofR.2.2.2.2.2.resolve_left hn).1; omega)
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => hw.le.mem_old hr
  have hrsQ : ¬ (pq' = zz ∧ cq = zzc) → ResSep T.mem s'.mem st pq' cq := by
    intro hn
    have e := hqq hn
    subst e
    exact rs_of (WC.cap0 hP hw') hnewQ hn
  have hrsR : ¬ (pr' = rr ∧ cr = rc) → ResSep T.mem s'.mem st pr' cr := by
    intro hn
    have e := hrr hn
    subst e
    exact rs_of (WC.cap0 hP hw') hnewR hn
  have hresQ := LN.of_res hzz hLL hw.sok (WC.cap0 hP hw) hofQ' hLE hsb hrsQ hq0
  have hresR := LN.of_res hr hLL hw.sok (WC.cap0 hP hw) hofR' hLE hsb hrsR hr0
  have hmP := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hmO, hmacc, hm48, hmN, hzm, -⟩ := hmP
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hmv := (obj_at hP hw hmO hmacc hm48 hmN (Nat.le_trans hml (by decide)) hzm tsp rfl (stk := W) (above := 0x70)
    hWK (by decide)).2.2.2
  have hval : natVal s'.mem pr' lr = Zv % natVal s.mem mp ml := by rw [hofR'.1, hz.2.2.1, hmv]
  have hlr : lr ≤ ml := by
    refine len_bdS hofR'.2.1 ?_
    rw [hval]
    have := natVal_lt s.mem mp ml
    have := Nat.mod_lt Zv hM
    omega
  have hp3 : Pw pr' cr pq' cq := by
    intro c1 c2
    rw [hrp c1, hqp c2]
    exact (hqr c2 c1).symm
  have hj' := hj.call (S' := s') (by rw [hsp', h4, hj.esp]; exact bv_add8 (by omega) hsp64) (h14'.trans h14)
    (hfs'.trans hfs) (hx'.trans hx15) (hdf'.trans hdf) hw'
    (fun a k h1 h2 => (hk a k (by omega) h2).trans (hkw a k h1 h2))
  rw [eR] at hbud
  exact KC s' L2 b2 pq' lq cq pr' lr cr hpc' hj' hk (e0.trans hpq'.symm) e3 e1 (e7.trans hpr'.symm) e6 e8
    ⟨⟨hresR.1, hresR.2.1, hval, hresR.2.2.2⟩, hkD _ _ hq, hB.lq, hkD _ _ hz.1, hzlc, hresQ.1, hresQ.2.1,
      pw_res hofR' hq hB.p6, pw_res hofR' hz.1 hB.p2.symm, hp3, hB.p3.symm, (pw_res hofQ' hq hB.p5).symm,
      (pw_res hofQ' hz.1 hB.p1.symm).symm⟩ hlr hbud

end

end FvModexp.Amd64.ExpSlow
