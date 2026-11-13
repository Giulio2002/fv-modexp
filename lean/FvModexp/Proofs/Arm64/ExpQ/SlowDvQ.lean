import FvModexp.Proofs.Arm64.ExpQ.SlowSqQ
import FvModexp.Proofs.Arm64.Exp.SlowDv

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowDv.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): the loop's generic `zz, r = zz.div(stk, r, z, m)` step (agent expmc)

`divS`: at the `nat.div` entry (return `fn + 4 idx`) with `zz` in `X0..X2`, `r` in `X4..X6`, `z` in `X7..X9` and the
INPUT `m` in `X10..X12`: the callee (`DivHypLG`) and the continuation with `JC` at the return, the slots kept, the
quotient in `X0..X2`, the remainder in `X3..X5`, and the buffers ROTATED as nat.go:760 (`zz, r, q, z = q, z, zz, r`):
`z := remainder` (value `Zv % M`, `len ≤ len m`), `zz := old q`, `r := old z`, `q := quotient`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp

/-- `DivPreG` at a constant cost gives `DivPreGQ` (the level twin added) -/
theorem preGQ_of {R : RtInv} {b H c : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st z2 z2l z2c u ul v vl : Nat}
    {s : State} (h : DivPreG R b (fun _ _ _ => c) L stk above zp zl zc st z2 z2l z2c u ul v vl s)
    (hH : stLen s.mem st + 16 * ul + 64 ≤ H) : DivPreGQ R b H c L stk above zp zl zc st z2 z2l z2c u ul v vl s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, hc, hinv⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, ⟨hH, hc⟩, hinv⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem divSQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {dvC : Nat → Nat → Nat} {H : Nat} (hdv : DivHypLGQ impl R ns stkS aboveS dvC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {T : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T M L1 b1)
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hB : BB R L st zp zc M L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc)
    (hM : 0 < natVal s.mem mp ml) (hzl : zl ≤ 2 ^ 9) (hs16 : stLen s.mem st + 16 * zl + 64 ≤ 2 ^ 16)
    (hH : stLen s.mem st + 16 * zl + 64 ≤ H) (hcost : dvC zl ml + stkR H M st ≤ b1)
    {ret0 : BitVec 64} {Q : State → Prop} {idx : Nat} (hidx : idx < 363)
    (hpc : T.pc = BitVec.ofNat 64 1806848) (h30 : T.regs 30 = BitVec.ofNat 64 (1788352 + 4 * idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h1 : T.regs 1 = BitVec.ofNat 64 zzl) (h2 : T.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 r) (h5 : T.regs 5 = BitVec.ofNat 64 rl)
    (h6 : T.regs 6 = BitVec.ofNat 64 rc) (h7 : T.regs 7 = BitVec.ofNat 64 z) (h8 : T.regs 8 = BitVec.ofNat 64 zl)
    (h9 : T.regs 9 = BitVec.ofNat 64 zc') (h10 : T.regs 10 = BitVec.ofNat 64 mp)
    (h11 : T.regs 11 = BitVec.ofNat 64 ml) (h12 : T.regs 12 = BitVec.ofNat 64 mc)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 pq lq cq pr lr cr : Nat),
      s'.pc = BitVec.ofNat 64 (1788352 + 4 * idx) →
      JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret s' s'.mem L2 b2 →
      (∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 120 ≤ a ∧ a + k ≤ sp + 544) → s'.mem.readLE a k = M.readLE a k) →
      s'.regs 0 = BitVec.ofNat 64 pq → s'.regs 1 = BitVec.ofNat 64 lq → s'.regs 2 = BitVec.ofNat 64 cq →
      s'.regs 3 = BitVec.ofNat 64 pr → s'.regs 4 = BitVec.ofNat 64 lr → s'.regs 5 = BitVec.ofNat 64 cr →
      BB R L st zp zc s'.mem L2 pr lr cr (Zv % natVal s.mem mp ml) q ql qc z zl zc' pq lq cq → lr ≤ ml →
      b1 - (dvC zl ml + stkR H M st) + stkR H s'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hw := hj.wc
  have hsN : T.sp.toNat = sp := by rw [hj.esp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (T.regs 28).toNat = g := by rw [hj.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hlen : stLen T.mem st = stLen s.mem st := by rw [hj.hm]; exact hw.len
  have hpre := divPreG hP hw hkS haS hj.esp hj.e28 hj.hm hB.bzz hB.lzz hB.br hB.lr hB.p4 hB.bz hB.p1 hB.p2 hzl hs16
    (dvC := fun _ _ _ => dvC zl ml + stkR H T.mem st) (by rw [hj.hm]; exact hcost)
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨br, brc⟩ := hB.br.lt64
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  have bst : st < 2 ^ 64 := by have := hP.stk0.2.2.2.1; omega
  have hzlc := hB.bz.2.1
  have hzzl := hB.lzz
  have hrl := hB.lr
  obtain ⟨hom, -, hm48, hmn, hzm, -, -, hmp, hmc, -⟩ :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  refine divCallGQ hap hns hdv (H := H) (b := b1) (L := L1) (ra_slow hap hnf idx hidx) (by rw [hpc, div_a]) h30
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 bzz (by omega) bzzc bst br (by omega) brc bz (by omega) bzc hmp
    (by omega) hmc (by omega) (preGQ_of hpre (by omega)) fun s' hpc' hsp' h28' h29' h18' hrg hpost => ?_
  obtain ⟨pq, lq, cq, pr, lr, cr, e0, e1, e2, e3, e4, e5, L2, b2, hofQ, hofR, ⟨hLE, hbud', hinv'⟩, hsb, hnewR, hF',
    hLF', hqr, hnewQ⟩ := hpost
  simp only [winA, hsN, ExpHyp.stWs, hj.hm] at hF' hLF' hsb hnewR hnewQ hbud' hofQ hofR hrg
  rw [hgN] at hinv'
  obtain ⟨hw', hk, -, hkD⟩ := stepC2 hP hw hB.bzz.2.2.1 hB.br.2.2.1 hkS haS hF' hLF' hrg hLE hinv' hsb
  have hcq := hofQ.2.2.2.1
  have hcr := hofR.2.2.2.1
  obtain ⟨pq', hpq', hofQ', hq0, hqq, hqp⟩ := res_norm hB.bzz hofQ
    (fun c0 hn => by have := (hofQ.2.2.2.2.2.resolve_left hn).1; omega)
  obtain ⟨pr', hpr', hofR', hr0, hrr, hrp⟩ := res_norm hB.br hofR
    (fun c0 hn => by have := (hofR.2.2.2.2.2.resolve_left hn).1; omega)
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => hw.le.mem_old hr
  have hrsQ : ¬ (pq' = zz ∧ cq = zzc) → ResSep M s'.mem st pq' cq := by
    intro hn
    have e := hqq hn
    subst e
    exact rs_of (WC.cap0 hP hw') hnewQ hn
  have hrsR : ¬ (pr' = r ∧ cr = rc) → ResSep M s'.mem st pr' cr := by
    intro hn
    have e := hrr hn
    subst e
    exact rs_of (WC.cap0 hP hw') hnewR hn
  have hresQ := LN.of_res hB.bzz hLL hw.sok (WC.cap0 hP hw) hofQ' hLE hsb hrsQ hq0
  have hresR := LN.of_res hB.br hLL hw.sok (WC.cap0 hP hw) hofR' hLE hsb hrsR hr0
  have hmv := (inVal hP hw hom hzm hmn).1
  have hval : natVal s'.mem pr' lr = Zv % natVal s.mem mp ml := by rw [hofR'.1, hB.bz.2.2.1, hmv]
  have hlr : lr ≤ ml := by
    refine len_bd hofR'.2.1 ?_
    rw [hval]
    have := natVal_lt s.mem mp ml
    have := Nat.mod_lt Zv hM
    omega
  have hp3 : Pw pr' cr pq' cq := by
    intro c1 c2
    rw [hrp c1, hqp c2]
    exact (hqr c2 c1).symm
  exact KC s' L2 b2 pq' lq cq pr' lr cr hpc' ⟨hw', rfl, hsp'.trans hj.esp, h28'.trans hj.e28, h29'.trans hj.e29,
    h18'.trans hj.e18, hj.sf.keep fun a k ha => hk a k (by omega)⟩ hk (e0.trans hpq'.symm) e1 e2 (e3.trans hpr'.symm) e4 e5
    ⟨⟨hresR.1, hresR.2.1, hval, hresR.2.2.2⟩, hkD _ _ hB.bq, hB.lq, hkD _ _ hB.bz.1, hzlc, hresQ.1, hresQ.2.1,
      pw_res hofR' hB.bq hB.p6, pw_res hofR' hB.bz.1 hB.p2.symm, hp3, hB.p3.symm, (pw_res hofQ' hB.bq hB.p5).symm,
      (pw_res hofQ' hB.bz.1 hB.p1.symm).symm⟩ hlr hbud'

end

end FvModexp.Arm64.Q.ExpSlow
