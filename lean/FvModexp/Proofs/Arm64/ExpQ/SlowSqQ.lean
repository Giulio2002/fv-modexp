import FvModexp.Proofs.Arm64.ExpQ.SlowCallsQ
import FvModexp.Proofs.Arm64.Exp.SlowSq
import FvModexp.Proofs.Arm64.Exp.SlowJF

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowSq.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): the loop's generic `zz = zz.sqr(stk, z)` step (agent expmc)

`sqrS`: at the `nat.sqr` entry (return `fn + 4 idx`) with `zz` in `X0..X2` and `z` in `X4..X6`: the callee
(`SqrHypG`) and the continuation with the context `JC` at the return, the slots kept, and the buffers ROTATED
(`z := result` of value `Zv²`, `len ≤ 2·len z`; `zz := old z`; `r`, `q` kept).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

/-- the callees' level twins from `needH` (`zl ≤ M` at `sqr`, `≤ 2M` at `mul` with `len x ≤ M`, `≤ 3M` at `div`) -/
theorem lvl_sq {l M zl H : Nat} (hz : zl ≤ M) (h : l + 48 * M + 64 ≤ H) : l + 4 * (2 * zl) + 64 ≤ H := by omega
theorem lvl_mu {l M zl xl H : Nat} (hz : zl ≤ 2 * M) (hx : xl ≤ M) (h : l + 48 * M + 64 ≤ H) :
    l + 4 * (zl + xl) + 64 ≤ H := by omega
theorem lvl_dv {l M zl H : Nat} (hz : zl ≤ 3 * M) (h : l + 48 * M + 64 ≤ H) : l + 16 * zl + 64 ≤ H := by omega

/-- the stack capacity is kept by slot stores -/
theorem capW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory} {ws : List (Nat × Nat)}
    (hws : InSlots sp ws) (hF : MemFrame M M' ws) : stCap M' st = stCap M st := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  exact hF.readLE _ _ (out_slots hws (by omega))

/-- the reserve is kept by slot stores -/
theorem stkRW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory} {ws : List (Nat × Nat)}
    (hws : InSlots sp ws) (hF : MemFrame M M' ws) (H : Nat) : stkR H M' st = stkR H M st :=
  stkR_congr (capW hP hws hF)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sqrSQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {sqC : Nat → Nat} {H : Nat} (hsq : SqrHypGQ impl R ns stkS aboveS sqC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {T : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T M L1 b1)
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hB : BB R L st zp zc M L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc)
    (hzl : zl ≤ 2 ^ 12) (hs16 : stLen s.mem st + 4 * (2 * zl) + 64 ≤ 2 ^ 16)
    (hH : stLen s.mem st + 4 * (2 * zl) + 64 ≤ H) (hcost : sqC zl + stkR H M st ≤ b1)
    {ret0 : BitVec 64} {Q : State → Prop} {idx : Nat} (hidx : idx < 363)
    (hpc : T.pc = BitVec.ofNat 64 1815584) (h30 : T.regs 30 = BitVec.ofNat 64 (1788352 + 4 * idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h1 : T.regs 1 = BitVec.ofNat 64 zzl) (h2 : T.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 z) (h5 : T.regs 5 = BitVec.ofNat 64 zl)
    (h6 : T.regs 6 = BitVec.ofNat 64 zc')
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat), s'.pc = BitVec.ofNat 64 (1788352 + 4 * idx) →
      JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret s' s'.mem L2 b2 →
      (∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 120 ≤ a ∧ a + k ≤ sp + 544) → s'.mem.readLE a k = M.readLE a k) →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 1 = BitVec.ofNat 64 l' → s'.regs 2 = BitVec.ofNat 64 c' →
      BB R L st zp zc s'.mem L2 p' l' c' (Zv * Zv) z zl zc' r rl rc q ql qc → l' ≤ 2 * zl →
      b1 - (sqC zl + stkR H M st) + stkR H s'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hw := hj.wc
  have hsN : T.sp.toNat = sp := by rw [hj.esp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (T.regs 28).toNat = g := by rw [hj.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hlen : stLen T.mem st = stLen s.mem st := by rw [hj.hm]; exact hw.len
  have hpre := sqrPreG hP hw hkS haS hj.esp hj.e28 hj.hm hB.bzz hB.lzz hB.bz hB.p1 hzl hs16
    (c := sqC zl + stkR H T.mem st) (by rw [hj.hm]; exact hcost)
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  have bst : st < 2 ^ 64 := by have := hP.stk0.2.2.2.1; omega
  have hzlc := hB.bz.2.1
  have hzzl := hB.lzz
  refine sqrCallGQ hap hns hsq (H := H) (b := b1) (L := L1) (ra_slow hap hnf idx hidx) (by rw [hpc, sqr_a]) h30
    h0 h1 h2 h3 h4 h5 h6 bzz (by omega) bzzc bst bz (by omega) bzc (by omega) ⟨hpre.1, hpre.2.1, hpre.2.2, by omega⟩
    fun s' hpc' hsp' h28' h29' h18' hrg hpost hE => ?_
  obtain ⟨p', l', c', e0, e1, e2, L2, b2, hof, ⟨hLE, hbud', hinv'⟩, hsb, hnew, hF', hLF'⟩ := hpost
  simp only [winA, hsN, ExpHyp.stWs, hj.hm] at hF' hLF' hsb hnew hbud' hof hrg
  rw [hgN] at hinv'
  obtain ⟨hw', hk, -, hkD⟩ := stepC1 hP hw hB.bzz.2.2.1 hkS haS hF' hLF' hrg hLE hinv' hsb
  have hc40 := hof.2.2.2.1
  have hE' : c' = 0 → ¬ (p' = zz ∧ c' = zzc) → BitVec.ofNat 64 p' = BitVec.ofNat 64 zz ∧ c' = zzc := by
    intro c0 hn
    have hz0 : zl = 0 := by have := (hof.2.2.2.2.2.resolve_left hn).1; omega
    obtain ⟨r0, r2⟩ := hE hz0
    exact ⟨e0.symm.trans r0, ofNat_inj (by omega) bzzc (e2.symm.trans r2)⟩
  obtain ⟨p'', hp'', hof'', h00, hpp, -⟩ := res_norm hB.bzz hof hE'
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => hw.le.mem_old hr
  have hrs : ¬ (p'' = zz ∧ c' = zzc) → ResSep M s'.mem st p'' c' := by
    intro hn
    have e := hpp hn
    subst e
    exact rs_of (WC.cap0 hP hw') hnew hn
  have hres := LN.of_res hB.bzz hLL hw.sok (WC.cap0 hP hw) hof'' hLE hsb hrs h00
  have hval : natVal s'.mem p'' l' = Zv * Zv := by rw [hof''.1, hB.bz.2.2.1]
  have hl2 : l' ≤ 2 * zl := by
    refine len_bd hof''.2.1 ?_
    rw [hval, ← hB.bz.2.2.1]
    have := natVal_lt M z zl
    calc natVal M z zl * natVal M z zl < 2 ^ (64 * zl) * 2 ^ (64 * zl) := Nat.mul_lt_mul'' this this
      _ = 2 ^ (64 * (2 * zl)) := by rw [← Nat.pow_add]; congr 1; omega
  refine KC s' L2 b2 p'' l' c' hpc' ⟨hw', rfl, hsp'.trans hj.esp, h28'.trans hj.e28, h29'.trans hj.e29,
    h18'.trans hj.e18, hj.sf.keep fun a k ha => hk a k (by omega)⟩ hk (e0.trans hp''.symm) e1 e2
    ⟨⟨hres.1, hres.2.1, hval, hres.2.2.2⟩, hkD _ _ hB.bz.1, hzlc, hkD _ _ hB.br, hB.lr, hkD _ _ hB.bq, hB.lq,
      pw_res hof'' hB.bz.1 hB.p1.symm, pw_res hof'' hB.br hB.p4, pw_res hof'' hB.bq hB.p5, hB.p2, hB.p3, hB.p6⟩
    hl2 hbud'

end

end FvModexp.Arm64.Q.ExpSlow
