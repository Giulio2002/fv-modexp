import FvModexp.Proofs.Amd64.Exp.P2W4
import FvModexp.Proofs.Amd64.Exp.P2QG

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the summary in the `NHyp.CPre` form (agent divmc s77, port of divmc s74; amd64 twin of agent
infra's `Arm64.P2W4EC` + `Arm64.P2W4C`, bridge adapted from agent asm's amd64 `ExpEven.epre_of`)

`PreC` is the exported-shape precondition (`NHyp.CPre` at `RSP`, window `[RSP - stk, RSP + 0x60)`, inputs `x`, `y`, need
`2^13`, `x` odd, `y > 0`, `2 ≤ logM ≤ 2^13`, `0 < st`, `natOne`) used by the `expNNPowerOfTwo` dispatch; `y` is the stack
argument (`NHyp.StkArg s 0`). `epre_of` gives `EPre` with frame `sp = RSP - 0x2f8`, `K = stk - 0x300` (so
`[sp - 0x8 - K, sp + 0x358)` is the same window), the caller's `RBP` as `bp`, the return-address word as `r` (bounded by
`2^47`: the `RetAddr` user-space bound) and the effective budget `b - stkR (HW ℓ₀ logM)`.
`fullC`: `full` as a `Summary` on `LibW` with `PreC ∧ EX` (`EX` = the table call's facts: `x` apart from `gA`, the
`natOne` word apart from `gA`, `adx` readable — the first three conjuncts of `NHyp.XGc`) and the post
`NHyp.CPostR … stk 0x60 …` at budget `costB` (+ the ABI facts `RSP + 8`, `RBP`, `R14`, `X15`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the bridged budget for callers: the Q-form cost plus ONE stack reserve `stkRes (HW ℓ0 lm)` for the whole call -/
@[reducible] def costB (l0 yl lm : Nat) : Nat := cost yl lm + stkRes (HW l0 lm)

/-- the `CPre`-form precondition (see the module doc) -/
@[reducible] def PreC (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (cst : Nat)
    (zp zl zc st xp xl yp yl lm : Nat) (s : State) : Prop :=
  NHyp.CPre R b L stk 0x60 zp zl zc st [(xp, xl), (yp, yl)] (2 ^ 13) cst s ∧
    natVal s.mem xp xl % 2 = 1 ∧ 0 < natVal s.mem yp yl ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk 0x60 ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      NHyp.StkApart s.mem st op 8

theorem ap_wC {a k SP stk : Nat} (h : Outside a k [(SP - stk, SP + 0x60)]) (h1 : 0x300 ≤ stk) (h2 : stk ≤ SP) :
    Apart a k (SP - 0x2f8 - 8 - (stk - 0x300)) (stk - 0x300 + 0x360) := by
  simp only [outside_cons, outside_nil, and_true] at h; unfold Apart; omega

theorem win_eqC {SP stk : Nat} (h1 : 0x300 ≤ stk) (h2 : stk ≤ SP) :
    [(SP - stk, SP + 0x60)] = [(SP - 0x2f8 - 8 - (stk - 0x300), SP - 0x2f8 + 0x358)] := by
  rw [show SP - 0x2f8 - 8 - (stk - 0x300) = SP - stk by omega, show SP - 0x2f8 + 0x358 = SP + 0x60 by omega]

/-- an input operand of the exported pre as an entry object -/
theorem oe_ofC {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk st p n SP : Nat} (hS : (s.regs 4).toNat = SP)
    (h1 : 0x300 ≤ stk) (h2 : stk ≤ SP)
    (h : EvenHyp.RdIn R L s stk 0x60 p n) (hst : Apart p (8 * n) st 24)
    (hf : Apart p (8 * n) (NHyp.freeOf s.mem st).1 (NHyp.freeOf s.mem st).2) :
    OE R L (SP - 0x2f8) (stk - 0x300) st s.mem p (8 * n) := by
  obtain ⟨-, -, -, hH, hw⟩ := h
  simp only [win, hS] at hw
  exact ⟨hH, ap_wC hw h1 h2, hst, hf⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the internal entry facts** -/
theorem epre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk cst : Nat}
    {zp zl zc st xp xl xc yp yl yc lm : Nat} {s : State}
    (hP : PreC R b L stk cst zp zl zc st xp xl yp yl lm s)
    (hk1 : 41512 + 0x300 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x300) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hy : NHyp.StkArg s 0 yp yl yc)
    (hr47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hr : stkR (HW (stLen s.mem st) lm) s.mem st ≤ b) :
    EPre R (b - stkR (HW (stLen s.mem st) lm) s.mem st) L (stk - 0x300) (s.regs 14).toNat s.fsBase.toNat
      ((s.regs 4).toNat - 0x2f8) st (s.regs 5).toNat (s.mem.readLE (s.regs 4).toNat 8) zp zc xp xl xc yp yl lm s := by
  obtain ⟨⟨hce, hsv, hgl, hro, hwT, hzl, hwo, hins, hsok, hstw, hstg, harr, hcap0, hneed, hwba, hstwb, hstf,
    ⟨hstfs, hfrfs⟩, hzs, hstgA, hfgA, hcst, hadx, harrfs, hinv⟩, hX, hY, hlm2, hlm, hst0, op, hone, hsa⟩ := hP
  obtain ⟨hgd, ⟨hle, h48, hacc⟩, hal, hdl, hwrt, hgw, hgrt, hLs, -, ⟨htb, htr, htg⟩, htout, htap⟩ := hce
  obtain ⟨gnw, grd, gbl⟩ := hgd
  simp only [regSP, regG, stackguard0, stackguard0Offset] at gnw grd gbl hle h48 hacc htg
  obtain ⟨hy1, hy2, hy3⟩ := hy
  generalize hS : (s.regs 4).toNat = SP at *
  generalize hG : (s.regs 14).toNat = g at *
  generalize hF : s.fsBase.toNat = fs at *
  have hspE : s.regs 4 = BitVec.ofNat 64 (SP - 0x2f8 + 0x2f8) := by
    apply BitVec.eq_of_toNat_eq; rw [hS, BitVec.toNat_ofNat]; omega
  have hgE : s.regs 14 = BitVec.ofNat 64 g := by
    apply BitVec.eq_of_toNat_eq; rw [hG, BitVec.toNat_ofNat]; omega
  have ew := win_eqC (SP := SP) (by omega : 0x300 ≤ stk) hle
  have hyi := hins yp yl (by simp)
  have hxi := hins xp xl (by simp)
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  obtain ⟨hwo1, hwo2, hwo3⟩ := hwo
  simp only [win, hS] at hstw harr hwo3 hgl hone hLs
  rw [ew] at hgl hLs hone
  have hK : stk - 0x300 ≤ SP - 0x2f8 - 8 := by omega
  have hww : SP - 0x2f8 - 8 - (stk - 0x300) = SP - stk := by omega
  have hwk : stk - 0x300 + 0x360 = stk + 0x60 := by omega
  refine ⟨⟨hspE, hgE, hF, hx15, hdf, by omega, by omega, by omega, ⟨by omega, hK, by omega, ?_, by omega, grd,
      by omega, ?_, ?_, hgrt, ?_, hdl, hro, by omega, by omega, htr, htg, htout, ?_⟩, hsv⟩,
    hgl, hro, hwT, hlm2, hlm,
    oe_ofC hS (by omega) hle hyi.1 hyi.2.2.2.1 hyi.2.2.2.2.1, hyi.1.2.1, hyi.1.2.2.1, hyi.2.2.1, hyl0,
    by have := hyi.2.1; omega,
    oe_ofC hS (by omega) hle hxi.1 hxi.2.2.2.1 hxi.2.2.2.2.1, hxi.1.2.1, hxi.1.2.2.1, hxi.2.2.1,
    by have := hxi.2.1; omega, by have := hxi.1.2.2.1; omega, hxc, hzp, hwo1, fun hz => ?_, ?_, hsok,
    ap_wC hstw (by omega) hle, hstg, hstfs, fun hc => ⟨ap_wC (harr hc).1 (by omega) hle, (harr hc).2, harrfs hc⟩,
    hwba, hstwb, hstf, by omega, hneed, rfl, by rw [show SP - 0x2f8 + 0x2f8 = SP by omega], hr47, ?_, ?_,
    ⟨op, hone, hsa⟩, P2Q.inv_eff hinv hr⟩
  · rw [hww, hwk]; exact hacc
  · rw [hww, hwk]; exact hwrt
  · unfold Apart at hgw ⊢; omega
  · rw [show SP - 0x2f8 - 8 + 0x360 = SP - 0x2f8 + 0x358 by omega]; exact hLs
  · unfold Apart at htap ⊢; omega
  · obtain ⟨n1, n2, n3, n4⟩ := hwo2 hz
    obtain ⟨o1, o2, o3⟩ := hwo3 hz
    obtain ⟨z1, z2, z3⟩ := hzs hz
    have a1 : Apart (g + 16) 8 zp (8 * zc) := by unfold Apart at o2 ⊢; omega
    have a2 : Apart (fs - 8) 8 zp (8 * zc) := by unfold Apart at o3 ⊢; omega
    exact ⟨⟨n2, ap_wC o1 (by omega) hle, z1, z2⟩, n3, n4, n1, a1, a2, hxi.2.2.2.2.2 hz, hyi.2.2.2.2.2 hz, z3⟩
  · obtain ⟨-, -, -, -, -, -, -, a8, a9, a10, -⟩ := hgl
    exact ⟨Or.inr a9, by simp only [outside_cons, outside_nil, and_true] at a10; unfold Apart; omega, hstgA.symm,
      hfgA.symm⟩
  · rw [show SP - 0x2f8 + 0x300 = SP + 0 + 8 by omega]; exact hy1
  · rw [show SP - 0x2f8 + 0x308 = SP + 0 + 16 by omega]; exact hy2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`expNNPowerOfTwoWindowSize4`** (amd64) as a `Summary` on `LibW` in the `CPre` form (see the module doc) -/
theorem fullC {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41512 + 0x300 ≤ stk) (hk1 : P2Pre.K kc + 0x300 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x300)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Summary (LibW.program.link impl) fnE
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧
        s.regs 7 = BitVec.ofNat 64 st ∧ s.regs 6 = BitVec.ofNat 64 xp ∧ s.regs 8 = BitVec.ofNat 64 xl ∧
        s.regs 9 = BitVec.ofNat 64 xc ∧ s.regs 10 = BitVec.ofNat 64 lm ∧ NHyp.StkArg s 0 yp yl yc ∧
        s.xmm 15 = 0 ∧ s.df = false ∧
        PreC R b L stk (costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧ EX xp xl s ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧
        NHyp.CPostR R b L stk 0x60 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
          (costB (stLen s.mem st) yl lm) s s') := by
  intro s hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, hy, hx15, hdf, hP, hX, hr47⟩
  have hkK : 184 + kc ≤ P2Pre.K kc := Nat.le_refl _
  have hcb : costB (stLen s.mem st) yl lm ≤ b := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzlc : zl ≤ zc := hP.1.2.2.2.2.2.1
  have hzc : zc < 2 ^ 40 := hP.1.2.2.2.2.2.2.1.1
  have hrl := stkR_le (HW (stLen s.mem st) lm) s.mem st
  have hcb' : cost yl lm + stkRes (HW (stLen s.mem st) lm) ≤ b := hcb
  have hE := epre_of (xc := xc) (yc := yc) hP hk0 hk2 hzp hxc hx15 hdf hy hr47
    (Nat.le_trans hrl (by omega))
  have e : stk - 0x300 + 0x300 = stk := by simp only [P2Pre.K] at hk1; omega
  have := full hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT hE hX
    (by simp only [P2Pre.K] at hk1 ⊢; omega) hP.2.1 hP.2.2.1 (by omega) (zl := zl) (by omega) hpc h0 h3 h1 h7 h6 h8
    h9 h10
  obtain ⟨k, s', hs, hr, hq⟩ := this
  simp only [FQ, e] at hq
  refine ⟨k, s', hs, hr, hq.1, ?_⟩
  obtain ⟨hfs, hdf', p, l, cc, r0, r1, r2, L', b', hres, ⟨hx, hb, hinv⟩, rest⟩ := hq.2
  exact ⟨hfs, hdf', p, l, cc, r0, r1, r2, L', b', hres, ⟨hx, by simp only [costB]; omega, hinv⟩, rest⟩

end FvModexp.Amd64.P2W4
