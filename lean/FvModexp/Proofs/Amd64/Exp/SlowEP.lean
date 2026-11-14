import FvModexp.Proofs.Amd64.Exp.SlowDefs
import FvModexp.Proofs.Amd64.Exp.SlowQStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the internal entry facts from the exported precondition (agent expmc s78; twin of arm64
`Exp/SlowEP.lean`, proof as asm's amd64 `ExpEven.epre_of` (EvEP.lean))

`epre_of`: the `NHyp.CPre` form at `RSP` (window `[RSP - stk, RSP + 0x70)`, the `SlowHypQ` pre's `CPre` conjunct
with any cost) gives `EPre` with frame `sp = RSP - 0x1b0`, `K = stk - 0x1b8` (so `[sp - 8 - K, sp + 0x220)` is the
same window), the caller's `RBP` as `bp` and the return-address word as `r`. `len x, len m ≤ 128` come from the
`need` conjunct (`need = 2^16 + 1` otherwise). `xc_of`: `x`'s capacity facts from `XFacts`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- an `Outside` the exported window fact as `Apart` from the internal window -/
theorem ap_w {a k SP stk : Nat} (h : Outside a k [(SP - stk, SP + 0x70)]) (h1 : 0x1b8 ≤ stk) (h2 : stk ≤ SP) :
    Apart a k (SP - 0x1b0 - 8 - (stk - 0x1b8)) (stk - 0x1b8 + 0x228) := by
  simp only [outside_cons, outside_nil, and_true] at h; unfold Apart; omega

theorem win_eq {SP stk : Nat} (h1 : 0x1b8 ≤ stk) (h2 : stk ≤ SP) :
    [(SP - stk, SP + 0x70)] = [(SP - 0x1b0 - 8 - (stk - 0x1b8), SP - 0x1b0 + wTop)] := by
  simp only [wTop]
  rw [show SP - 0x1b0 - 8 - (stk - 0x1b8) = SP - stk by omega, show SP - 0x1b0 + 0x220 = SP + 0x70 by omega]

/-- an input operand of the exported pre as an entry object -/
theorem oe_of {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk st p n SP : Nat} (hS : (s.regs 4).toNat = SP)
    (h1 : 0x1b8 ≤ stk) (h2 : stk ≤ SP)
    (h : EvenHyp.RdIn R L s stk 0x70 p n) (hst : Apart p (8 * n) st 24)
    (hf : Apart p (8 * n) (NHyp.freeOf s.mem st).1 (NHyp.freeOf s.mem st).2) :
    OE R L (SP - 0x1b0) (stk - 0x1b8) st s.mem p (8 * n) := by
  obtain ⟨-, -, -, hH, hw⟩ := h
  simp only [win, hS] at hw
  exact ⟨hH, ap_w hw h1 h2, hst, hf⟩

/-- the `need` conjunct bounds the operand lengths -/
theorem lens_of {l xl yl ml : Nat} (h : l + need xl yl ml ≤ 2 ^ 16) : xl ≤ 128 ∧ ml ≤ 128 ∧ l + 2 ^ 13 ≤ 2 ^ 16 := by
  by_cases hc : xl ≤ 128 ∧ ml ≤ 128
  · simp only [need, if_pos hc] at h; exact ⟨hc.1, hc.2, h⟩
  · simp only [need, if_neg hc] at h; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the internal entry facts** -/
theorem epre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk c : Nat}
    {zp zl zc st xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    (hC : NHyp.CPre R b L stk 0x70 zp zl zc st [(xp, xl), (yp, yl), (mp, ml)] (need xl yl ml) c s)
    (hM : 0 < natVal s.mem mp ml) (hY : 2 ≤ natVal s.mem yp yl) (hst : 0 < st)
    (hk1 : 41512 + 0x1b8 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x1b8) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hy : NHyp.StkArg s 0 yp yl yc)
    (hm : NHyp.StkArg s 24 mp ml mc) (hr47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    EPre R b L (stk - 0x1b8) (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x1b0) st (s.regs 5).toNat
      (s.mem.readLE (s.regs 4).toNat 8) zp zc xp xl xc yp yl yc mp ml mc s := by
  obtain ⟨hce, hsv, hgl, hro, hwT, hzl, hwo, hins, hsok, hstw, hstg, harr, hcap0, hneed, hwba, hstwb, hstf,
    ⟨hstfs, hfrfs⟩, hzs, hstgA, hfgA, hcst, hadx, harrfs, hinv⟩ := hC
  obtain ⟨hxl, hml, hst13⟩ := lens_of hneed
  obtain ⟨hgd, ⟨hle, h48, hacc⟩, hal, hdl, hwrt, hgw, hgrt, hLs, -, ⟨htb, htr, htg⟩, htout, htap⟩ := hce
  obtain ⟨gnw, grd, gbl⟩ := hgd
  simp only [regSP, regG, stackguard0, stackguard0Offset] at gnw grd gbl hle h48 hacc htg
  obtain ⟨hy1, hy2, hy3⟩ := hy
  obtain ⟨hm1, hm2, hm3⟩ := hm
  have hyc : yc < 2 ^ 64 := hy3 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := hm3 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  generalize hS : (s.regs 4).toNat = SP at *
  generalize hG : (s.regs 14).toNat = g at *
  generalize hF : s.fsBase.toNat = fs at *
  have hspE : s.regs 4 = BitVec.ofNat 64 (SP - 0x1b0 + 0x1b0) := by
    apply BitVec.eq_of_toNat_eq; rw [hS, BitVec.toNat_ofNat]; omega
  have hgE : s.regs 14 = BitVec.ofNat 64 g := by
    apply BitVec.eq_of_toNat_eq; rw [hG, BitVec.toNat_ofNat]; omega
  have ew := win_eq (SP := SP) (by omega : 0x1b8 ≤ stk) hle
  have hyi := hins yp yl (by simp)
  have hxi := hins xp xl (by simp)
  have hmi := hins mp ml (by simp)
  have hml0 : 0 < ml := by
    rcases Nat.eq_zero_or_pos ml with h | h
    · subst h; simp [natVal] at hM
    · exact h
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  obtain ⟨hwo1, hwo2, hwo3⟩ := hwo
  simp only [win, hS] at hstw harr hwo3 hgl hLs
  rw [ew] at hgl hLs
  have hK : stk - 0x1b8 ≤ SP - 0x1b0 - 8 := by omega
  have hww : SP - 0x1b0 - 8 - (stk - 0x1b8) = SP - stk := by omega
  have hwk : stk - 0x1b8 + 0x228 = stk + 0x70 := by omega
  refine ⟨⟨hspE, hgE, hF, hx15, hdf, by omega, by omega, by omega, ⟨by omega, hK, by omega, ?_, by omega, grd,
      by omega, ?_, ?_, hgrt, ?_, hdl, hro, by omega, by omega, htr, htg, htout, ?_⟩, hsv⟩,
    hgl, hwT, hadx, hml0, hml,
    oe_of hS (by omega) hle hyi.1 hyi.2.2.2.1 hyi.2.2.2.2.1, hyi.1.2.1, hyi.1.2.2.1, hyi.2.2.1, hyl0, hyi.2.1,
    oe_of hS (by omega) hle hxi.1 hxi.2.2.2.1 hxi.2.2.2.2.1, hxi.1.2.1, hxi.1.2.2.1, hxi.2.2.1, hxl,
    by have := hxi.1.2.2.1; omega, hxc, hzp, hwo1, fun hz => ?_, ?_, hsok, ap_w hstw (by omega) hle, hstg, hstfs,
    fun hc => ⟨ap_w (harr hc).1 (by omega) hle, (harr hc).2, harrfs hc⟩, hwba, hstwb, hstf, by omega, hst13,
    ⟨oe_of hS (by omega) hle hmi.1 hmi.2.2.2.1 hmi.2.2.2.2.1, hmi.1.2.1, hmi.1.2.2.1, hmi.2.2.1,
      hmi.2.2.2.2.2, by have := hyi.1.2.2.1; omega, hyc, by have := hmi.1.2.2.1; omega, hmc, hcap0⟩,
    ⟨rfl, by rw [show SP - 0x1b0 + 0x1b0 = SP by omega], hr47, ?_, ?_, ?_, ?_, ?_, ?_⟩, hinv⟩
  · rw [hww, hwk]; exact hacc
  · rw [hww, hwk]; exact hwrt
  · unfold Apart at hgw ⊢; omega
  · rw [show SP - 0x1b0 - 8 + 0x228 = SP - 0x1b0 + 0x220 by omega]; exact hLs
  · unfold Apart at htap ⊢; omega
  · obtain ⟨n1, n2, n3, n4⟩ := hwo2 hz
    obtain ⟨o1, o2, o3⟩ := hwo3 hz
    obtain ⟨z1, z2, z3⟩ := hzs hz
    have a1 : Apart (g + 16) 8 zp (8 * zc) := by unfold Apart at o2 ⊢; omega
    have a2 : Apart (fs - 8) 8 zp (8 * zc) := by unfold Apart at o3 ⊢; omega
    exact ⟨⟨n2, ap_w o1 (by omega) hle, z1, z2⟩, n3, n4, n1, a1, a2, hxi.2.2.2.2.2 hz, hyi.2.2.2.2.2 hz, z3⟩
  · obtain ⟨-, -, -, -, -, -, -, a8, a9, a10, -⟩ := hgl
    exact ⟨Or.inr a9, by simp only [wTop, outside_cons, outside_nil, and_true] at a10; unfold Apart; omega, hstgA.symm,
      hfgA.symm⟩
  all_goals first
    | (rw [show SP - 0x1b0 + 0x1b8 = SP + 0 + 8 by omega]; exact hy1)
    | (rw [show SP - 0x1b0 + 0x1c0 = SP + 0 + 16 by omega]; exact hy2)
    | (rw [show SP - 0x1b0 + 0x1c8 = SP + 0 + 24 by omega]; exact hy3)
    | (rw [show SP - 0x1b0 + 0x1d0 = SP + 24 + 8 by omega]; exact hm1)
    | (rw [show SP - 0x1b0 + 0x1d8 = SP + 24 + 16 by omega]; exact hm2)
    | (rw [show SP - 0x1b0 + 0x1e0 = SP + 24 + 24 by omega]; exact hm3)

/-- `x`'s capacity facts at the entry (`XFacts`; `XGc`-free: the slow loop reads only `x[0:len x]`) -/
theorem xc_of {R : RtInv} {L : List (Nat × Nat)} {xp xl xc : Nat} (hX : NHyp.XFacts R L xp xl xc) :
    xl ≤ xc ∧ xc < 2 ^ 40 ∧ (0 < xc → Held R L xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48) := hX.1

end FvModexp.Amd64.ExpSlow
