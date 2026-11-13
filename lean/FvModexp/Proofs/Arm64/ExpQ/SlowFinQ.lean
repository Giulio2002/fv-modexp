import FvModexp.Proofs.Arm64.ExpQ.SlowXUQ
import FvModexp.Proofs.Arm64.Exp.SlowFin

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowFin.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): `EX` → `RET` with the function's post `FQ` (agent expmc)

At `EX` (`fnE + 0x528`, nat.go:787 `return z.norm()`, nat.go:51-54): `z` is normalised (`LN`), so the `norm` loop
makes one pass (`len z = 0`: `BLE`; else `z[len z - 1] ≠ 0`: `CBZ` not taken); `CMP R2, R5; BHI panic` not taken
(`len ≤ cap`); `R1 := R5`, `LDP -8(RSP), (R29, R30)`, `ADD $432, RSP`, `RET`. No stores.
* `FQ`: the ABI facts and `CPostR0` with the entry window `[SP - (K + 432), SP + 112)`;
* `finQ`: `FQ` from `WC` at the exit memory, `z`'s `LN` (location → `NatOF0`, `FA` → `ResSep`);
* `segFin`: `KE` → `RET` with `FQ`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

/-- the function's post (internal form) -/
@[reducible] def FQQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    NHyp.CPostR0Q R b L (K + 432) 112 zp zc st v (cst + stkR H s.mem st) (stkR H s'.mem st) s s'

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
/-- **the function's post** from the exit memory (no stores after `EX`) -/
theorem finQQ (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 (stLen s.mem st))
    {p l c v cst H : Nat} (hz : LN R L st zp zc M L1 p l c v) (hb : b - (cst + stkR H s.mem st) + stkR H M st ≤ b1)
    {s' : State} (hm : s'.mem = M)
    (e0 : s'.regs 0 = BitVec.ofNat 64 p) (e1 : s'.regs 1 = BitVec.ofNat 64 l) (e2 : s'.regs 2 = BitVec.ofNat 64 c) :
    NHyp.CPostR0Q R b L (K + 432) 112 zp zc st v (cst + stkR H s.mem st) (stkR H s'.mem st) s s' := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hsp := hP.1.sp
  subst hm
  obtain ⟨⟨c40, hlv, hloc, hob, h0⟩, hlc, hv, hn⟩ := hz
  refine ⟨p, l, c, e0, e1, e2, L1, b1, ⟨hv, hn, hlc, c40, hlv, ?loc⟩, ⟨hw.le, hb, ?inv⟩,
    ⟨⟨hw.sok, hw.len, hw.kf⟩, hw.ain⟩, ?fr, hw.lf, ?rs⟩
  case loc =>
    rcases Nat.eq_zero_or_pos c with c0 | c0
    · exact Or.inl ⟨c0, h0 c0⟩
    · rcases hloc with ⟨rfl, rfl, -⟩ | ⟨hin, hap⟩ | ⟨-, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨c0, hin, hap⟩)
      · exact absurd c0 (Nat.lt_irrefl 0)
  case inv => rw [hP.1.g]; exact hw.inv
  case fr =>
    have hwin : winA s (K + 432) 112 = WN sp K := by
      simp only [winA, WN, hsp]
      rw [show sp + 432 - (K + 432) = sp - K by omega, show sp + 432 - 8 = sp + 424 by omega,
        show sp + 432 + 8 = sp + 440 by omega, show sp + 432 + 112 = sp + 544 by omega]
    rw [hwin, show ExpHyp.stWs s.mem st = stkWs s.mem st from rfl]
    simpa only [ZS, List.append_assoc] using hw.fr
  case rs =>
    intro c0 hne
    rcases hw.kf with e | ⟨hin, hap⟩
    · exact absurd e hne
    · exact (hob c0).2.2 hin hap

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`EX` → `RET`** with the function's post -/
theorem segFinQ {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h18 : s.regs 18 = r18) (h29 : s.regs 29 = BitVec.ofNat 64 r29) (hr4 : ret % 4 = 0) (hr48 : ret < 2 ^ 48)
    {cst v H : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 z zl zc' Zv zz zzl zzc
      r rl rc q ql qc) (hv : Zv = v) (hb : b - (cst + stkR H s.mem st) + stkR H S.mem st ≤ b1) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S (FQQ R b H L K zp zc st v cst s) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : S.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hk.jc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hz := hk.bb.bz
  have hw := hk.jc.wc
  subst hv
  have hzl := hk.zl128
  obtain ⟨hz64, hzc64⟩ := hz.1.lt64
  have hlc := hz.2.1
  have hc40 := hz.1.1
  have epc := hk.pc; have e0 := hk.e0; have e5 := hk.e5; have e2 := hk.e2
  have esp := hk.jc.esp; have e28 := hk.jc.e28; have e29 := hk.jc.e29; have e18 := hk.jc.e18
  have hm := hk.jc.hm
  have sfp := hk.jc.sf.sfp; have slr := hk.jc.sf.slr
  have hf48 : r29 < 2 ^ 64 := by
    rw [← sfp]; have := Expmc.readLE_lt_B S.mem (sp - 8) 1; rw [Nat.mul_one, Nat.pow_one, Exp.B_def] at this
    exact this
  have hfin := fun (s' : State) (hm' : s'.mem = S.mem) (q0 : s'.regs 0 = BitVec.ofNat 64 z)
    (q1 : s'.regs 1 = BitVec.ofNat 64 zl) (q2 : s'.regs 2 = BitVec.ofNat 64 zc') =>
    finQQ (cst := cst) hP hw hz (by rw [← hm]; exact hb) (s' := s') (by rw [hm', hm]) q0 q1 q2
  have hssp := hP.1.1
  have hs28 := hP.1.2.1
  clear hk
  rcases Nat.eq_zero_or_pos zl with z0 | z0
  · subst z0
    janus_run [hmacc, sfp, slr]
    refine ⟨?_, ?_, ?_, ?_, hfin _ rfl ?_ ?_ ?_⟩
    all_goals first | (janus_simp; done) | (janus_simp [hssp, hs28, h18, h29]; done) | skip
    rw [hssp]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have hn := hz.2.2.2
    rw [hm] at hn
    have hnz : S.mem.readLE (z + (zl - 1) * 8) 8 ≠ 0 := by
      rcases hn with h | h
      · omega
      · rw [Nat.mul_comm]; exact h
    obtain ⟨-, -, a3, a4⟩ := hz.1.2.1 (by omega)
    rw [hm] at a3
    have hza : S.mem.accessible (z + (zl - 1) * 8) 8 false = true :=
      Memory.accessible_weaken _ (Memory.accessible_mono _ a3 (by omega) (by omega))
    have hsub : BitVec.ofNat 64 zl - 1#64 = BitVec.ofNat 64 (zl - 1) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hmacc, sfp, slr, hnz, hza, hsub]
    refine ⟨?_, ?_, ?_, ?_, hfin _ rfl ?_ ?_ ?_⟩
    all_goals first | (janus_simp; done) | (janus_simp [hssp, hs28, h18, h29]; done) | skip
    rw [hssp]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

end

end FvModexp.Arm64.Q.ExpSlow
