import FvModexp.Proofs.Amd64.Exp.SlowK2
import FvModexp.Proofs.Amd64.Exp.SlowFinR
import FvModexp.Proofs.Amd64.Exp.SlowQStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): `KE` → `RET` with the function's post `FQS` (agent asm s75; twin of arm64
`Arm64/ExpQ/SlowFinQ`)

* `FQS`: the Summary exit facts (`RSP + 8`, `RBP`, `R14`, `X15`) and `NHyp.CPostR0Q` with the entry window
  `[RSP - (K + 0x1b8), RSP + 0x70)` (`RSP = sp + 0x1b0`; it covers `WN sp K`);
* `finQ`: `CPostR0Q` from `WC` at the exit memory and `z`'s `LN` (no stores after `ex`);
* `segFin`: `KE` → `RET` (`runFin`) with `FQS`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.ExpHyp

/-- the function's post (internal form) -/
@[reducible] def FQS (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    NHyp.CPostR0Q R b L (K + 0x1b8) 0x70 zp zc st v (cst + stkR H s.mem st) (stkR H s'.mem st) s s'

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the return address of the entry -/
theorem EPre.r47 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    (s.regs 5).toNat = bp ∧ r < 2 ^ 47 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨h1, -, h2, -⟩, -⟩ := hP
  exact ⟨h1, h2⟩

set_option maxRecDepth 20000 in
/-- **the function's post** from the exit memory (no stores after `ex`) -/
theorem finQ (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 (stLen s.mem st))
    {p l c v cst H : Nat} (hz : LN R L st zp zc M L1 p l c v) (hb : b - (cst + stkR H s.mem st) + stkR H M st ≤ b1)
    {s' : State} (hm : s'.mem = M) (hf : s'.fsBase = s.fsBase) (hd : s'.df = s.df)
    (e0 : s'.regs 0 = BitVec.ofNat 64 p) (e3 : s'.regs 3 = BitVec.ofNat 64 l)
    (e1 : s'.regs 1 = BitVec.ofNat 64 c) :
    NHyp.CPostR0Q R b L (K + 0x1b8) 0x70 zp zc st v (cst + stkR H s.mem st) (stkR H s'.mem st) s s' := by
  have hk := hP.kf
  have hsN : (s.regs 4).toNat = sp + 0x1b0 := hP.1.sp
  subst hm
  obtain ⟨⟨c40, hlv, hloc, hob, h0⟩, hlc, hv, hn⟩ := hz
  refine ⟨hf, hd, p, l, c, e0, e3, e1, L1, b1, ⟨hv, hn, hlc, c40, hlv, ?loc⟩, ⟨hw.le, hb, ?inv⟩,
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
    refine hw.fr.mono fun a n ho => ?_
    simp only [win, hsN, WN, ZS, stWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨ho.1.1.1, by omega, by omega⟩, ho.1.2, ho.2⟩
  case rs =>
    intro c0 hne
    rcases hw.kf with e | ⟨hin, hap⟩
    · exact absurd e hne
    · exact (hob c0).2.2 hin hap

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`ex` → `RET`** with the function's post -/
theorem segFin {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {cst v H : Nat} {S : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KE R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc)
    (hv : Zv = v) (hb : b - (cst + stkR H s.mem st) + stkR H S.mem st ≤ b1) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQS R b H L K zp zc st v cst s) := by
  have hkf := hP.kf
  have hbr := hP.r47
  have hce := hP.cenv0
  have hz := hk.bb.bz
  have hw := hk.jc.wc
  subst hv
  obtain ⟨hz64, hzc64⟩ := hz.1.lt64
  have hlc := hz.2.1
  have hacc : S.mem.accessible (sp + 0x1a8) 16 false = true := by
    rw [hw.fr.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hce.2.2.2.1 (by omega) (by omega))
  have hn : 0 < zl → S.mem.readLE (z + zl * 8 - 8) 8 ≠ 0 := by
    intro h0
    rcases hz.2.2.2 with h | h
    · omega
    · rw [show z + zl * 8 - 8 = z + 8 * (zl - 1) by omega]; exact h
  have hza : 0 < zl → S.mem.accessible (z + zl * 8 - 8) 8 false = true := by
    intro h0
    obtain ⟨-, -, a3, -⟩ := hz.1.2.1 (by omega)
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ a3 (by omega) (by omega))
  have hpl : z + zl * 8 ≤ 2 ^ 48 := by
    rcases Nat.eq_zero_or_pos zc' with c0 | c0
    · have := hz.1.2.2.2.2 c0; omega
    · have := (hz.1.2.1 c0).2.2.2; omega
  refine ReachesRet.mono (runFin (impl := impl) S sp g fs bp r z zl zc' S.mem hk.pc hk.jc.esp hk.jc.e14 hk.jc.efs
    hk.jc.ex15 hk.jc.edf hk.e0 hk.e10 hk.e8 rfl hz64 hlc hzc64 hn hza hpl hacc hk.jc.esl.1 hk.jc.esl.2.1 hbr.2
    (by omega)) fun s' ⟨t4, t5, t14, tfs, tx, tdf, t0, t3, t1, tm⟩ => ?_
  have hE := hP.1
  refine ⟨⟨?_, by rw [t5]; exact (bv_of_toNat hbr.1).symm, by rw [t14, hE.2.1], by rw [tx, hE.2.2.2.1]⟩,
    finQ hP hw hz hb tm (BitVec.eq_of_toNat_eq (by rw [tfs, hE.2.2.1]))
      (by rw [tdf, hE.2.2.2.2.1]) t0 t3 t1⟩
  have h48 : sp + 0x1b8 ≤ 2 ^ 48 := by omega
  rw [t4, hE.1]
  bv_omega

end

end FvModexp.Amd64.ExpSlow
