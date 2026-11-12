import FvModexp.Proofs.Arm64.Nat.DivLargeCall

/-!
# `divLarge` (arm64): the quotient's array `q = z.make(m + 1)` (natdiv.go:620-623) — relations (pure)

`QArr`: `q`'s array `(qp, qc)` (`z`'s when `cap z ≥ m + 1`, else fresh; `alias(z, u)` is false: `z` is apart from `u`'s
array). `AtJ`: the state at the join after `z.make` (`fn + 0x38c`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

namespace FvModexp.Arm64.DivLarge

/-- `q`'s array -/
structure QArr (R : RtInv) (zp zc st : Nat) (vp vl : Nat) (il : Nat) (s : State) (t w1 c1 : Nat)
    (L1 Lq : List (Nat × Nat)) (lenS : Nat) (P C qp qc : Nat) (M : Memory) : Prop where
  cap : il - vl + 1 ≤ qc
  c40 : qc < 2 ^ 40
  p8 : qp % 8 = 0
  p48 : qp + 8 * qc ≤ 2 ^ 48
  pacc : M.accessible qp (8 * qc) true = true
  pw : qp + 8 * qc ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ qp
  pg : Apart qp (8 * qc) ((s.regs 28).toNat + 16) 8
  pheld : Held R Lq qp (8 * qc)
  ror : (qp = zp ∧ qc = zc) ∨ (zc < il - vl + 1 ∧ InRanges qp (8 * qc) R.rt ∧ ApartAll qp (8 * qc) L1)
  pu : Apart qp (8 * qc) P (8 * C)
  pv : Apart qp (8 * qc) vp (8 * vl)
  pt : Apart qp (8 * qc) t (8 * vl)
  ps : Apart qp (8 * qc) st 24
  pf : Apart qp (8 * qc) (w1 + 8 * lenS) (8 * (c1 - lenS))

theorem QArr.frame {R : RtInv} {zp zc st vp vl il : Nat} {s : State} {t w1 c1 : Nat} {L1 Lq : List (Nat × Nat)}
    {lenS P C qp qc : Nat} {M M' : Memory} (h : QArr R zp zc st vp vl il s t w1 c1 L1 Lq lenS P C qp qc M)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) :
    QArr R zp zc st vp vl il s t w1 c1 L1 Lq lenS P C qp qc M' :=
  { h with pacc := by rw [hacc]; exact h.pacc }

/-- the join after `z.make(m + 1)` -/
abbrev joinQ : Nat := segAddr Extracted.program fn + 0x38c

/-- the state at `joinQ` -/
structure AtJ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat) (S : State) :
    Prop where
  pc : S.pc = BitVec.ofNat 64 joinQ
  sp : S.sp = s.sp - 304#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 312#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 t
  r1 : S.regs 1 = BitVec.ofNat 64 vl
  r2 : S.regs 2 = BitVec.ofNat 64 vl
  r3 : S.regs 3 = BitVec.ofNat 64 C
  r4 : S.regs 4 = BitVec.ofNat 64 (il + 1)
  r5 : S.regs 5 = BitVec.ofNat 64 P
  r6 : S.regs 6 = BitVec.ofNat 64 qc
  r12 : S.regs 12 = BitVec.ofNat 64 vl
  r14 : S.regs 14 = BitVec.ofNat 64 qp
  r15 : S.regs 15 = BitVec.ofNat 64 (il - vl + 1)
  mem : MemU R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lq bq P C sh S.mem
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C S.mem
  qa : QArr R zp zc st vp vl il s t w1 c1 L1 Lq (stLen s.mem st + StackNat.rnd vl) P C qp qc S.mem
  ext3 : LiveExt R L1 Lq
  bud3 : b1 - makeCost (il + 1) - makeCost (il - vl + 1) ≤ bq
  sh63 : sh ≤ 63
  vval : natVal S.mem t vl = natVal s.mem vp vl * 2 ^ sh
  vtop : 2 ^ 63 ≤ S.mem.readLE (t + 8 * (vl - 1)) 8
  uval : natVal S.mem P (il + 1) = natVal s.mem ip il * 2 ^ sh

set_option maxHeartbeats 4000000 in
/-- `QArr` on the reuse path (`m + 1 ≤ cap z`): `q = z` -/
theorem qarr_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {P C : Nat} {M : Memory}
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M) (hx : LiveExt R L1 Lk)
    (hacc : ∀ a n w, M.accessible a n w = s.mem.accessible a n w) (hz : il - vl + 1 ≤ zc) :
    QArr R zp zc st vp vl il s t w1 c1 L1 Lk (stLen s.mem st + StackNat.rnd vl) P C zp zc M := by
  have hl := hE.lay
  have hpre := hE.pre
  have hz0 : 0 < zc := by omega
  obtain ⟨hz40, hzl, hzw⟩ := hpre.zo
  obtain ⟨hz8, hzh, hzacc, hz48⟩ := hzl hz0
  have hsz := hpre.sz hz0
  have hzio := hpre.zio hz0
  have hpz := hU.pz hz0
  unfold Apart at hpz
  exact {
    cap := hz, c40 := hz40, p8 := hz8, p48 := hz48, pacc := (by rw [hacc]; exact hzacc),
    pw := hl.zw hz0, pg := (hzw hz0).2, pheld := hx.held (hE.ext.held hzh), ror := Or.inl ⟨rfl, rfl⟩,
    pu := (by unfold Apart; omega), pv := hzio.2, pt := (by have := hl.tz hz0; unfold Apart; omega), ps := hsz.1,
    pf := apart_free hE (by omega) hzh hsz.2 }

set_option maxHeartbeats 4000000 in
/-- `QArr` on the allocation path: `makeslice` returned `[ptr, ptr + round)` (fresh, apart from `Lk`) -/
theorem qarr_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {P C : Nat} {M : Memory}
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M) (hx : LiveExt R L1 Lk)
    (hz : zc < il - vl + 1) {ptr round qc : Nat} (hAp : ApartAll ptr round Lk) (hIn : InRanges ptr round R.rt)
    (hle : ptr + round ≤ 2 ^ 48) (hacc : M.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hsz : 8 * qc ≤ round) (hq : il - vl + 1 ≤ qc) (hq40 : qc < 2 ^ 40) (hw1h : Held R Lk w1 (8 * c1)) :
    QArr R zp zc st vp vl il s t w1 c1 L1 (Lk ++ [(ptr, ptr + round)]) (stLen s.mem st + StackNat.rnd vl) P C ptr qc M := by
  have hl := hE.lay
  have hpre := hE.pre
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hpre.ce.2.2.2.2.2.1
  have hpw := outside_of_inRanges hout hIn
  have hpg := outside_of_inRanges hgr hIn
  have fr : ∀ p n, Held R Lk p n → p + n ≤ ptr ∨ ptr + round ≤ p := by
    intro p n hh
    rcases hh with hi | ho
    · obtain ⟨r, hr, h1, h2⟩ := hi; have := hAp r hr; unfold Apart at this; omega
    · have := outside_of_inRanges ho hIn; omega
  have hpu := fr _ _ hU.pheld
  have hc1 := hE.c1len
  exact {
    cap := hq, c40 := hq40, p8 := h8, p48 := (by omega),
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := (by omega), pg := (by unfold Apart; omega),
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    ror := Or.inr ⟨hz, hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r (hx.mem_old hr)).mono (by omega)
      (Nat.le_refl _)⟩,
    pu := (by unfold Apart; omega),
    pv := (by have := fr _ _ (hx.held (hE.ext.held hpre.vo.2.2.2.1)); unfold Apart; omega),
    pt := (by have := fr _ _ (hx.held hl.theld); unfold Apart; omega),
    ps := (by have := fr _ _ (hx.held (hE.ext.held hpre.sti.1.2.1)); unfold Apart; omega),
    pf := (by have := fr _ _ hw1h; unfold Apart; omega) }

end FvModexp.Arm64.DivLarge
