import FvModexp.Proofs.Arm64.Nat.KMulLoop
import FvModexp.Proofs.Arm64.Nat.KMulPA
import FvModexp.Proofs.Arm64.Nat.KMulPB
import FvModexp.Proofs.Arm64.Nat.KMulPC
import FvModexp.Proofs.Arm64.Nat.KMulPE

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the whole prologue, entry → `KM1` (natmul.go:164-206)

`kmPro` = `kmPA` → `kmLoopX0` (`x0 = x[:n2].norm()`) → `kmPB1` → `kmLoopX1` (`x1 = x[n2:].norm()`) → `kmPB2` →
`kmLoopY0` → `kmPB3` → `kmLoopY1` → `kmPC` → `kmCall` (`stk.nat`, headers). (Adapted from this repo's `KSqrPro`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (IntAt)

/-- `NatNorm` through a frame that avoids the top limb (copied from this repo's `KSqrPro.natNorm_frame`) -/
theorem km_norm_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p l : Nat}
    (ho : Outside p (8 * l) rs) (hn : NatNorm m' p l) : NatNorm m p l := by
  rcases hn with h0 | h1
  · exact Or.inl h0
  · by_cases hl : l = 0
    · exact Or.inl hl
    right; rw [← h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h1

set_option maxRecDepth 20000 in
/-- **`karatsuba`'s prologue**: entry → `KM1` (`0x1bc10c`) -/
theorem kmPro (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} (hpre : KPre R b L W st zp (2 * n) zc xp n xc yp n yc s) (hpc : s.pc = BitVec.ofNat 64 0x1bbe70)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h1 : s.regs 1 = BitVec.ofNat 64 zp)
    (h2 : s.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : s.regs 3 = BitVec.ofNat 64 zc)
    (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 n) (h6 : s.regs 6 = BitVec.ofNat 64 xc)
    (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 n) (h9 : s.regs 9 = BitVec.ofNat 64 yc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (S : State) (lx0 lx1 ly0 ly1 t : Nat) (Lk : List (Nat × Nat)) (bk : Nat),
      KM1 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ReachesRet (LibMul.program.link impl) ret s Q := by
  have F := hpre.F
  obtain ⟨-, ⟨hal, hb', ha, -⟩, -⟩ := F.env
  have hW := F.hW; have hW' := kW_ge n
  have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40; have hyc := F.ycn; have hyc40 := F.yc40
  have hxacc := F.xacc; have hyacc := F.yacc; have hx48 := F.x48; have hy48 := F.y48
  have hxw := F.xw; have hyw := F.yw
  clear F
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hk := kh_facts h40
  -- the halves of `x`, `y` are outside our frame's writes
  have hfo : ∀ p k, (p + k ≤ s.sp.toNat - W ∨ s.sp.toNat + 72 ≤ p) →
      Outside p k [(s.sp.toNat - 456, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)] :=
    fun p k hp => by simp only [outside_cons, outside_nil, and_true]; omega
  refine kmPA impl hpre hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
  intro S1 p1 sp1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r28 r29 r18 hQ
  have hacc1 : S1.mem.accessible xp (8 * kh n) false = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hacc2 : S1.mem.accessible (xp + 8 * kh n) (8 * (n - kh n)) false = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hxacc (by omega) (by omega)
  refine kmLoopX0 impl ret Q S1.mem S1.regs S1.sp xp (kh n) (natVal S1.mem xp (kh n)) hacc1 (by omega)
    (by omega) r4 ?_ (kh n) S1 (Nat.le_refl _) p1 r11 (fun _ _ _ _ => rfl) rfl rfl rfl
  intro S' lx0 q1 q11 qR qsp qm hl0 hv0 hn0
  have g : ∀ r, r ≠ 11 → r ≠ 13 → r ≠ 14 → S'.regs r = S1.regs r := qR
  refine kmPB1 impl (S := S') (qm ▸ hQ) hl0 q1 (qsp.trans sp1) ((g 0 (by decide) (by decide) (by decide)).trans r0)
    ((g 1 (by decide) (by decide) (by decide)).trans r1) ((g 2 (by decide) (by decide) (by decide)).trans r2)
    ((g 3 (by decide) (by decide) (by decide)).trans r3) ((g 4 (by decide) (by decide) (by decide)).trans r4)
    ((g 5 (by decide) (by decide) (by decide)).trans r5) ((g 6 (by decide) (by decide) (by decide)).trans r6)
    ((g 7 (by decide) (by decide) (by decide)).trans r7) ((g 8 (by decide) (by decide) (by decide)).trans r8)
    ((g 9 (by decide) (by decide) (by decide)).trans r9) ((g 10 (by decide) (by decide) (by decide)).trans r10)
    q11 ((g 12 (by decide) (by decide) (by decide)).trans r12)
    ((g 28 (by decide) (by decide) (by decide)).trans r28) ((g 29 (by decide) (by decide) (by decide)).trans r29)
    ((g 18 (by decide) (by decide) (by decide)).trans r18) ?_
  intro S2 p2 sp2 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t28 t29 t18 qm2
  refine kmLoopX1 impl ret Q S1.mem S2.regs S2.sp (xp + 8 * kh n) (n - kh n)
    (natVal S1.mem (xp + 8 * kh n) (n - kh n)) hacc2 (by omega) (by omega) t14 ?_ (n - kh n) S2
    (Nat.le_refl _) p2 t5 (fun _ _ _ _ => rfl) rfl (qm2.trans qm) rfl
  intro S3 lx1 u1 u5 uR usp um hl1 hv1 hn1
  have g2 : ∀ r, r ≠ 5 → r ≠ 15 → r ≠ 16 → S3.regs r = S2.regs r := uR
  have hQ3 : KQm R b L W st zp zc xp n xc yp yc s S3.mem := um ▸ hQ
  refine kmPB2 impl (S := S3) hQ3 hl0 hl1 u1 (usp.trans sp2)
    ((g2 0 (by decide) (by decide) (by decide)).trans t0) ((g2 1 (by decide) (by decide) (by decide)).trans t1)
    ((g2 2 (by decide) (by decide) (by decide)).trans t2) ((g2 3 (by decide) (by decide) (by decide)).trans t3)
    ((g2 4 (by decide) (by decide) (by decide)).trans t4) u5 ((g2 6 (by decide) (by decide) (by decide)).trans t6)
    ((g2 7 (by decide) (by decide) (by decide)).trans t7) ((g2 8 (by decide) (by decide) (by decide)).trans t8)
    ((g2 9 (by decide) (by decide) (by decide)).trans t9) ((g2 10 (by decide) (by decide) (by decide)).trans t10)
    ((g2 11 (by decide) (by decide) (by decide)).trans t11) ((g2 12 (by decide) (by decide) (by decide)).trans t12)
    ((g2 13 (by decide) (by decide) (by decide)).trans t13) ((g2 14 (by decide) (by decide) (by decide)).trans t14)
    ((g2 28 (by decide) (by decide) (by decide)).trans t28) ((g2 29 (by decide) (by decide) (by decide)).trans t29)
    ((g2 18 (by decide) (by decide) (by decide)).trans t18) ?_
  intro S4 p4 sp4 v0 v1 v2 v3 v4 v7 v8 v9 v10 v12 v28 v29 v18 hQ4 hx0 hx1
  have hacc3 : S4.mem.accessible yp (8 * kh n) false = true := by
    rw [hQ4.fr.accessible]; exact Memory.accessible_mono _ hyacc (by omega) (by omega)
  have hacc4 : S4.mem.accessible (yp + 8 * kh n) (8 * (n - kh n)) false = true := by
    rw [hQ4.fr.accessible]; exact Memory.accessible_mono _ hyacc (by omega) (by omega)
  refine kmLoopY0 impl ret Q S4.mem S4.regs S4.sp yp (kh n) (natVal S4.mem yp (kh n)) hacc3 (by omega)
    (by omega) v7 ?_ (kh n) S4 (Nat.le_refl _) p4 v12 (fun _ _ _ _ => rfl) rfl rfl rfl
  intro S5 ly0 w1 w12 wR wsp wm hm0 hw0 hmn0
  have g3 : ∀ r, r ≠ 12 → r ≠ 5 → r ≠ 6 → S5.regs r = S4.regs r := wR
  refine kmPB3 impl (S := S5) (wm ▸ hQ4) hm0 w1 (wsp.trans sp4)
    ((g3 0 (by decide) (by decide) (by decide)).trans v0) ((g3 1 (by decide) (by decide) (by decide)).trans v1)
    ((g3 2 (by decide) (by decide) (by decide)).trans v2) ((g3 3 (by decide) (by decide) (by decide)).trans v3)
    ((g3 4 (by decide) (by decide) (by decide)).trans v4) ((g3 7 (by decide) (by decide) (by decide)).trans v7)
    ((g3 8 (by decide) (by decide) (by decide)).trans v8) ((g3 9 (by decide) (by decide) (by decide)).trans v9)
    ((g3 10 (by decide) (by decide) (by decide)).trans v10) w12
    ((g3 28 (by decide) (by decide) (by decide)).trans v28) ((g3 29 (by decide) (by decide) (by decide)).trans v29)
    ((g3 18 (by decide) (by decide) (by decide)).trans v18) ?_
  intro S6 p6 sp6 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y12 y28 y29 y18 wm6
  refine kmLoopY1 impl ret Q S4.mem S6.regs S6.sp (yp + 8 * kh n) (n - kh n)
    (natVal S4.mem (yp + 8 * kh n) (n - kh n)) hacc4 (by omega) (by omega) y6 ?_ (n - kh n) S6
    (Nat.le_refl _) p6 y8 (fun _ _ _ _ => rfl) rfl (wm6.trans wm) rfl
  intro S7 ly1 z1 z8 zR zsp zm hm1 hw1 hmn1
  have g4 : ∀ r, r ≠ 8 → r ≠ 11 → r ≠ 13 → S7.regs r = S6.regs r := zR
  have hQ7 : KQm R b L W st zp zc xp n xc yp yc s S7.mem := zm ▸ hQ4
  have hF1 := hQ.fr
  have hF4 := hQ4.fr
  refine kmPC impl (S := S7) hQ7 hl0
    (((natVal_frame hF1 (hfo _ _ (by omega))).symm.trans hv0).trans (natVal_frame hF1 (hfo _ _ (by omega))))
    (km_norm_frame hF1 (hfo _ _ (by omega)) hn0) hl1
    (((natVal_frame hF1 (hfo _ _ (by omega))).symm.trans hv1).trans (natVal_frame hF1 (hfo _ _ (by omega))))
    (km_norm_frame hF1 (hfo _ _ (by omega)) hn1) hm0
    (((natVal_frame hF4 (hfo _ _ (by omega))).symm.trans hw0).trans (natVal_frame hF4 (hfo _ _ (by omega))))
    (km_norm_frame hF4 (hfo _ _ (by omega)) hmn0) hm1
    (((natVal_frame hF4 (hfo _ _ (by omega))).symm.trans hw1).trans (natVal_frame hF4 (hfo _ _ (by omega))))
    (km_norm_frame hF4 (hfo _ _ (by omega)) hmn1) (zm ▸ hx0) (zm ▸ hx1) z1 (zsp.trans sp6)
    ((g4 0 (by decide) (by decide) (by decide)).trans y0) ((g4 1 (by decide) (by decide) (by decide)).trans y1)
    ((g4 2 (by decide) (by decide) (by decide)).trans y2) ((g4 3 (by decide) (by decide) (by decide)).trans y3)
    ((g4 4 (by decide) (by decide) (by decide)).trans y4) ((g4 5 (by decide) (by decide) (by decide)).trans y5)
    ((g4 6 (by decide) (by decide) (by decide)).trans y6) ((g4 7 (by decide) (by decide) (by decide)).trans y7)
    z8 ((g4 9 (by decide) (by decide) (by decide)).trans y9) ((g4 10 (by decide) (by decide) (by decide)).trans y10)
    ((g4 12 (by decide) (by decide) (by decide)).trans y12) ((g4 28 (by decide) (by decide) (by decide)).trans y28)
    ((g4 29 (by decide) (by decide) (by decide)).trans y29) ((g4 18 (by decide) (by decide) (by decide)).trans y18)
    fun P hP => kmCall impl hap R hgr hmc hwb hP fun S t Lk bk hB => hK S lx0 lx1 ly0 ly1 t Lk bk hB

end FvModexp.Arm64.NatMul
