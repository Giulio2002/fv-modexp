import FvModexp.Proofs.Amd64.NatQ.KMulLoop
import FvModexp.Proofs.Amd64.NatQ.KMulPA
import FvModexp.Proofs.Amd64.NatQ.KMulPB
import FvModexp.Proofs.Amd64.NatQ.KMulPC
import FvModexp.Proofs.Amd64.NatQ.KMulPE

set_option autoImplicit false

/-!
# [amd64 port (divmc s53) of the Q-form Arm64/NatQ/KMulPro.lean — TIGHT COSTS] `karatsuba` (amd64): the whole prologue, entry → `KM1` (natmul.go:164-206)

`kmPro` = `kmPA` → `kmLoopX0` (`x0 = x[:n2].norm()`) → `kmPB1` → `kmLoopX1` (`x1 = x[n2:].norm()`) → `kmPB2` →
`kmLoopY0` → `kmPB3` → `kmLoopY1` → `kmPC` → `kmCall` (`stk.nat`, headers). (Adapted from this repo's amd64 `KSqrPro`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (IntAt)

/-- `NatNorm` through a frame that avoids the top limb (copied from this repo's amd64 `KSqrPro.natNorm_frameB`) -/
theorem km_norm_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p l : Nat}
    (ho : Outside p (8 * l) rs) (hn : NatNorm m' p l) : NatNorm m p l := by
  rcases hn with h0 | h1
  · exact Or.inl h0
  · by_cases hl : l = 0
    · exact Or.inl hl
    right; rw [← h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h1

set_option maxRecDepth 20000 in
/-- **`karatsuba`'s prologue**: entry → `KM1` (`0x5f2149`) -/
theorem kmPro (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} (hpre : KPre R b H L W st zp (2 * n) zc xp n xc yp n yc s) (hpc : s.rip = BitVec.ofNat 64 0x5f1da0)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h3 : s.regs 3 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : s.regs 7 = BitVec.ofNat 64 zc)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 n) (h9 : s.regs 9 = BitVec.ofNat 64 xc)
    (y8 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp) (y16 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n)
    (y24 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (S : State) (lx0 lx1 ly0 ly1 t : Nat) (Lk : List (Nat × Nat)) (bk : Nat),
      KM1 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ReachesRet (LibMul.program.link impl) ret s Q := by
  have F := hpre.F
  obtain ⟨-, ⟨hb', ha, -⟩, hal, -⟩ := F.env
  simp only [regSP] at hb' ha
  have hW := F.hW; have hW' := kW64_ge n
  have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40; have hyc := F.ycn; have hyc40 := F.yc40
  have hxacc := F.xacc; have hyacc := F.yacc; have hx48 := F.x48; have hy48 := F.y48
  have hxw := F.xw; have hyw := F.yw
  clear F
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hk : kh n ≤ n ∧ 0 < kh n := by simp only [kh]; omega
  -- the halves of `x`, `y` are outside our frame's writes
  have hfo : ∀ p k, (p + k ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 72 ≤ p) →
      Outside p k [((s.regs 4).toNat - 448, (s.regs 4).toNat), ((s.regs 4).toNat + 32, (s.regs 4).toNat + 72)] :=
    fun p k hp => by simp only [outside_cons, outside_nil, and_true]; omega
  refine kmPA impl hpre hpc h0 h3 h1 h7 h6 h8 h9 y8 y16 y24 ?_
  intro S1 p1 sp1 r0 r3 r1 r7 r6 r8 r9 r10 r11 r12 r2 r14 r5 rfs rdf rx hQ
  have hacc1 : S1.mem.accessible xp (8 * kh n) false = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hacc2 : S1.mem.accessible (xp + 8 * kh n) (8 * (n - kh n)) false = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hacc32 : S1.mem.accessible ((s.regs 4).toNat + 32) 8 false = true := by
    have hw := hpre.F.env.2.1.2.2
    simp only [regSP] at hw
    rw [hQ.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _
      (Janus.Arm64.Memory.accessible_sub _ hw (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)) (by omega) (by omega)
  refine kmLoopX0 impl ret Q S1.mem S1.regs S1.fsBase S1.df (S1.xmm 15) xp (kh n) (natVal S1.mem xp (kh n)) hacc1
    (by omega) (by omega) r6 ?_ (kh n) S1 (Nat.le_refl _) p1 r2 (fun _ _ _ => rfl) rfl rfl rfl rfl rfl
  intro S' lx0 q1 q2 qR qfs qdf qx qm hl0 hv0 hn0
  have g : ∀ r, r ≠ 2 → r ≠ 13 → S'.regs r = S1.regs r := qR
  refine kmPB1 impl (S := S') (qm ▸ hQ) hl0 q1 ((g 4 (by decide) (by decide)).trans sp1)
    ((g 0 (by decide) (by decide)).trans r0) ((g 3 (by decide) (by decide)).trans r3)
    ((g 1 (by decide) (by decide)).trans r1) ((g 7 (by decide) (by decide)).trans r7)
    ((g 6 (by decide) (by decide)).trans r6) ((g 8 (by decide) (by decide)).trans r8)
    ((g 9 (by decide) (by decide)).trans r9) ((g 10 (by decide) (by decide)).trans r10)
    ((g 11 (by decide) (by decide)).trans r11) ((g 12 (by decide) (by decide)).trans r12) q2
    ((g 14 (by decide) (by decide)).trans r14) ((g 5 (by decide) (by decide)).trans r5)
    (qfs.trans rfs) (qdf.trans rdf) (qx.trans rx) ?_
  intro S2 p2 sp2 t0 t3 t1 t7 t6 t8 t9 t10 t11 t12 t13 t15 t2 t14 t5 tfs tdf tx hQ2 m32 m368
  have hacc2' : S2.mem.accessible (xp + 8 * kh n) (8 * (n - kh n)) false = true := by
    rw [hQ2.fr.accessible, ← hQ.fr.accessible]; exact hacc2
  have esp : (S2.regs 4).toNat + 480 = (s.regs 4).toNat + 32 := by
    rw [sp2]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hacc11' : S2.mem.accessible ((S2.regs 4).toNat + 480) 8 false = true := by
    rw [hQ2.fr.accessible, ← hQ.fr.accessible, esp]; exact hacc32
  have h11' : S2.mem.readLE ((S2.regs 4).toNat + 480) 8 = (S2.regs 0).toNat := by
    rw [esp, m32, t0, BitVec.toNat_ofNat]
    have := hpre.F.stk.2.1.2.2.2.1
    omega
  have hsp48 : (S2.regs 4).toNat + 488 ≤ 2 ^ 48 := by
    rw [sp2]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine kmLoopX1 impl ret Q S2.mem S2.regs S2.fsBase S2.df (S2.xmm 15) (xp + 8 * kh n) (n - kh n)
    (natVal S2.mem (xp + 8 * kh n) (n - kh n)) hacc2' (by omega) (by omega) t9 h11' hacc11' hsp48 ?_
    (n - kh n) S2 (Nat.le_refl _) p2 t8 (fun _ _ => rfl) rfl rfl rfl rfl rfl
  intro S3 lx1 u1 u8 uR ufs udf ux um hl1 hv1 hn1
  have g2 : ∀ r, r ≠ 8 → S3.regs r = S2.regs r := uR
  have hQ3 : KQm R b H L W st zp zc xp n xc yp yc s S3.mem := um ▸ hQ2
  refine kmPB2 impl (S := S3) hQ3 hl0 hl1 u1 ((g2 4 (by decide)).trans sp2)
    ((g2 0 (by decide)).trans t0) ((g2 3 (by decide)).trans t3) ((g2 1 (by decide)).trans t1)
    ((g2 7 (by decide)).trans t7) ((g2 6 (by decide)).trans t6) u8 ((g2 9 (by decide)).trans t9)
    ((g2 10 (by decide)).trans t10) ((g2 11 (by decide)).trans t11) ((g2 12 (by decide)).trans t12)
    ((g2 13 (by decide)).trans t13) ((g2 15 (by decide)).trans t15) ((g2 2 (by decide)).trans t2)
    ((g2 14 (by decide)).trans t14) ((g2 5 (by decide)).trans t5) (ufs.trans tfs) (udf.trans tdf) (ux.trans tx)
    (um ▸ m32) (um ▸ m368) ?_
  intro S4 p4 sp4 v0 v3 v1 v7 v6 v10 v11 v12 v15 v2 v14 v5 vfs vdf vx hQ4 n32 n48 hx0 hx1
  have hacc3 : S4.mem.accessible yp (8 * kh n) false = true := by
    rw [hQ4.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hyacc (by omega) (by omega)
  have hacc4 : S4.mem.accessible (yp + 8 * kh n) (8 * (n - kh n)) false = true := by
    rw [hQ4.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hyacc (by omega) (by omega)
  refine kmLoopY0 impl ret Q S4.mem S4.regs S4.fsBase S4.df (S4.xmm 15) yp (kh n) (natVal S4.mem yp (kh n)) hacc3
    (by omega) (by omega) v1 ?_ (kh n) S4 (Nat.le_refl _) p4 v15 (fun _ _ _ => rfl) rfl rfl rfl rfl rfl
  intro S5 ly0 w1 w15 wR wfs wdf wx wm hm0 hw0 hmn0
  have g3 : ∀ r, r ≠ 15 → r ≠ 6 → S5.regs r = S4.regs r := wR
  refine kmPB3 impl (S := S5) (wm ▸ hQ4) hm0 w1 ((g3 4 (by decide) (by decide)).trans sp4)
    ((g3 0 (by decide) (by decide)).trans v0) ((g3 3 (by decide) (by decide)).trans v3)
    ((g3 1 (by decide) (by decide)).trans v1) ((g3 7 (by decide) (by decide)).trans v7)
    ((g3 10 (by decide) (by decide)).trans v10) ((g3 11 (by decide) (by decide)).trans v11)
    ((g3 12 (by decide) (by decide)).trans v12) w15 ((g3 2 (by decide) (by decide)).trans v2)
    ((g3 14 (by decide) (by decide)).trans v14) ((g3 5 (by decide) (by decide)).trans v5)
    (wfs.trans vfs) (wdf.trans vdf) (wx.trans vx) ?_
  intro S6 p6 sp6 y0 y3 y1 y7 y6 y8 y9 y10 y11 y12 y15 y2 y14 y5 yfs ydf yx wm6
  refine kmLoopY1 impl ret Q S4.mem S6.regs S6.fsBase S6.df (S6.xmm 15) (yp + 8 * kh n) (n - kh n)
    (natVal S4.mem (yp + 8 * kh n) (n - kh n)) hacc4 (by omega) (by omega) y6 ?_ (n - kh n) S6
    (Nat.le_refl _) p6 y10 (fun _ _ _ => rfl) rfl rfl rfl (wm6.trans wm) rfl
  intro S7 ly1 z1 z10 zR zfs zdf zx zm hm1 hw1 hmn1
  have g4 : ∀ r, r ≠ 10 → r ≠ 13 → S7.regs r = S6.regs r := zR
  have hQ7 : KQm R b H L W st zp zc xp n xc yp yc s S7.mem := zm ▸ hQ4
  have hF1 := hQ.fr
  have hF2 := hQ2.fr
  have hF4 := hQ4.fr
  refine kmPC impl (S := S7) hQ7 hl0
    (((natVal_frame hF1 (hfo _ _ (by omega))).symm.trans hv0).trans (natVal_frame hF1 (hfo _ _ (by omega))))
    (km_norm_frame hF1 (hfo _ _ (by omega)) hn0) hl1
    (((natVal_frame hF2 (hfo _ _ (by omega))).symm.trans hv1).trans (natVal_frame hF2 (hfo _ _ (by omega))))
    (km_norm_frame hF2 (hfo _ _ (by omega)) hn1) hm0
    (((natVal_frame hF4 (hfo _ _ (by omega))).symm.trans hw0).trans (natVal_frame hF4 (hfo _ _ (by omega))))
    (km_norm_frame hF4 (hfo _ _ (by omega)) hmn0) hm1
    (((natVal_frame hF4 (hfo _ _ (by omega))).symm.trans hw1).trans (natVal_frame hF4 (hfo _ _ (by omega))))
    (km_norm_frame hF4 (hfo _ _ (by omega)) hmn1) (zm ▸ n32) (zm ▸ n48) (zm ▸ hx0) (zm ▸ hx1) z1
    ((g4 4 (by decide) (by decide)).trans sp6)
    ((g4 0 (by decide) (by decide)).trans y0) ((g4 3 (by decide) (by decide)).trans y3)
    ((g4 1 (by decide) (by decide)).trans y1) ((g4 7 (by decide) (by decide)).trans y7)
    ((g4 6 (by decide) (by decide)).trans y6) ((g4 8 (by decide) (by decide)).trans y8)
    ((g4 9 (by decide) (by decide)).trans y9) z10 ((g4 11 (by decide) (by decide)).trans y11)
    ((g4 12 (by decide) (by decide)).trans y12) ((g4 15 (by decide) (by decide)).trans y15)
    ((g4 2 (by decide) (by decide)).trans y2) ((g4 14 (by decide) (by decide)).trans y14)
    ((g4 5 (by decide) (by decide)).trans y5) (zfs.trans yfs) (zdf.trans ydf) (zx.trans yx)
    fun P hP => kmCall impl hap R hgr hmc hwb hP hx150 hdf0 fun S t Lk bk hB => hK S lx0 lx1 ly0 ly1 t Lk bk hB

end FvModexp.Amd64.Q.NatMul
