import FvModexp.Proofs.Amd64.NatQ.KSqrPA
import FvModexp.Proofs.Amd64.NatQ.KSqrPB
import FvModexp.Proofs.Amd64.NatQ.KSqrPC

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/KSqrPro.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the whole
prologue, entry → `KB1` (natmul.go:257-292)

`kPro` = `kPA` → `kLoop1` (`x0 = x[:n2].norm()`) → `kPB` → `kLoop2` (`x1 = x[n2:].norm()`) → `kPC` (`stk.nat` call).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

/-- `NatNorm` through a frame that avoids the top limb -/
theorem natNorm_frameB {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p l : Nat}
    (ho : Outside p (8 * l) rs) (hn : NatNorm m' p l) : NatNorm m p l := by
  rcases hn with h0 | h1
  · exact Or.inl h0
  · by_cases hl : l = 0
    · exact Or.inl hl
    right; rw [← h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h1

set_option maxRecDepth 20000 in
/-- **`karatsubaSqr`'s prologue**: entry → the state after `z1 := stk.nat(2·n2 + 1)` (`KB1`) -/
theorem kPro (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} (hpre : KPre R b H L W st zp (2 * n) zc xp n xc s) (hpc : s.rip = BitVec.ofNat 64 0x5f2380)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h3 : s.regs 3 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : s.regs 7 = BitVec.ofNat 64 zc)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 n) (h9 : s.regs 9 = BitVec.ofNat 64 xc)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (S : State) (lx0 lx1 : Nat) (Lk : List (Nat × Nat)) (bk : Nat),
      KB1 R b H L W st zp zc xp n xc s lx0 lx1 (stW S.mem st + 8 * stLen s.mem st) S Lk bk →
      ReachesRet (LibSqr.program.link impl) ret S Q) :
    ReachesRet (LibSqr.program.link impl) ret s Q := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, hal, -⟩, hW, -, -, -, h80, hxc, hxc40, hn12, hxacc, -, hxp48, hxw, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  simp only [regSP] at hb' ha hw
  unfold ksqrW at hW
  have hk : kn2 n ≤ n ∧ 0 < kn2 n := by simp only [kn2]; omega
  refine kPA impl hpre hpc h0 h3 h1 h7 h6 h8 h9 ?_
  intro S1 p1 sp1 r0 r3 r1 r7 r6 r8 r9 r10 r11 r2 r14 r5 rfs rdf rx hQ
  have hxo : ∀ k, k ≤ n → Outside xp (8 * k)
      [((s.regs 4).toNat - 320, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 48)] :=
    fun k hk' => by simp only [outside_cons, outside_nil, and_true]; omega
  have hxo2 : ∀ k, k ≤ n - kn2 n → Outside (xp + 8 * kn2 n) (8 * k)
      [((s.regs 4).toNat - 320, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 48)] :=
    fun k hk' => by simp only [outside_cons, outside_nil, and_true]; omega
  have hacc1 : S1.mem.accessible xp (8 * kn2 n) false = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hacc2 : S1.mem.accessible (xp + 8 * kn2 n) (8 * (n - kn2 n)) false = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hacc11 : S1.mem.accessible ((s.regs 4).toNat - 240) 8 false = true := by
    rw [hQ.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _
      (Janus.Arm64.Memory.accessible_sub _ hw (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)) (by omega) (by omega)
  clear hw
  refine kLoop1 impl ret Q S1.mem S1.regs S1.fsBase S1.df (S1.xmm 15) xp (kn2 n) (natVal S1.mem xp (kn2 n)) hacc1
    (by omega) (by omega) r6 ?_ (kn2 n) S1 (Nat.le_refl _) p1 r2 (fun _ _ _ => rfl) rfl rfl rfl rfl rfl
  intro S' lx0 q1 q2 qR qfs qdf qx qm hl0 hv0 hn0
  have g : ∀ r, r ≠ 2 → r ≠ 12 → S'.regs r = S1.regs r := qR
  refine kPB impl (S := S') (qm ▸ hQ) hl0 q1 ((g 4 (by decide) (by decide)).trans sp1)
    ((g 0 (by decide) (by decide)).trans r0) ((g 3 (by decide) (by decide)).trans r3)
    ((g 1 (by decide) (by decide)).trans r1) ((g 7 (by decide) (by decide)).trans r7)
    ((g 6 (by decide) (by decide)).trans r6) ((g 8 (by decide) (by decide)).trans r8)
    ((g 9 (by decide) (by decide)).trans r9) ((g 10 (by decide) (by decide)).trans r10)
    ((g 11 (by decide) (by decide)).trans r11) q2 ((g 14 (by decide) (by decide)).trans r14)
    ((g 5 (by decide) (by decide)).trans r5) (qfs.trans rfs) (qdf.trans rdf) (qx.trans rx) ?_
  intro S2 p2 sp2 t0 t3 t1 t7 t6 t8 t9 t10 t11 t12 t13 t15 t2 t14 t5 tfs tdf tx hQ2 hn1s
  have hacc2' : S2.mem.accessible (xp + 8 * kn2 n) (8 * (n - kn2 n)) false = true := by
    rw [hQ2.fr.accessible, ← hQ.fr.accessible]; exact hacc2
  have hacc11' : S2.mem.accessible ((S2.regs 4).toNat + 72) 8 false = true := by
    rw [hQ2.fr.accessible, ← hQ.fr.accessible, sp2]
    rw [show (s.regs 4 - 312#64).toNat + 72 = (s.regs 4).toNat - 240 by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega]
    exact hacc11
  have h11' : S2.mem.readLE ((S2.regs 4).toNat + 72) 8 = (S2.regs 11).toNat := by
    rw [sp2, t11, show (s.regs 4 - 312#64).toNat + 72 = (s.regs 4).toNat - 240 by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega, hn1s, BitVec.toNat_ofNat]
    omega
  have hsp48 : (S2.regs 4).toNat + 80 ≤ 2 ^ 48 := by
    rw [sp2]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine kLoop2 impl ret Q S2.mem S2.regs S2.fsBase S2.df (S2.xmm 15) (xp + 8 * kn2 n) (n - kn2 n)
    (natVal S2.mem (xp + 8 * kn2 n) (n - kn2 n)) hacc2' (by omega) (by omega) t9 h11' hacc11' hsp48 ?_
    (n - kn2 n) S2 (Nat.le_refl _) p2 t8 (fun _ _ => rfl) rfl rfl rfl rfl rfl
  intro S3 lx1 u1 u8 uR ufs udf ux um hl1 hv1 hn1
  have g2 : ∀ r, r ≠ 8 → S3.regs r = S2.regs r := uR
  have hQ3 : KQ R b H L W st zp zc xp n xc s S3.mem := um ▸ hQ2
  refine kPC impl hap R hgr hmc hwb hQ3 (um ▸ hn1s) hl0
    (((natVal_frame hQ.fr (hxo _ (by omega))).symm.trans hv0).trans (natVal_frame hQ.fr (hxo _ hk.1)))
    (natNorm_frameB hQ.fr (hxo _ (by omega)) hn0) hl1
    (((natVal_frame hQ2.fr (hxo2 _ (by omega))).symm.trans hv1).trans
      (natVal_frame hQ2.fr (hxo2 _ (Nat.le_refl _))))
    (natNorm_frameB hQ2.fr (hxo2 _ (by omega)) hn1) hx150 hdf0 u1
    ((g2 4 (by decide)).trans sp2) ((g2 0 (by decide)).trans t0) ((g2 3 (by decide)).trans t3)
    ((g2 1 (by decide)).trans t1) ((g2 7 (by decide)).trans t7) ((g2 6 (by decide)).trans t6) u8
    ((g2 9 (by decide)).trans t9) ((g2 10 (by decide)).trans t10) ((g2 11 (by decide)).trans t11)
    ((g2 12 (by decide)).trans t12) ((g2 13 (by decide)).trans t13) ((g2 15 (by decide)).trans t15)
    ((g2 2 (by decide)).trans t2) ((g2 14 (by decide)).trans t14) ((g2 5 (by decide)).trans t5)
    (ufs.trans tfs) (udf.trans tdf) (ux.trans tx)
    fun S Lk bk hB => hK S lx0 lx1 Lk bk hB

end FvModexp.Amd64.Q.NatSqr
