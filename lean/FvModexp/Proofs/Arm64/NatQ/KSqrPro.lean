import FvModexp.Proofs.Arm64.NatQ.KSqrPA
import FvModexp.Proofs.Arm64.NatQ.KSqrPB
import FvModexp.Proofs.Arm64.NatQ.KSqrPC

/-!
# [Q-form copy of Arm64/Nat/KSqrPro.lean — TIGHT COSTS, divmc s34] `karatsubaSqr` (arm64): the whole prologue, entry → `KB1` (natmul.go:257-292)

`kPro` = `kPA` → `kLoop1` (`x0 = x[:n2].norm()`) → `kPB` → `kLoop2` (`x1 = x[n2:].norm()`) → `kPC` (`stk.nat` call).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

/-- `NatNorm` through a frame that avoids the top limb -/
theorem natNorm_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p l : Nat}
    (ho : Outside p (8 * l) rs) (hn : NatNorm m' p l) : NatNorm m p l := by
  rcases hn with h0 | h1
  · exact Or.inl h0
  · by_cases hl : l = 0
    · exact Or.inl hl
    right; rw [← h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h1

set_option maxRecDepth 20000 in
/-- **`karatsubaSqr`'s prologue**: entry → the state after `z1 := stk.nat(2·n2 + 1)` (`KB1`) -/
theorem kPro (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} (hpre : KPre R b H L W st zp (2 * n) zc xp n xc s) (hpc : s.pc = BitVec.ofNat 64 0x1bc2b0)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h1 : s.regs 1 = BitVec.ofNat 64 zp)
    (h2 : s.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : s.regs 3 = BitVec.ofNat 64 zc)
    (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 n) (h6 : s.regs 6 = BitVec.ofNat 64 xc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (S : State) (lx0 lx1 : Nat) (Lk : List (Nat × Nat)) (bk : Nat),
      KB1 R b H L W st zp zc xp n xc s lx0 lx1 (stW S.mem st + 8 * stLen s.mem st) S Lk bk →
      ReachesRet (LibSqr.program.link impl) ret S Q) :
    ReachesRet (LibSqr.program.link impl) ret s Q := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal, hb', ha, -⟩, -⟩, hW, -, -, -, h80, hxc, hxc40, hn12, hxacc, -, hxp48, hxw, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold ksqrW at hW
  have hk : kn2 n ≤ n ∧ 0 < kn2 n := by simp only [kn2]; omega
  refine kPA impl hpre hpc h0 h1 h2 h3 h4 h5 h6 ?_
  intro S1 p1 sp1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r28 r29 r18 hQ
  have hxo : ∀ k, k ≤ n → Outside xp (8 * k) [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)] :=
    fun k hk' => by simp only [outside_cons, outside_nil, and_true]; omega
  have hxo2 : ∀ k, k ≤ n - kn2 n → Outside (xp + 8 * kn2 n) (8 * k)
      [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)] :=
    fun k hk' => by simp only [outside_cons, outside_nil, and_true]; omega
  have hacc1 : S1.mem.accessible xp (8 * kn2 n) false = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hacc2 : S1.mem.accessible (xp + 8 * kn2 n) (8 * (n - kn2 n)) false = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hxacc (by omega) (by omega)
  refine kLoop1 impl ret Q S1.mem S1.regs S1.sp xp (kn2 n) (natVal S1.mem xp (kn2 n)) hacc1 (by omega)
    (by omega) r4 ?_ (kn2 n) S1 (Nat.le_refl _) p1 r8 (fun _ _ _ _ => rfl) rfl rfl rfl
  intro S' lx0 q1 q8 qR qsp qm hl0 hv0 hn0
  have g : ∀ r, r ≠ 8 → r ≠ 10 → r ≠ 11 → S'.regs r = S1.regs r := qR
  refine kPB impl (S := S') (qm ▸ hQ) hl0 q1 (qsp.trans sp1) ((g 0 (by decide) (by decide) (by decide)).trans r0)
    ((g 1 (by decide) (by decide) (by decide)).trans r1) ((g 2 (by decide) (by decide) (by decide)).trans r2)
    ((g 3 (by decide) (by decide) (by decide)).trans r3) ((g 4 (by decide) (by decide) (by decide)).trans r4)
    ((g 5 (by decide) (by decide) (by decide)).trans r5) ((g 6 (by decide) (by decide) (by decide)).trans r6)
    ((g 7 (by decide) (by decide) (by decide)).trans r7) q8 ((g 9 (by decide) (by decide) (by decide)).trans r9)
    ((g 28 (by decide) (by decide) (by decide)).trans r28) ((g 29 (by decide) (by decide) (by decide)).trans r29)
    ((g 18 (by decide) (by decide) (by decide)).trans r18) ?_
  intro S2 p2 sp2 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t28 t29 t18 qm2
  refine kLoop2 impl ret Q S1.mem S2.regs S2.sp (xp + 8 * kn2 n) (n - kn2 n)
    (natVal S1.mem (xp + 8 * kn2 n) (n - kn2 n)) hacc2 (by omega) (by omega) t11 ?_ (n - kn2 n) S2
    (Nat.le_refl _) p2 t5 (fun _ _ _ _ => rfl) rfl (qm2.trans qm) rfl
  intro S3 lx1 u1 u5 uR usp um hl1 hv1 hn1
  have g2 : ∀ r, r ≠ 5 → r ≠ 12 → r ≠ 13 → S3.regs r = S2.regs r := uR
  have hQ3 : KQ R b H L W st zp zc xp n xc s S3.mem := um ▸ hQ
  refine kPC impl hap R hgr hmc hwb hQ3 hl0
    (((natVal_frame hQ.fr (hxo _ (by omega))).symm.trans hv0).trans (natVal_frame hQ.fr (hxo _ hk.1)))
    (natNorm_frame hQ.fr (hxo _ (by omega)) hn0) hl1
    (((natVal_frame hQ.fr (hxo2 _ (by omega))).symm.trans hv1).trans (natVal_frame hQ.fr (hxo2 _ (Nat.le_refl _))))
    (natNorm_frame hQ.fr (hxo2 _ (by omega)) hn1) u1 (usp.trans sp2)
    ((g2 0 (by decide) (by decide) (by decide)).trans t0) ((g2 1 (by decide) (by decide) (by decide)).trans t1)
    ((g2 2 (by decide) (by decide) (by decide)).trans t2) ((g2 3 (by decide) (by decide) (by decide)).trans t3)
    ((g2 4 (by decide) (by decide) (by decide)).trans t4) u5 ((g2 6 (by decide) (by decide) (by decide)).trans t6)
    ((g2 7 (by decide) (by decide) (by decide)).trans t7) ((g2 8 (by decide) (by decide) (by decide)).trans t8)
    ((g2 9 (by decide) (by decide) (by decide)).trans t9) ((g2 10 (by decide) (by decide) (by decide)).trans t10)
    ((g2 11 (by decide) (by decide) (by decide)).trans t11) ((g2 28 (by decide) (by decide) (by decide)).trans t28)
    ((g2 29 (by decide) (by decide) (by decide)).trans t29) ((g2 18 (by decide) (by decide) (by decide)).trans t18)
    fun S Lk bk hB => hK S lx0 lx1 Lk bk hB

end FvModexp.Arm64.Q.NatSqr
