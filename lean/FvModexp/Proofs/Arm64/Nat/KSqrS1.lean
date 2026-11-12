import FvModexp.Proofs.Arm64.Nat.KSqrS1c

/-!
# `karatsubaSqr` (arm64): `z1.abs = z1.abs.sqr(stk, tx.abs); z1.neg = true; clear(z)` (natmul.go:297-299), `KB2 → KB3`

`kS1clr`: from `0x1bc49c` (z1's header stored) the `memclrNoHeapPointers(zp, 16n)` call (live contract) to `KB3`;
`kS1st`: the stores of the square's header (`0x1bc488 → 0x1bc49c`); `kS1`: from `KB2` to the inner `nat.sqr`
(`ks_sqcallR`: result in `t`, reused) and on to `kS1st`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the stores of `z1`'s new header (`0x1bc488 → 0x1bc49c`), then `kS1clr` -/
theorem kS1st (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bc488)
    (hsp : S.sp = s.sp - 320#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 328#64)
    (h18 : S.regs 18 = s.regs 18)
    (hkm : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 (stLen s.mem st) n) S.mem) {l1 : Nat}
    (r0 : S.regs 0 = BitVec.ofNat 64 t) (r1 : S.regs 1 = BitVec.ofNat 64 l1)
    (r2 : S.regs 2 = BitVec.ofNat 64 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal S.mem t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm S.mem t l1)
    (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - 328) 376 true = true := by
    rw [hkm.fr.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have ht := hkm.tops
  have htw : t + 8 * kT n ≤ s.sp.toNat - W ∨ s.sp.toNat + 48 ≤ t := by
    have := ht.2.1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have ht48 : t + 8 * kT n ≤ 2 ^ 48 := ht.2.2.2.2.2
  clear ht
  have hl1' : l1 < 2 ^ 64 := by simp only [kn2] at hl1; omega
  unfold KGoal
  janus_run until [0x1bc49c]
  refine kS1mid impl hap R hmc _ rfl rfl ?_ ?_ ?_ hkm ?fr ?reg ?z1 hl1 hz1v hz1n hz0 hz2 hK
  case fr => janus_frame
  all_goals (try simp only [IntAt])
  all_goals janus_simp


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB2 → KB3`**: the loads and the inner `nat.sqr(z1 ← tx)` (`ks_sqcallR`, result reused in `t`), then `kS1st` -/
theorem kS1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    (ih : ∀ a, IH impl R (2 * n) (false, a))
    {Lk : List (Nat × Nat)} {bk tng ltx : Nat} (S : State)
    (hB : KB2 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk tng ltx)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  obtain ⟨-, z1b, z1c, z1d⟩ := hB.z1h
  obtain ⟨-, txb, txc, txd⟩ := hB.txh
  have q192 : S.mem.readLE (s.sp.toNat - 192) 8 = t := by rw [show s.sp.toNat - 192 = s.sp.toNat - 200 + 8 by omega]; exact z1b
  have q184 : S.mem.readLE (s.sp.toNat - 184) 8 = kT n := by rw [show s.sp.toNat - 184 = s.sp.toNat - 200 + 16 by omega]; exact z1c
  have q176 : S.mem.readLE (s.sp.toNat - 176) 8 = kT n := by rw [show s.sp.toNat - 176 = s.sp.toNat - 200 + 24 by omega]; exact z1d
  have q224 : S.mem.readLE (s.sp.toNat - 224) 8 = zp := by rw [show s.sp.toNat - 224 = s.sp.toNat - 232 + 8 by omega]; exact txb
  have q216 : S.mem.readLE (s.sp.toNat - 216) 8 = ltx := by rw [show s.sp.toNat - 216 = s.sp.toNat - 232 + 16 by omega]; exact txc
  have q208 : S.mem.readLE (s.sp.toNat - 208) 8 = zc := by rw [show s.sp.toNat - 208 = s.sp.toNat - 232 + 24 by omega]; exact txd
  have q328 : S.mem.readLE (s.sp.toNat + 8) 8 = st := hkm.s1
  clear z1b z1c z1d txb txc txd
  have hltx := hB.hltx
  have hst : st + 24 ≤ 2 ^ 48 := hkm.sok.2.2.2.1
  obtain ⟨-, hzlive, hzw, -, hzs, -, -, -, hzh, hz48⟩ := hkm.zops
  obtain ⟨htl, htw, htg, htz, -, ht48⟩ := hkm.tops
  have htsep := hkm.tsep
  have hsc : kc2 (stLen s.mem st) n + kcS (stLen s.mem st) n ≤ ksqrC (stLen s.mem st) n := by
    have := kc7_le (ℓ := stLen s.mem st) h80; unfold kc7 kc6 kc5 kc4 kc3 at this; omega
  have hxacc : S.mem.accessible zp (8 * ltx) false = true := by
    obtain ⟨-, -, hacc, -⟩ := hzlive (by omega)
    exact Memory.accessible_sub _ hacc (Or.inr rfl) (Nat.le_refl _) (by simp only [kn2] at hltx; omega)
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - 328) 376 false = true := by
    rw [hkm.fr.accessible]; exact Memory.accessible_sub _ hw0 (Or.inl rfl) (by omega) (by omega)
  clear hw0
  have hz0 := hB.z0h; have hz2 := hB.z2h; have htv := hB.tv
  unfold KGoal
  janus_run [q192, q184, q176, q224, q216, q208, q328] until [0x1bb420]
  refine ks_sqcallR impl R hkm ih _ ?pcS ?sp ?g ?hm ?l4 ?l48 (zp' := t) (zl' := kT n) (zc' := kT n) (xp' := zp)
    (xl' := ltx) (xc' := zc) (by omega) (by simp only [kT, kn2]; omega) (by simp only [kT, kn2]; omega) (by omega)
    (by omega) (by simp only [kn2] at hltx; omega) (by omega) ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 hltx
    (by simp only [kn2] at hltx; omega) hzc40 hxacc (fun _ => ⟨hzh, hz48⟩)
    (fun _ => hzw.of_sub (by omega) (by simp only [kn2] at hltx; omega)) (by simp only [kT, kn2]; omega) htl htw
    (fun _ => ⟨htg, htsep⟩) (fun _ _ => by unfold Apart at htz ⊢; simp only [kn2] at hltx; omega)
    (fun _ => hzs.sub (by simp only [kn2] at hltx; omega)) (by simp only [kT, kn2] at hltx ⊢; omega)
    (by unfold Apart at htz; simp only [kT, kn2] at htz ⊢; omega) (Or.inr ⟨Nat.le_refl _, by simp only [kT, kn2] at hltx ⊢; omega⟩)
    hsc ?cont
  case cont =>
    intro s2 Lk' bk' l' hr hreg hk hkm' e0 e1 e2 hval hnn hl2 hv2 hF hLF
    have e320 : (s.sp - 320#64).toNat = s.sp.toNat - 320 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hF' := hF
    simp only [winA, e320] at hF'
    rw [List.append_assoc] at hF'
    obtain ⟨-, -, -, -, -, -, hfw, -⟩ := (hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 : StkPre R L s W 48 st)
    have hstw : Outside st 24 (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
    have hfw' := hkm.stk.2.2.1
    simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfw' htw
    have hlc := hkm.sok.2.2.2.2.2.1
    have htw2 : t + 8 * (2 * ltx) ≤ s.sp.toNat - W ∨ s.sp.toNat + 48 ≤ t := by
      simp only [kT, kn2] at htw hltx; omega
    have hrd : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat + 48 → s2.mem.readLE x m = S.mem.readLE x m :=
      fun x m h1 h2 => hkm.rdW (k := W - 320) (a := 64) (by omega) (Nat.le_refl _) hF' h1 h2
        (by simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
    refine kS1st impl hap R hmc s2 ?pc2 ?sp2 ?g2 ?f2 ?x2 hkm' e0 e1 e2 (by simp only [kn2] at hltx ⊢; omega)
      (by rw [hval, htv]) hnn (hz0.keep fun x m h1 h2 => hrd x m (by omega) (by omega))
      (hz2.keep fun x m h1 h2 => hrd x m (by omega) (by omega)) hK
    case pc2 => rw [hr]; rfl
    case sp2 => rw [hk.1]
    case g2 => rw [hk.2.1]; janus_simp
    case f2 => rw [hk.2.2.1]; janus_simp
    case x2 => rw [hk.2.2.2]; janus_simp
  case pcS => rfl
  case hm => rfl
  all_goals janus_simp

end FvModexp.Arm64.NatSqr
