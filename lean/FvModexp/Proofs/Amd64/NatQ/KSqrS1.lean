import FvModexp.Proofs.Amd64.NatQ.KSqrS1c

/-!
# [amd64 port (divmc s39) of the Q-form Arm64/NatQ/KSqrS1.lean — TIGHT COSTS] `karatsubaSqr` (amd64): `z1.abs = z1.abs.sqr(stk, tx.abs); z1.neg = true; clear(z)` (natmul.go:297-299), `KB2 → KB3`

`kS1st`: the stores of the square's header and sign (`0x5f2610 → 0x5f262a`), then `kS1mid`; `kS1`: from `KB2` the
loads and the inner `nat.sqr` (`0x5f260b`, return `0x5f2610` pushed at `SP - 320`; `ks_sqcallR`: result in `t`,
reused) and on to `kS1st`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the stores of `z1`'s new header and sign (`0x5f2610 → 0x5f262a`), then `kS1mid` -/
theorem kS1st (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hA : KAt s S 0x5f2610)
    (hkm : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 n) S.mem) {l1 : Nat}
    (r0 : S.regs 0 = BitVec.ofNat 64 t) (r1 : S.regs 3 = BitVec.ofNat 64 l1)
    (r2 : S.regs 1 = BitVec.ofNat 64 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal S.mem t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm S.mem t l1)
    (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hA
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have ht := hkm.tops
  have htw : t + 8 * kT n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ t := by
    have := ht.2.1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have ht48 : t + 8 * kT n ≤ 2 ^ 48 := ht.2.2.2.2.2
  clear ht
  have hl1' : l1 < 2 ^ 64 := by simp only [kn2] at hl1; omega
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KGoal
  janus64_run [hsp'] until [0x5f262a]
  refine kS1mid impl hap R hmc hx150 hdf0 _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ hkm ?fr ?reg ?z1 hl1 hz1v hz1n hz0 hz2 hK
  case fr => janus_frame
  all_goals (try simp only [IntAt])
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB2 → KB3`**: the loads and the inner `nat.sqr(z1 ← tx)` (`ks_sqcallR`, result reused in `t`), then `kS1st` -/
theorem kS1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    (ih : ∀ a, IH impl R H (2 * n) (false, a)) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {Lk : List (Nat × Nat)} {bk tng ltx : Nat} (S : State)
    (hB : KB2 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk tng ltx)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  obtain ⟨-, z1b, z1c, z1d⟩ := hB.z1h
  obtain ⟨-, txb, txc, txd⟩ := hB.txh
  have q192 : S.mem.readLE ((s.regs 4).toNat - 192) 8 = t := by
    rw [show (s.regs 4).toNat - 192 = (s.regs 4).toNat - 200 + 8 by omega]; exact z1b
  have q184 : S.mem.readLE ((s.regs 4).toNat - 184) 8 = kT n := by
    rw [show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 200 + 16 by omega]; exact z1c
  have q176 : S.mem.readLE ((s.regs 4).toNat - 176) 8 = kT n := by
    rw [show (s.regs 4).toNat - 176 = (s.regs 4).toNat - 200 + 24 by omega]; exact z1d
  have q224 : S.mem.readLE ((s.regs 4).toNat - 224) 8 = zp := by
    rw [show (s.regs 4).toNat - 224 = (s.regs 4).toNat - 232 + 8 by omega]; exact txb
  have q216 : S.mem.readLE ((s.regs 4).toNat - 216) 8 = ltx := by
    rw [show (s.regs 4).toNat - 216 = (s.regs 4).toNat - 232 + 16 by omega]; exact txc
  have q208 : S.mem.readLE ((s.regs 4).toNat - 208) 8 = zc := by
    rw [show (s.regs 4).toNat - 208 = (s.regs 4).toNat - 232 + 24 by omega]; exact txd
  have q8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = st := hkm.s1
  clear z1b z1c z1d txb txc txd
  have hltx := hB.hltx
  have hst : st + 24 ≤ 2 ^ 48 := hkm.sok.2.2.2.1
  obtain ⟨-, hzlive, hzw, -, hzs, -, -, -, hzh, hz48⟩ := hkm.zops
  obtain ⟨htl, htw, htg, htz, -, ht48⟩ := hkm.tops
  obtain ⟨htt, -⟩ := hkm.ttls
  have htsep := hkm.tsep
  have hsc : kc2 n + kcS n ≤ ksqrCQ n := by
    have := kc7_le h80; unfold kc7 kc6 kc5 kc4 kc3 at this; omega
  have hxacc : S.mem.accessible zp (8 * ltx) false = true := by
    obtain ⟨-, -, hacc, -⟩ := hzlive (by omega)
    exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (Nat.le_refl _) (by simp only [kn2] at hltx; omega)
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hz0 := hB.z0h; have hz2 := hB.z2h; have htv := hB.tv
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- the facts at the call memory (the return address `0x5f2610` pushed at `SP - 320`)
  have hkmP := hkm.push 0x5f2610
  have hzwN : zp + 8 * zc ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  have htwN : t + 8 * kT n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ t := by
    simp only [win, outside_cons, outside_nil, and_true] at htw; omega
  have hxaccP : (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f2610).accessible zp (8 * ltx) false = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hxacc
  have htlP := pushLive (q := (s.regs 4).toNat - 320) (v := 0x5f2610) htl
  have htsepP := hkm.pushSep 0x5f2610 htsep
  have hzsP := hkm.pushSep 0x5f2610 (hzs.sub (k' := 8 * ltx) (by simp only [kn2] at hltx; omega))
  have htvP : natVal (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f2610) zp ltx = natVal S.mem zp ltx := by
    unfold natVal; exact pushRd (by simp only [kn2] at hltx; omega)
  unfold KGoal
  janus64_run [q192, q184, q176, q224, q216, q208, q8, hsp'] until [0x5f0fe0]
  refine ks_sqcallR impl R hkmP ih _ ?pcS ?sp ?g ?hm ?fs (ra := 0x5f2610) ?rv (by decide) ?x15 ?df ?h5 hx150 hdf0 (zp' := t) (zl' := kT n) (zc' := kT n) (xp' := zp)
    (xl' := ltx) (xc' := zc) (by omega) (by simp only [kT, kn2]; omega) (by simp only [kT, kn2]; omega) (by omega)
    (by omega) (by simp only [kn2] at hltx; omega) (by omega) ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 hltx
    (by simp only [kn2] at hltx; omega) hzc40 hxaccP (fun _ => ⟨hzh, hz48⟩)
    (fun _ => hzw.of_sub (by omega) (by simp only [kn2] at hltx; omega)) (by simp only [kT, kn2]; omega) htlP htw
    (fun _ => ⟨htg, htt, htsepP⟩) (fun _ _ => by unfold Apart at htz ⊢; simp only [kn2] at hltx; omega)
    (fun _ => hzsP) (by simp only [kT, kn2] at hltx ⊢; omega)
    (by unfold Apart at htz; simp only [kT, kn2] at htz ⊢; omega) (Or.inr ⟨Nat.le_refl _, by simp only [kT, kn2] at hltx ⊢; omega⟩)
    hsc ?cont
  case cont =>
    intro s2 Lk' bk' l' hA2 hreg hkm' e0 e1 e2 hval hnn hl2 hv2 hF hLF
    have hF' := hF
    rw [List.append_assoc] at hF'
    have hstw : Outside st 24 (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
    have hfw' := hkmP.stk.2.2.1
    simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfw' htw
    have htw2 : t + 8 * (2 * ltx) ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ t := by
      simp only [kT, kn2] at htw hltx; omega
    have hrd : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat + 48 →
        s2.mem.readLE x m = S.mem.readLE x m :=
      fun x m h1 h2 => (hkmP.rdW (k := W - 320) (a := 64) (by omega) (Nat.le_refl _) hF' h1 h2
        (by simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)).trans
        (pushRd (by omega))
    refine kS1st impl hap R hmc hx150 hdf0 s2 hA2 hkm' e0 e1 e2 (by simp only [kn2] at hltx ⊢; omega)
      (by rw [hval, htvP, htv]) hnn (hz0.keep fun x m h1 h2 => hrd x m (by omega) (by omega))
      (hz2.keep fun x m h1 h2 => hrd x m (by omega) (by omega)) hK
  case pcS => rfl
  case hm => rfl
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega

end FvModexp.Amd64.Q.NatSqr
