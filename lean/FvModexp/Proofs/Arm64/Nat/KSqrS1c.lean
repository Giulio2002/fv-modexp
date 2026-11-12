import FvModexp.Proofs.Arm64.Nat.KSqrB

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
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem kS1clr (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bc49c)
    (hsp : S.sp = s.sp - 320#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 328#64)
    (h18 : S.regs 18 = s.regs 18)
    (hkm : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 (stLen s.mem st) n) S.mem) {l1 : Nat}
    (hz1 : IntAt S.mem (s.sp.toNat - 200) 1 t l1 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal S.mem t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm S.mem t l1)
    (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibSqr.names
  have hmc' := MemclrNoHeapPointersLive.of_codeIn hc hmc
  clear hc
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, hzal, hzh, hz48⟩ := hkm.zops
  have hsv : RunIface.Serves R := hkm.pre.2.2.1
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [zp, 8 * (2 * n)] := hsv.2.2.1 _ _ (by omega)
  have hzacc : S.mem.accessible zp (8 * (2 * n)) true = true := by
    obtain ⟨-, -, hacc, -⟩ := hzlive (by omega); exact Memory.accessible_mono _ hacc (by omega) (by omega)
  have hzH : InRanges zp (8 * (2 * n)) Lk ∨ Outside zp (8 * (2 * n)) R.rt := hzh.sub (by omega) (by omega)
  have hzg' : Apart zp (8 * (2 * n)) ((s.regs 28).toNat + 16) 8 := by
    simp only [guard] at hzg; unfold Apart at hzg ⊢; omega
  have hzw' : zp + 8 * (2 * n) ≤ s.sp.toNat - W ∨ s.sp.toNat + 48 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  have hgQ := hkm.grd
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := hkm.pre.1
  have hg2' : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hkm.fr.accessible]; exact hg2
  have hg3' : S.mem.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 320 := by rw [hgQ]; omega
  have hga1 : (s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 320 - 4096 ∨ s.sp.toNat - 320 - 8 ≤ (s.regs 28).toNat + 16 := by
    unfold Apart at hga; omega
  have hga2 : (s.regs 28).toNat + 16 ≤ s.sp.toNat - 320 ∨ s.sp.toNat - 320 + 8 ≤ (s.regs 28).toNat := by
    unfold Apart at hga; omega
  clear hg2 hg3
  have hL1 := hkm.lsep
  have hinv := hkm.inv
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - W) (W + 48) true = true := by rw [hkm.fr.accessible]; exact hw0
  clear hw0
  have q344 : S.mem.readLE (s.sp.toNat + 24) 8 = 2 * n := hkm.s3
  have q336 : S.mem.readLE (s.sp.toNat + 16) 8 = zp := hkm.s2
  unfold KGoal
  have htops := hkm.tops
  have hstw : Outside st 24 (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hsz : Apart st 24 zp (8 * zc) := (hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
  janus_run [q344, q336] until [0x1bc4ac] calls [hmc' Lk bk]
  rename_i jk fl vv w ex ep hFc hLFc hinvw hz
  have hreg : w.regions = S.mem.regions := by janus_assumption
  obtain ⟨hlive, htw, -, htz, -, ht48⟩ := htops
  simp only [win, outside_cons, outside_nil, and_true] at htw hstw
  unfold Apart at htz hsz
  have hF1 : MemFrame S.mem w (R.rt ++ [(s.sp.toNat - 320 - 4096, s.sp.toNat - 320 - 8),
      (s.sp.toNat - 320 + 8, s.sp.toNat - 320 + 24)] ++ [(zp, zp + 8 * (2 * n))]) :=
    hFc.mono fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, ho.1.2.1, by omega⟩, ho.2⟩
  have hsb : StackBack R Lk Lk st S.mem w := by
    refine stackBack_keep' hkm.sok (ws := [(s.sp.toNat - 320 - 4096, s.sp.toNat - 320 - 8),
      (s.sp.toNat - 320 + 8, s.sp.toNat - 320 + 8 + 16)] ++ [(zp, zp + 8 * (2 * n))]) ?_
      (FvModexp.LiveFrame.mono_ws hLFc fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ (LiveExt.refl R Lk)
    · rw [← List.append_assoc]; exact hFc
    · simp only [outside_append, outside_cons, outside_nil, and_true]; omega
  have hkm1 := hkm.step (k := 4096) (a := 24) (by omega) (by omega) (ws := [(zp, zp + 8 * (2 * n))])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩)
    hF1 hLFc hreg (LiveExt.refl R Lk) (c := 0) (by omega) hinvw hsb
  rw [Nat.add_zero] at hkm1
  have hrd : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat + 48 → w.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 => hkm.rdW (k := 4096) (a := 24) (by omega) (by omega) hF1 h1 h2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have htH : Held R Lk t (8 * kT n) := hkm.scr.held
  have hrt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → w.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 => Held.readLE2 (htH.sub h1 h2) hFc hLFc
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine hK _ Lk bk l1 ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hkm1, hz1.keep fun x m h1 h2 => hrd x m (by omega) (by omega), hl1,
    ?_, ?_, hz0.keep fun x m h1 h2 => hrd x m (by omega) (by omega),
    hz2.keep fun x m h1 h2 => hrd x m (by omega) (by omega), ?_⟩
  · rfl
  · rfl
  · simp only [retStateX, callRegs_apply]; simp; exact h28
  · simp only [retStateX, callRegs_apply]; simp; exact h29
  · simp only [retStateX, callRegs_apply]; simp; exact h18
  · show natVal w t l1 = _
    rw [← hz1v]; unfold natVal; exact hrt _ _ (Nat.le_refl _) (by simp only [kT, kn2] at hl1 ⊢; omega)
  · show NatNorm w t l1
    rcases hz1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hrt _ _ (by omega) (by simp only [kT, kn2] at hl1 ⊢; omega)]
  · show natVal w zp (2 * n) = 0
    unfold natVal; exact FvModexp.readLE_of_zeroed hz _ _ (Nat.le_refl _) (Nat.le_refl _)

/-- `kS1clr` from the facts before the header stores (memory `Q`) and the frame of the stores -/
theorem kS1mid (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {Q : Memory} (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bc49c)
    (hsp : S.sp = s.sp - 320#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 328#64)
    (h18 : S.regs 18 = s.regs 18)
    (hkm : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 (stLen s.mem st) n) Q)
    (hfr : MemFrame Q S.mem [(s.sp.toNat - 200, s.sp.toNat - 168)]) (hreg : S.mem.regions = Q.regions) {l1 : Nat}
    (hz1 : IntAt S.mem (s.sp.toNat - 200) 1 t l1 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal Q t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm Q t l1)
    (hz0 : Z0H s Q zp zc n) (hz2 : Z2H s Q zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have htw : t + 8 * kT n ≤ s.sp.toNat - W ∨ s.sp.toNat + 48 ≤ t := by
    have := hkm.tops.2.1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hk : ∀ x m, (x + m ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 168 ≤ x) → S.mem.readLE x m = Q.readLE x m :=
    fun x m h => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hl1' := hl1; simp only [kn2] at hl1'
  refine kS1clr impl hap R hmc S hpc hsp h28 h29 h18 (hkm.store (ws := [(s.sp.toNat - 200, s.sp.toNat - 168)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg)
    hz1 hl1 ?_ ?_ (hz0.keep fun x m h1 h2 => hk x m (by omega)) (hz2.keep fun x m h1 h2 => hk x m (by omega)) hK
  · rw [← hz1v]; unfold natVal; exact hk _ _ (by simp only [kT, kn2] at htw; omega)
  · rcases hz1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hk _ _ (by simp only [kT, kn2] at htw; omega)]

end FvModexp.Arm64.NatSqr
