import FvModexp.Proofs.Amd64.NatQ.KSqrB

set_option autoImplicit false

/-!
# [amd64 port (divmc s39) of the Q-form Arm64/NatQ/KSqrS1c.lean — TIGHT COSTS] `karatsubaSqr` (amd64): `clear(z)` (natmul.go:299), the end of `KB2 → KB3`

`kS1clr`: from `0x5f262a` (z1's header and sign stored) the `memclrNoHeapPointers(zp, 16n)` call (live contract,
callee `RSP = SP - 320`, return `0x5f2649` pushed) to `KB3`; `kS1mid`: the same from the memory before the header stores.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after the `memclrNoHeapPointers` call (memory `w`; the return address pushed at `SP - 320`): `KB3` -/
theorem kS1post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hkm : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 n) M) {l1 : Nat}
    (hz1 : IntAt M ((s.regs 4).toNat - 200) 1 t l1 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal M t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm M t l1)
    (hz0 : Z0H s M zp zc n) (hz2 : Z2H s M zp zc n) {v : Nat} {w : Memory}
    (hFc : MemFrame (M.writeLE ((s.regs 4).toNat - 320) 8 v) w
      (R.rt ++ [((s.regs 4).toNat - 320 - 4096, (s.regs 4).toNat - 320),
        ((s.regs 4).toNat - 320 + 8, (s.regs 4).toNat - 320 + 8 + 16)] ++ [(zp, zp + 2 * n * 8)]))
    (hLFc : LiveFrame (M.writeLE ((s.regs 4).toNat - 320) 8 v) w Lk [(zp, zp + 2 * n * 8)])
    (hreg : w.regions = M.regions)
    (hinvw : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk w)) (hz : Mem.Zeroed w zp (2 * n * 8))
    (S' : State) (hA : KAt s S' 0x5f2649) (hm : S'.mem = w) :
    KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk bk l1 := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  rw [show 2 * n * 8 = 8 * (2 * n) by omega] at hFc hLFc hz
  have hkmP := hkm.push v
  obtain ⟨htlive, htw, -, htz, -, ht48⟩ := hkm.tops
  have hzw : Outside zp (8 * zc) (win s W 48) := hkm.zops.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  have hstw : Outside st 24 (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hsz : Apart st 24 zp (8 * zc) := (hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
  simp only [win, outside_cons, outside_nil, and_true] at htw hstw
  unfold Apart at htz hsz
  have hF1 : MemFrame (M.writeLE ((s.regs 4).toNat - 320) 8 v) w (R.rt ++ [((s.regs 4).toNat - 320 - 4096,
      (s.regs 4).toNat - 320 + 24)] ++ [(zp, zp + 8 * (2 * n))]) :=
    hFc.mono fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  have hsbC : StackBackL R Lk Lk st (M.writeLE ((s.regs 4).toNat - 320) 8 v) w ∧
      stCap w st = stCap (M.writeLE ((s.regs 4).toNat - 320) 8 v) st := by
    refine stackBack_keepC hkmP.sok (ws := [((s.regs 4).toNat - 320 - 4096, (s.regs 4).toNat - 320 + 24)] ++
      [(zp, zp + 8 * (2 * n))]) ?_
      (FvModexp.LiveFrame.mono_ws hLFc fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ (LiveExt.refl R Lk)
    · rw [← List.append_assoc]; exact hF1
    · simp only [outside_append, outside_cons, outside_nil, and_true]; omega
  have hkm1 := hkmP.step (k := 4096) (a := 24) (by omega) (by omega) (ws := [(zp, zp + 8 * (2 * n))])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩)
    hF1 hLFc (by rw [hreg]; simp only [Janus.Arm64.Memory.regions_writeLE]) (LiveExt.refl R Lk) (c := 0)
    (Or.inr ⟨by omega, hsbC.2⟩) (by have := hkm.spk; omega) hinvw hsbC.1
  rw [Nat.add_zero] at hkm1
  have hrd : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat + 48 → w.readLE x m = M.readLE x m :=
    fun x m h1 h2 => (hkmP.rdW (k := 4096) (a := 24) (by omega) (by omega) hF1 h1 h2
      (by simp only [outside_cons, outside_nil, and_true]; omega)).trans (pushRd (by omega))
  have htH : Held R Lk t (8 * kT n) := hkm.scr.held
  have hrt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → w.readLE x m = M.readLE x m :=
    fun x m h1 h2 => (Held.readLE2 (htH.sub h1 h2) hFc hLFc
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)).trans (pushRd (by omega))
  subst hm
  refine ⟨hA, hkm1, hz1.keep fun x m h1 h2 => hrd x m (by omega) (by omega), hl1,
    ?_, ?_, hz0.keep fun x m h1 h2 => hrd x m (by omega) (by omega),
    hz2.keep fun x m h1 h2 => hrd x m (by omega) (by omega), ?_⟩
  · show natVal S'.mem t l1 = _
    rw [← hz1v]; unfold natVal; exact hrt _ _ (Nat.le_refl _) (by simp only [kT, kn2] at hl1 ⊢; omega)
  · show NatNorm S'.mem t l1
    rcases hz1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hrt _ _ (by omega) (by simp only [kT, kn2] at hl1 ⊢; omega)]
  · show natVal S'.mem zp (2 * n) = 0
    unfold natVal; exact FvModexp.readLE_of_zeroed hz _ _ (Nat.le_refl _) (Nat.le_refl _)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem kS1clr (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State) (hA : KAt s S 0x5f262a)
    (hkm : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 n) S.mem) {l1 : Nat}
    (hz1 : IntAt S.mem ((s.regs 4).toNat - 200) 1 t l1 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal S.mem t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm S.mem t l1)
    (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibSqr.names
  have hmc' := MemclrNoHeapPointersLive64.of_codeIn hc hmc
  clear hc
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hA
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, hzal, hzh, hz48⟩ := hkm.zops
  have hsv : RunIface.Serves R := hkm.pre.2.2.1
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [zp, 8 * (2 * n)] := hsv.2.2.1 _ _ (by omega)
  have hzacc : S.mem.accessible zp (8 * (2 * n)) true = true := by
    obtain ⟨-, -, hacc, -⟩ := hzlive (by omega); exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hzH : InRanges zp (8 * (2 * n)) Lk ∨ Outside zp (8 * (2 * n)) R.rt := hzh.sub (by omega) (by omega)
  have hzg' : Apart zp (8 * (2 * n)) ((s.regs 14).toNat + 16) 8 := by
    simp only [guard] at hzg; unfold Apart at hzg ⊢; omega
  have hzw' : zp + 8 * (2 * n) ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  have hgQ := hkm.grd
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := hkm.pre.1
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3
  have hg2' : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hkm.fr.accessible]; exact hg2
  have hg3' : S.mem.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 320 := by rw [hgQ]; omega
  have hga1 : (s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 320 - 4096 ∨ (s.regs 4).toNat - 296 ≤ (s.regs 14).toNat + 16 := by
    unfold Apart at hga; omega
  clear hg2 hg3
  have hL1 := hkm.lsep
  have hinv := hkm.inv
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := by rw [hkm.fr.accessible]; exact hw0
  clear hw0
  have q24 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = 2 * n := hkm.s3
  have q16 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = zp := hkm.s2
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KGoal
  have hstw : Outside st 24 (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hsz : Apart st 24 zp (8 * zc) := (hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
  have bxT := IntAS.Box.mk (And.intro hkm.tops (And.intro hstw hsz))
  clear hstw hsz hzlive hzw hzg hzh hsv hgQ hga hgr
  have hok' : R.ok (cA "runtime.memclrNoHeapPointers") [zp, 2 * n * 8] := by rw [show 2 * n * 8 = 8 * (2 * n) by omega]; exact hok
  have hzH' : InRanges zp (2 * n * 8) Lk ∨ Outside zp (2 * n * 8) R.rt := by rw [show 2 * n * 8 = 8 * (2 * n) by omega]; exact hzH
  janus64_run [q24, q16, hsp'] until [0x5f2649] calls [hmc' Lk bk]
  janus_grab 4096 as hFc
  janus_grab Mem.Zeroed as hz
  janus_grab LiveFrame as hLFc
  refine hK _ Lk bk l1 (kS1post hkm hz1 hl1 hz1v hz1n hz0 hz2 hFc hLFc ?_ ?_ hz _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ rfl)
  all_goals (try janus64_simp)
  all_goals first | exact hfs | janus_assumption

/-- `kS1clr` from the facts before the header stores (memory `Q`) and the frame of the stores -/
theorem kS1mid (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {Q : Memory} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hA : KAt s S 0x5f262a)
    (hkm : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 n) Q)
    (hfr : MemFrame Q S.mem [((s.regs 4).toNat - 200, (s.regs 4).toNat - 168)]) (hreg : S.mem.regions = Q.regions) {l1 : Nat}
    (hz1 : IntAt S.mem ((s.regs 4).toNat - 200) 1 t l1 (kT n)) (hl1 : l1 ≤ 2 * kn2 n)
    (hz1v : natVal Q t l1 = kD s xp n * kD s xp n) (hz1n : NatNorm Q t l1)
    (hz0 : Z0H s Q zp zc n) (hz2 : Z2H s Q zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 : Nat),
      KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have htw : t + 8 * kT n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ t := by
    have := hkm.tops.2.1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hk : ∀ x m, (x + m ≤ (s.regs 4).toNat - 200 ∨ (s.regs 4).toNat - 168 ≤ x) → S.mem.readLE x m = Q.readLE x m :=
    fun x m h => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hl1' := hl1; simp only [kn2] at hl1'
  refine kS1clr impl hap R hmc hx150 hdf0 S hA (hkm.store (ws := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 168)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg)
    hz1 hl1 ?_ ?_ (hz0.keep fun x m h1 h2 => hk x m (by omega)) (hz2.keep fun x m h1 h2 => hk x m (by omega)) hK
  · rw [← hz1v]; unfold natVal; exact hk _ _ (by simp only [kT, kn2] at htw; omega)
  · rcases hz1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hk _ _ (by simp only [kT, kn2] at htw; omega)]

end FvModexp.Amd64.Q.NatSqr
