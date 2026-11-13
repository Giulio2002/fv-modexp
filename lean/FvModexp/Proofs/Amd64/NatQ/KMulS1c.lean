import FvModexp.Proofs.Amd64.NatQ.KMulB

set_option autoImplicit false

/-!
# [amd64 port (divmc s50) of the Q-form Arm64/NatQ/KMulS1c.lean — TIGHT COSTS] `karatsuba` (amd64): `clear(z)` (natmul.go:212), the end of `KM2b → KM3`

`kS1clr`: from `0x5f21a7` (the inner product returned) the `memclrNoHeapPointers(zp, 16n)` call (live contract,
callee `RSP = SP - 8`, return `0x5f21c6` pushed at `RSP - 456`) to `KM3`; `kS1post`: the facts after the call.
(Mechanics adapted from this repo's amd64 `KSqrS1c`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (IntAt pushRd)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after the `memclrNoHeapPointers` call (memory `w`; the return address pushed at `RSP - 456`): `KM3` -/
theorem kS1post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hkm : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc3 n) M)
    {ng l1 : Nat} (hz1 : IntAt M ((s.regs 4).toNat - 264) ng t l1 (kT n)) (hng : ng ≤ 1) (hcan : ng = 1 → 0 < l1)
    (hl1 : l1 ≤ 2 * kh n)
    (hz1v : sgnV ng (natVal M t l1) =
      ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int)))
    (hz1n : NatNorm M t l1) (hz0 : Z0H s M zp zc n) (hz2 : Z2H s M zp zc n) {v : Nat} {w : Memory}
    (hFc : MemFrame (M.writeLE ((s.regs 4).toNat - 456) 8 v) w
      (R.rt ++ [((s.regs 4).toNat - 456 - 4096, (s.regs 4).toNat - 456),
        ((s.regs 4).toNat - 456 + 8, (s.regs 4).toNat - 456 + 8 + 16)] ++ [(zp, zp + 2 * n * 8)]))
    (hLFc : LiveFrame (M.writeLE ((s.regs 4).toNat - 456) 8 v) w Lk [(zp, zp + 2 * n * 8)])
    (hreg : w.regions = M.regions)
    (hinvw : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk w)) (hz : Mem.Zeroed w zp (2 * n * 8))
    (S' : State) (hA : KNAt s S' 0x5f21c6) (hm : S'.mem = w) :
    KM3 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk bk ng l1 := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, -, -, -, -, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  rw [show 2 * n * 8 = 8 * (2 * n) by omega] at hFc hLFc hz
  have hkmP := hkm.push v
  obtain ⟨htlive, htw, -, htz, -, -, ht48⟩ := hkm.tops
  have hstw : Outside st 24 (win s W 72) := hkm.F.stk.2.2.1
  have hsz : Apart st 24 zp (8 * zc) := hkm.F.zs.1
  have hzw : zp + 8 * zc ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 72 ≤ zp := by
    have := hkm.F.zw; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  simp only [win, outside_cons, outside_nil, and_true] at htw hstw
  unfold Apart at htz hsz
  have hF1 : MemFrame (M.writeLE ((s.regs 4).toNat - 456) 8 v) w (R.rt ++ [((s.regs 4).toNat - 456 - 4096,
      (s.regs 4).toNat - 456 + 24)] ++ [(zp, zp + 8 * (2 * n))]) :=
    hFc.mono fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  have hsbC : StackBackL R Lk Lk st (M.writeLE ((s.regs 4).toNat - 456) 8 v) w ∧
      stCap w st = stCap (M.writeLE ((s.regs 4).toNat - 456) 8 v) st := by
    refine NatSqr.stackBack_keepC hkmP.sok (ws := [((s.regs 4).toNat - 456 - 4096, (s.regs 4).toNat - 456 + 24)] ++
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
  have hrd : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat + 72 → w.readLE x m = M.readLE x m :=
    fun x m h1 h2 => (hkmP.rdW (k := 4096) (a := 24) (by omega) (by omega) hF1 h1 h2
      (by simp only [outside_cons, outside_nil, and_true]; omega)).trans (pushRd (by omega))
  have htH : Held R Lk t (8 * kT n) := hkm.scr.held
  have hrt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → w.readLE x m = M.readLE x m :=
    fun x m h1 h2 => (Held.readLE2 (htH.sub h1 h2) hFc hLFc
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)).trans (pushRd (by omega))
  have hkh : kh n = (n + 1) / 2 := rfl
  have htv : natVal w t l1 = natVal M t l1 := by
    unfold natVal; exact hrt _ _ (Nat.le_refl _) (by simp only [kT]; omega)
  subst hm
  refine ⟨hA, hkm1, NatSqr.IntAt.keep hz1 fun x m h1 h2 => hrd x m (by omega) (by omega), hng, hcan, hl1, ?_, ?_,
    NatSqr.IntAt.keep hz0 fun x m h1 h2 => hrd x m (by omega) (by omega),
    NatSqr.IntAt.keep hz2 fun x m h1 h2 => hrd x m (by omega) (by omega), ?_⟩
  · rw [htv]; exact hz1v
  · rcases hz1n with h0 | h0
    · exact Or.inl h0
    · by_cases hl0 : l1 = 0
      · exact Or.inl hl0
      · right; rwa [hrt _ _ (by omega) (by simp only [kT]; omega)]
  · unfold natVal; exact FvModexp.readLE_of_zeroed hz _ _ (Nat.le_refl _) (Nat.le_refl _)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- **`0x5f21a7 → KM3`**: `clear(z)` = `memclrNoHeapPointers(zp, 16n)` -/
theorem kS1clr (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hA : KNAt s S 0x5f21a7)
    (hkm : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc3 n) S.mem)
    {ng l1 : Nat} (hz1 : IntAt S.mem ((s.regs 4).toNat - 264) ng t l1 (kT n)) (hng : ng ≤ 1)
    (hcan : ng = 1 → 0 < l1) (hl1 : l1 ≤ 2 * kh n)
    (hz1v : sgnV ng (natVal S.mem t l1) =
      ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int)))
    (hz1n : NatNorm S.mem t l1)
    (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' ng l1 : Nat),
      KM3 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibMul.names
  have hmc' := MemclrNoHeapPointersLive64.of_codeIn hc hmc
  clear hc
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hA
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, -, -, -, -, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, hzal, hzh, hz48⟩ := hkm.zops
  have F := hkm.F
  have hsv : RunIface.Serves R := F.sv
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [zp, 8 * (2 * n)] := hsv.2.2.1 _ _ (by omega)
  have hzacc : S.mem.accessible zp (8 * (2 * n)) true = true := by
    obtain ⟨-, -, hacc, -⟩ := hzlive (by omega)
    exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hzH : InRanges zp (8 * (2 * n)) Lk ∨ Outside zp (8 * (2 * n)) R.rt := hzh.sub (by omega) (by omega)
  have hzg' : Apart zp (8 * (2 * n)) ((s.regs 14).toNat + 16) 8 := by
    simp only [NatSqr.guard] at hzg; unfold Apart at hzg ⊢; omega
  have hzw' : zp + 8 * (2 * n) ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 72 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  have hgQ := hkm.grd
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := F.env
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3
  have hg2' : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hkm.fr.accessible]; exact hg2
  have hg3' : S.mem.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 456 := by rw [hgQ]; omega
  have hga1 : (s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 456 - 4096 ∨
      (s.regs 4).toNat - 432 ≤ (s.regs 14).toNat + 16 := by
    unfold Apart at hga; omega
  clear hg2 hg3
  have hL1 := hkm.lsep
  have hinv := hkm.inv
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := F.env.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := by rw [hkm.fr.accessible]; exact hw0
  clear hw0
  have q48 : S.mem.readLE ((s.regs 4).toNat + 48) 8 = 2 * n := hkm.s3
  have q40 : S.mem.readLE ((s.regs 4).toNat + 40) 8 = zp := hkm.s2
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KNGoal
  clear F hzlive hzw hzg hzh hsv hgQ hga hgr
  have hok' : R.ok (cA "runtime.memclrNoHeapPointers") [zp, 2 * n * 8] := by
    rw [show 2 * n * 8 = 8 * (2 * n) by omega]; exact hok
  have hzH' : InRanges zp (2 * n * 8) Lk ∨ Outside zp (2 * n * 8) R.rt := by
    rw [show 2 * n * 8 = 8 * (2 * n) by omega]; exact hzH
  janus64_run [q48, q40, hsp'] until [0x5f21c6] calls [hmc' Lk bk]
  janus_grab 4096 as hFc
  janus_grab Mem.Zeroed as hz
  janus_grab LiveFrame as hLFc
  refine hK _ Lk bk ng l1 (kS1post hkm hz1 hng hcan hl1 hz1v hz1n hz0 hz2 hFc hLFc ?_ ?_ hz _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ rfl)
  all_goals (try janus64_simp)
  all_goals first | exact hfs | janus_assumption

end FvModexp.Amd64.Q.NatMul
