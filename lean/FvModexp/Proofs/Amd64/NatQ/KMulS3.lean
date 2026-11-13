import FvModexp.Proofs.Amd64.NatQ.KMulI
import FvModexp.Proofs.Amd64.NatQ.KMulMath
import FvModexp.Proofs.Common.OmegaOnly

set_option autoImplicit false

/-!
# [amd64 port (divmc s47) of the Q-form Arm64/NatQ/KMulS3.lean — TIGHT COSTS] `karatsuba` (amd64): `z2.mul(stk, x1, y1)` (natmul.go:214), `KM4 → KM5`

`kS3`: from `KM4` (`0x5f2210`) the argument setup (`AX = &z0`, `BX = stk`, `CX = &x0`, `DI = &y0`), the `CALL`
(return address `0x5f2210` pushed at `RSP - 456`) and the inner `(*Int).mul` (`kn_icallR`: the product is
written exactly into `z[2n2:2n2 + len x1 + len y1]`, zero before), then `KM5` at the return address `0x5f2210`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le natVal_zero_part tls pushRd pushLive
  pushFrame pushLF)
open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`KM4 → KM5`**: `z2.mul(stk, x1, y1)` (`0x5f2210 …`, `kn_icallR`) -/
theorem kS3 (impl : List Amd64.Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    (ih : ∀ j, IH impl R H (8 * n + 2) j) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} (S : State)
    (hB : KM4 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk ng l1 l0)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l2 : Nat),
      KM5 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 l0 l2 →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hkh : kh n = (n + 1) / 2 := rfl
  have hl0 := hkm.l1; have hm0 := hkm.m1
  -- the facts at the call memory (return address `0x5f2210` pushed at `RSP - 456`)
  have hkmP := hkm.push 0x5f2210
  obtain ⟨x1, x2, x3, x4⟩ := hkmP.x1h
  obtain ⟨y1, y2, y3, y4⟩ := hkmP.y1h
  obtain ⟨z1, z2, z3, z4⟩ := IntAt.pushK (sp := (s.regs 4).toNat) (v := 0x5f2210) hB.z2h (by omega) (by omega)
  obtain ⟨hxacc, hx48, hxH, hxc48, hxw, hxs, hzx, hxv, hxn⟩ := hkmP.halfX (o := kh n) (l := lx1) (by omega)
  obtain ⟨hyacc, hy48, hyH, hyc48, hyw, hys, hzy, hyv, hyn⟩ := hkmP.halfY (o := kh n) (l := ly1) (by omega)
  obtain ⟨-, -, -, -, -, -, hzlive, hzw, hzg, hzs⟩ := hkmP.partZ (o := 2 * kh n) (l := 2 * n - 2 * kh n) (by omega)
  rw [show zp + 8 * (2 * kh n) = zp + 16 * kh n by omega] at hzlive hzw hzg hzs
  obtain ⟨-, hzt0⟩ := hkmP.ttls
  have hzt : Apart (zp + 16 * kh n) (8 * (zc - 2 * kh n)) (tls s) 8 := by unfold Apart at hzt0 ⊢; omega
  have hzx0 := hkm.F.zx
  have hzy0 := hkm.F.zy
  have hsl : stLen (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) st + 4 * (lx1 + ly1) + 64 ≤ 2 ^ 16 := by
    rw [hkmP.slen]; have := hkmP.F.slb; simp only [StackNat.rnd, kT]; omega
  have hops : Ops R Lk (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) (s.regs 14).toNat (tls s) (win s W 72) st
      (hP (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 208))
      (hC (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 208))
      (hP (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 80))
      (hL (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 80))
      (hC (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 80))
      (hP (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 144))
      (hL (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 144))
      (hC (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 144)) := by
    simp only [hP, hL, hC, x2, x3, x4, y2, y3, y4, z2, z4]
    exact ⟨⟨by omega, by omega, by omega, fun _ => hxacc, fun _ => ⟨hxH, hxc48⟩, fun _ => ⟨hxw, hxs⟩⟩,
      ⟨by omega, by omega, by omega, fun _ => hyacc, fun _ => ⟨hyH, hyc48⟩, fun _ => ⟨hyw, hys⟩⟩,
      ⟨by omega, hzlive, hzw, fun _ => ⟨hzg, hzt, hzs⟩, Or.inr fun _ _ => by unfold Apart at hzx0 ⊢; omega,
        Or.inr fun _ _ => by unfold Apart at hzy0 ⊢; omega⟩, hsl⟩
  have q8 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = st := hkm.s1
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := hkm.F.env.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hnex := hkm.F.nex
  have hney := hkm.F.ney
  have hopsB := IntAS.Box.mk hops
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨e1, e2, e3⟩ := hkm.pushHdr 0x5f2210
  have hLs := hkm.lsep
  clear hops hxacc hx48 hxH hxc48 hxs hyacc hy48 hyH hyc48 hys hzlive hzg hzs hsl hzt hzt0 hzx0 hzy0
  unfold KNGoal
  janus64_run [q8, hsp'] until [0x5e29e0]
  refine kn_icallR impl R hkmP ih _ (by rfl) ?sp ?g ?hm ?fs ?ra ?x15 ?df ?r0 ?r1 ?r2 ?r3
    (Or.inr ⟨by omega, by omega⟩) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold Apart; omega) (by unfold Apart; omega) ?nx ?ny hopsB.h ?lx ?ly ?ru ?ne1 ?ne2 ?hq ?hsc ?h5 hx150 hdf0
    (ra := 0x5f2210) ?rv ?K
  case hm => rfl
  case nx => simp only [hNeg, x1]; decide
  case ny => simp only [hNeg, y1]; decide
  case lx => simp only [hL, x3]; omega
  case ly => simp only [hL, y3]; omega
  case ru => simp only [hL, hC, x3, y3, z4]; omega
  case ne1 => simp only [hP, hC, z2, z4, x2, x4]; omega
  case ne2 => simp only [hP, hC, z2, z4, y2, y4]; omega
  case hq => simp only [hP, hL, z2, x3, y3]; left; omega
  case hsc => have := kc7_le n; unfold kc7 kc6 kc5 at this; omega
  case K =>
    intro s2 Lk' bk' ng0 l' hA2 hreg hkm2 hz hng0 hcan0 hval hnn hl2 hv2 hF hLF
    simp only [hP, hC, hL, z2, z4, x2, x3, y2, y3] at hz hval hnn hl2 hF hLF hv2
    have hix : intZ (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 80) = (kX1 s xp n : Int) := by
      simp only [intZ, hNeg, hP, hL, x1, x2, x3, ↓reduceIte, hxv, hkm.v1]
    have hiy : intZ (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210) ((s.regs 4).toNat - 144) = (kX1 s yp n : Int) := by
      simp only [intZ, hNeg, hP, hL, y1, y2, y3, ↓reduceIte, hyv, hkm.w1]
    rw [hix, hiy, ← Int.natCast_mul] at hval
    obtain ⟨e0, hv0⟩ := sgn_nonneg hval hng0 hcan0 hnn
    subst e0
    rw [hxv, hyv, hkm.v1, hkm.w1] at hv2
    -- the frames of the call relative to `S.mem` (through the push)
    have hF' : MemFrame S.mem s2.mem (R.rt ++ [((s.regs 4).toNat - 456 - (W - 456), (s.regs 4).toNat - 456 + 40)] ++
        ([((s.regs 4).toNat - 208, (s.regs 4).toNat - 208 + 32), (zp + 16 * kh n, zp + 16 * kh n + 8 * (lx1 + ly1))] ++
          stkWs S.mem st)) := by
      have := pushFrame (rt := R.rt) (w := [((s.regs 4).toNat - 456 - (W - 456), (s.regs 4).toNat - 456 + 40)])
        (ws := [((s.regs 4).toNat - 208, (s.regs 4).toNat - 208 + 32), (zp + 16 * kh n, zp + 16 * kh n + 8 * (lx1 + ly1))] ++
          stkWs S.mem st)
        (q := (s.regs 4).toNat - 456) (v := 0x5f2210) (M := S.mem) (M' := s2.mem)
        (fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)
      simp only [stkWs, e1, e2, e3, List.append_assoc] at hF this ⊢
      exact this hF
    have hLF' : LiveFrame S.mem s2.mem Lk
        ([((s.regs 4).toNat - 208, (s.regs 4).toNat - 208 + 32), (zp + 16 * kh n, zp + 16 * kh n + 8 * (lx1 + ly1))] ++
          stkWs S.mem st) := by
      have := pushLF (M := S.mem) (M' := s2.mem) (q := (s.regs 4).toNat - 456) (v := 0x5f2210) (Lk := Lk)
        (ws := [((s.regs 4).toNat - 208, (s.regs 4).toNat - 208 + 32), (zp + 16 * kh n, zp + 16 * kh n + 8 * (lx1 + ly1))] ++
          stkWs S.mem st)
        (fun r hr => by have := hLs r hr; simp only [outside_cons, outside_nil, and_true]; omega)
      simp only [stkWs, e1, e2, e3] at hLF this ⊢
      exact this hLF
    clear hF hLF
    obtain ⟨-, htw, -, htz, -, -, -⟩ := hkm.tops
    have hts := hkm.tsep
    obtain ⟨-, -, hzw', -, hzs', -, -, hzh', -⟩ := hkm.zops
    have hstw : Outside st 24 (win s W 72) := hkm.F.stk.2.2.1
    have hfrw := hkm.stk.2.2.1
    have hslc := hkm.sok.2.2.2.2.2.1
    have hkTd : kT n = 2 * kh n + 1 := rfl
    obtain ⟨s1, s2', -⟩ := hzs'
    obtain ⟨u1, u2, -⟩ := hts
    simp only [BasicSqr.freeP, BasicSqr.freeN] at s2' u2
    unfold Apart at s1 s2' u1 u2 htz
    simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hzw' hstw hfrw htw
    have hrd : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat + 72 → (x + m ≤ (s.regs 4).toNat - 208 ∨
        (s.regs 4).toNat - 176 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m := by
      intro x m h1 h2 h3
      exact hkm.rdW (k := W - 456) (a := 40) (by omega) (by omega) hF' h1 h2
        (by simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
            omega_only [h1, h2, h3, hzw', hstw, hfrw, hW, hWs, hl0, hm0, hzl, h40, hkh])
    -- `z` and `t` outside the written part keep their bytes
    have hkz : ∀ a m, ((zp ≤ a ∧ a + m ≤ zp + 8 * zc) ∨ (t ≤ a ∧ a + m ≤ t + 8 * kT n)) →
        (a + m ≤ zp + 16 * kh n ∨ zp + 16 * kh n + 8 * (lx1 + ly1) ≤ a) → s2.mem.readLE a m = S.mem.readLE a m := by
      intro a m ha hq
      have hH : Held R Lk a m := by
        rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · exact hzh'.sub q1 q2
        · exact hkm.scr.held.sub q1 q2
      refine Held.readLE2 hH hF' hLF' ?_ ?_
      · simp only [outside_cons, outside_nil, and_true]
        rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · omega_only [q1, q2, hzw', hW, hWs]
        · omega_only [q1, q2, htw, hW, hWs]
      · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
        rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · omega_only [q1, q2, hq, hzw', s1, s2', hW, hWs]
        · omega_only [q1, q2, htw, htz, u1, u2, hW, hWs, hl0, hm0, hzl, h40, hkh]
    have hkzT : ∀ a m, t ≤ a → a + m ≤ t + 8 * kT n → s2.mem.readLE a m = S.mem.readLE a m :=
      fun a m q1 q2 => hkz a m (Or.inr ⟨q1, q2⟩) (by clear s1 s2' u1 u2 hzw' hstw hfrw htw hrd hkz; omega)
    -- `z[2n2:2n2+need]` at the call memory is `z[2n2:2n2+need]` at `S.mem`
    have hzP : ∀ a m, zp ≤ a → a + m ≤ zp + 8 * zc →
        (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2210).readLE a m = S.mem.readLE a m :=
      fun a m q1 q2 => pushRd (by omega)
    clear hzw' hstw hfrw htw s1 s2' u1 u2 hF' hLF' hzx hzy hxw hyw hzw htz
    have h0 := hB.zhi
    have hl1 := hB.hl1
    have hl0' := hB.hl0
    refine hK s2 Lk' bk' l' ⟨hA2, hkm2, NatSqr.IntAt.keep hB.z1h fun x m q1 q2 => hrd x m (by omega) (by omega)
      (Or.inl (by omega)), hB.hng, hB.hcan, hl1, ?_, ?_,
      NatSqr.IntAt.keep hB.z0h fun x m q1 q2 => hrd x m (by omega) (by omega) (Or.inr (by omega)), hl0', ?_, ?_,
      ?_, by omega, hv0, ?_, ?_, ?_⟩
    · have e : natVal s2.mem t l1 = natVal S.mem t l1 := by
        unfold natVal; exact hkzT _ _ (Nat.le_refl _) (by omega)
      rw [e]; exact hB.z1v
    · rcases hB.z1n with q | q
      · exact Or.inl q
      · by_cases hq0 : l1 = 0
        · exact Or.inl hq0
        · right; rwa [hkzT _ _ (by omega) (by omega)]
    · have e : natVal s2.mem zp l0 = natVal S.mem zp l0 := by
        unfold natVal; exact hkz _ _ (Or.inl ⟨Nat.le_refl _, by omega⟩) (Or.inl (by omega))
      rw [e]; exact hB.z0v
    · rcases hB.z0n with q | q
      · exact Or.inl q
      · by_cases hq0 : l0 = 0
        · exact Or.inl hq0
        · right; rwa [hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inl (by omega))]
    · exact hz
    · exact hnn
    · rw [← hB.zlo]; unfold natVal; exact hkz _ _ (Or.inl ⟨Nat.le_refl _, by omega⟩) (Or.inl (by omega))
    · rcases hv2 with hv2 | ⟨hv0', hv2⟩
      · refine fill_val (need := lx1 + ly1) (by omega) h0 (Or.inl hv2) ?_
        unfold natVal; exact hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inr (by omega))
      · refine fill_val (need := lx1 + ly1) (by omega) h0 (Or.inr ⟨hv0', ?_⟩) ?_
        · rw [hv2]; unfold natVal; exact hzP _ _ (by omega) (by omega)
        · unfold natVal; exact hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inr (by omega))
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega_only [hW, hWs] |
    (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_only [hW, hWs])

end FvModexp.Amd64.Q.NatMul
