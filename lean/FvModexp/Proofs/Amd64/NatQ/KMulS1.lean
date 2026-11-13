import FvModexp.Proofs.Amd64.NatQ.KMulI
import FvModexp.Proofs.Amd64.NatQ.KMulS1c
import FvModexp.Proofs.Common.OmegaOnly

set_option autoImplicit false

/-!
# [amd64 port (divmc s50) of the Q-form Arm64/NatQ/KMulS1.lean — TIGHT COSTS] `karatsuba` (amd64): `z1.mul(stk, tx, ty); clear(z)` (natmul.go:210-212), `KM2b → KM3`

`kS1`: from `KM2b` (`0x5f2185`) the argument setup (`AX = &z1`, `BX = stk`, `CX = &tx`, `DI = &ty`), the `CALL`
(`0x5f21a2`, return address `0x5f21a7` pushed at `RSP - 456`) and the inner `(*Int).mul` (`kn_icallR`: the product is
written into `z1`'s array `t`, reused), then `kS1clr` (KMulS1c) at the return address.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le tls pushRd)
open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`KM2b → KM3`**: `z1.mul(stk, tx, ty)` (`0x5f2185 … 0x5f21a2`, `kn_icallR`), then `kS1clr` -/
theorem kS1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    (ih : ∀ j, IH impl R H (8 * n + 2) j) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {Lk : List (Nat × Nat)} {bk tng ltx yng lty : Nat} (S : State)
    (hB : KM2b R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk tng ltx yng lty)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' ng l1 : Nat),
      KM3 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hkh : kh n = (n + 1) / 2 := rfl
  have hltx := hB.hltx; have hlty := hB.hlty
  -- the facts at the call memory (return address `0x5f21a7` pushed at `RSP - 456`)
  have hkmP := hkm.push 0x5f21a7
  obtain ⟨t1, t2, t3, t4⟩ := IntAt.pushK (sp := (s.regs 4).toNat) (v := 0x5f21a7) hB.txh (by omega) (by omega)
  obtain ⟨y1, y2, y3, y4⟩ := IntAt.pushK (sp := (s.regs 4).toNat) (v := 0x5f21a7) hB.tyh (by omega) (by omega)
  obtain ⟨z1, z2, z3, z4⟩ := IntAt.pushK (sp := (s.regs 4).toNat) (v := 0x5f21a7) hB.z1h (by omega) (by omega)
  obtain ⟨hxacc, hx48, hxH, hxc48, hxw, hxs, -, -, -, -⟩ := hkmP.partZ (o := 0) (l := ltx) (by omega)
  obtain ⟨hyacc, hy48, hyH, hyc48, hyw, hys, -, -, -, -⟩ := hkmP.partZ (o := kh n) (l := lty) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hxacc hx48 hxH hxc48 hxw hxs
  obtain ⟨hlive, htw, htg, htz, -, -, ht48⟩ := hkmP.tops
  obtain ⟨htt, -⟩ := hkmP.ttls
  have hts := hkmP.tsep
  have hsl : stLen (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) st + 4 * (ltx + lty) + 64 ≤ 2 ^ 16 := by
    rw [hkmP.slen]; have := hkmP.F.slb; simp only [StackNat.rnd, kT]; omega
  have hops : Ops R Lk (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) (s.regs 14).toNat (tls s) (win s W 72) st
      (hP (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 264))
      (hC (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 264))
      (hP (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 296))
      (hL (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 296))
      (hC (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 296))
      (hP (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 328))
      (hL (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 328))
      (hC (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 328)) := by
    simp only [hP, hL, hC, t2, t3, t4, y2, y3, y4, z2, z4]
    exact ⟨⟨by omega, by omega, by omega, fun _ => hxacc, fun _ => ⟨hxH, hxc48⟩, fun _ => ⟨hxw, hxs⟩⟩,
      ⟨by omega, by omega, by omega, fun _ => hyacc, fun _ => ⟨hyH, hyc48⟩, fun _ => ⟨hyw, hys⟩⟩,
      ⟨by simp only [kT]; omega, hlive, htw, fun _ => ⟨htg, htt, hts⟩,
        Or.inr fun _ _ => by unfold Apart at htz ⊢; simp only [kT] at htz ⊢; omega,
        Or.inr fun _ _ => by unfold Apart at htz ⊢; simp only [kT] at htz ⊢; omega⟩, hsl⟩
  have q32 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = st := hkm.s1
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := hkm.F.env.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hopsB := IntAS.Box.mk hops
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- the value facts of `tx`, `ty` in the call memory
  have hzw0 : zp + 8 * zc ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 72 ≤ zp := by
    have := hkm.F.zw; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have htv : natVal (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) zp ltx = natVal S.mem zp ltx := by
    unfold natVal; exact pushRd (by omega)
  have hyv : natVal (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) (zp + 8 * kh n) lty =
      natVal S.mem (zp + 8 * kh n) lty := by
    unfold natVal; exact pushRd (by omega)
  clear hops hxacc hx48 hxH hxc48 hxw hxs hyacc hy48 hyH hyc48 hyw hys hlive htg hts htt hsl
  unfold KNGoal
  janus64_run [q32, hsp'] until [0x5e29e0]
  refine kn_icallR impl R hkmP ih _ (by rfl) ?sp ?g ?hm ?fs ?ra ?x15 ?df ?r0 ?r1 ?r2 ?r3
    (Or.inl ⟨by omega, by omega⟩) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold Apart; omega) (by unfold Apart; omega) ?nx ?ny hopsB.h ?lx ?ly ?ru ?ne1 ?ne2 ?hq ?hsc ?h5 hx150 hdf0
    (ra := 0x5f21a7) ?rv ?K
  case hm => rfl
  case nx => simp only [hNeg, t1]; exact hB.htng
  case ny => simp only [hNeg, y1]; exact hB.hyng
  case lx => simp only [hL, t3]; exact hltx
  case ly => simp only [hL, y3]; exact hlty
  case ru => simp only [hL, hC, t3, y3, z4, kT]; omega
  case ne1 => simp only [hP, hC, z2, z4, t2, t4, kT]; unfold Apart at htz; simp only [kT] at htz; omega
  case ne2 => simp only [hP, hC, z2, z4, y2, y4, kT]; unfold Apart at htz; simp only [kT] at htz; omega
  case hq => simp only [hP, hL, z2, t3, y3, kT]; right; omega
  case hsc => have := kc7_le n; unfold kc7 kc6 kc5 kc4 kc3 at this; omega
  case K =>
    intro s2 Lk' bk' ng l' hA2 hreg hkm2 hz hng hcan hval hnn hl2 _ hF hLF
    simp only [hP, hC, hL, z2, z4, t3, y3] at hz hval hnn hl2 hF hLF
    have hix : intZ (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 296) =
        (kX0 s xp n : Int) - (kX1 s xp n : Int) := by
      rw [← hB.tv, ← htv]; simp only [intZ, hNeg, hP, hL, t1, t2, t3, sgnV]
    have hiy : intZ (S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f21a7) ((s.regs 4).toNat - 328) =
        (kX1 s yp n : Int) - (kX0 s yp n : Int) := by
      rw [← hB.yv, ← hyv]; simp only [intZ, hNeg, hP, hL, y1, y2, y3, sgnV]
    rw [hix, hiy] at hval
    rw [List.append_assoc] at hF
    obtain ⟨-, htw', -, -, -, -, -⟩ := hkmP.tops
    have hstw : Outside st 24 (win s W 72) := hkmP.F.stk.2.2.1
    have hfrw := hkmP.stk.2.2.1
    simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfrw htw'
    have hslc := hkmP.sok.2.2.2.2.2.1
    have hkTd : kT n = 2 * kh n + 1 := rfl
    have hrd : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat + 72 → (x + m ≤ (s.regs 4).toNat - 264 ∨
        (s.regs 4).toNat - 232 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m := by
      intro x m h1 h2 h3
      refine (hkmP.rdW (k := W - 456) (a := 40) (by omega) (by omega) hF h1 h2 ?_).trans (pushRd (by omega))
      simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
      omega_only [h1, h2, h3, htw', hstw, hfrw, hW, hWs, hltx, hlty, h40, hkh, hkTd]
    refine kS1clr impl hap R hmc hx150 hdf0 s2 hA2 hkm2 hz hng hcan (by omega) hval hnn
      (NatSqr.IntAt.keep hB.z0h fun x m h1 h2 => hrd x m (by omega) (by omega) (Or.inr (by omega)))
      (NatSqr.IntAt.keep hB.z2h fun x m h1 h2 => hrd x m (by omega) (by omega) (Or.inr (by omega))) hK
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega_only [hW, hWs] |
    (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_only [hW, hWs])

end FvModexp.Amd64.Q.NatMul
