import FvModexp.Proofs.Amd64.Exp.ModInvJ2
import FvModexp.Proofs.Amd64.Exp.ModInvMake

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `JM` → `J2` (nat.go:1322-1325) (agent infra s55; twin of
`Arm64/Exp/ModInvMkZZ`)

From `JM` (`+0x1b6`): `zz := nat(nil).make(2·numWords)` (`zzalloc`), `z.setWord(k0)` (`k0 ≠ 0`, `cap z ≥ numWords + 1`:
the store `z[0] = k0`, `setw`), `i = 2`, the jump to the loop head `J2` with `j = 1` and `Z0 = natVal z (numWords + 1)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

theorem zB_one (n : Nat) : zB n 1 = NW n + 1 := by simp [zB]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`JM` from `J2`**: the `zz` allocation and `z[0] = k0`, then the loop head at round `1` -/
theorem mkzz (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4096 ≤ kc)
    (kJ : J2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s) :
    JM impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S zp' zc' L1 b1 hpre hn hpc h4 h5 hab h0 h2 h1 h3 h7 h6 h8 h9 h10 h12 hfw hrt hb hown hcap
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, -, hg3⟩, ⟨hb', hb2, -⟩, hal, -, hout, hga, -, -, -, -⟩, hsv, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hx1, -, -, -, -, -, -, ⟨-, hcost⟩, -, hty, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP, K, A] at hg1 hg3 hb' hb2 hout hga
  simp only [cost] at hcost
  have hnw1 : 2 ≤ NW n := by simp only [NW]; omega
  have hnw2 : NW n ≤ 2 ^ 12 := by simp only [NW]; omega
  have hk0 := k0_lt s xp xl n
  have hk0p : 0 < k0 s xp xl n := by
    unfold k0; rw [show min 64 n = 64 by omega]; exact newton64_pos _ hx1
  obtain ⟨ew, eg, egr, eLs⟩ := env_rt hpre hrt
  have hd := dl_rt hpre hrt
  obtain ⟨hta, ht8, ht0⟩ := FvModexp.Amd64.wordT_data hd
  have hwt : Apart NatAdd.wordT 16 ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) :=
    apart_of_data hd 1 (by decide) (by decide) ew
  have hok : R.ok (cA "runtime.makeslice") [NatAdd.wordT, 2 * NW n, 2 * NW n + 4] := hsv.1 _ _ _ (by omega)
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok hwt
  have hzc0 : 0 < zc' := by omega
  have hzlt := hown.1
  have hzp' := hown.2.1
  have hzo := hown.2.2.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzo
  obtain ⟨-, -, hzacc, -⟩ := hown.2.2.1 hzc0
  unfold Goal
  refine zzalloc impl R hmk kc b1 L1 s (NW n) zp' zc' hkc (by omega) (by omega) hal hnw1 hnw2 hzp' (by omega) S hpc h4 h5
    hab h0 h1 h2 h3 ew hout eLs ht8 ht0 hwt hty hok hta (by omega) eg hga (by rw [egr]; omega) (by omega)
    hrt.2.2.2.2.1 _ ?KZ
  intro S' m q r k1 k4 k5 kab k15 k13 k11 k0' k1' k2' k3 k6 k7 k8 k9 k10 k12 ksl kmem hap
  have hacc : m.accessible zp' 8 true = true := by
    rw [hap.1.accessible]
    exact Arm64.Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
  have hsa : m.accessible ((s.regs 4).toNat - 224 + 192) 8 false = true := by
    rw [hap.1.accessible]
    exact Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ ew (by omega) (by omega))
  refine setw impl _ _ zp' zc' (k0 s xp xl n) (s.regs 4).toNat m hk0p hk0 hzc0 (by omega) hzp' (by omega) (by omega)
    hacc hsa ksl (by omega) S' k1 (k4.trans h4) k0' k1' (by rw [k12, show (s.regs 4).toNat - 224 + 144 =
      (s.regs 4).toNat - 80 by omega, hfw.2.2.2.2.2.2.1]) kmem ?KS
  intro S'' f1 f2 f3 fr ffs fx fdf fm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := zz_j2 hkc hpre hn hfw hrt hb hown hcap hk0 hap
  have hz0i := Exp.z0_inv _ _ hx1 (show natVal (m.writeLE zp' 8 (k0 s xp xl n)) zp' (NW n + 1) % Exp.B = _ by
    rw [g7, k0, Nat.min_eq_left (by omega)])
  obtain ⟨-, f3', f4', f5', f6', f7', f9'⟩ := hfw.toFw2
  have r3 : S''.regs 3 = BitVec.ofNat 64 (NW n) := by
    rw [fr 3 (by decide) (by decide), k3, show (s.regs 4).toNat - 224 + 120 = (s.regs 4).toNat - 104 by omega, f9']
  have r6 : S''.regs 6 = BitVec.ofNat 64 xp := by
    rw [fr 6 (by decide) (by decide), k6, show (s.regs 4).toNat - 224 + 264 = (s.regs 4).toNat + 40 by omega, f4']
  have r7 : S''.regs 7 = BitVec.ofNat 64 st := by
    rw [fr 7 (by decide) (by decide), k7, show (s.regs 4).toNat - 224 + 256 = (s.regs 4).toNat + 32 by omega, f3']
  have r8 : S''.regs 8 = BitVec.ofNat 64 xl := by
    rw [fr 8 (by decide) (by decide), k8, show (s.regs 4).toNat - 224 + 272 = (s.regs 4).toNat + 48 by omega, f5']
  have r9 : S''.regs 9 = BitVec.ofNat 64 xc := by
    rw [fr 9 (by decide) (by decide), k9, show (s.regs 4).toNat - 224 + 280 = (s.regs 4).toNat + 56 by omega, f6']
  have r10 : S''.regs 10 = BitVec.ofNat 64 n := by
    rw [fr 10 (by decide) (by decide), k10, show (s.regs 4).toNat - 224 + 288 = (s.regs 4).toNat + 64 by omega, f7']
  obtain ⟨a14, afs, ax15, adf⟩ := kab
  refine kJ 1 S'' zp' (NW n + 1) zc' q (2 * NW n) (2 * NW n + 4) _ _ hpre hn f1
    (by rw [fr 4 (by decide) (by decide), k4, h4]) (by rw [fr 5 (by decide) (by decide), k5, h5])
    ⟨by rw [fr 14 (by decide) (by decide), a14], by rw [ffs, afs], by rw [fx, ax15], by rw [fdf, adf]⟩
    (by rw [f2]) f3 (by rw [fr 2 (by decide) (by decide), k2']) (by rw [fr 1 (by decide) (by decide), k1'])
    (by rw [fr 15 (by decide) (by decide), k15]) (by rw [fr 13 (by decide) (by decide), k13])
    (by rw [fr 11 (by decide) (by decide), k11]) r3 r7 r6 r8 r9 r10
    (by rw [fm]; exact g1) (by rw [fm]; exact g2) (by rw [fm]; exact g3) (by rw [fm]; exact g4) (by rw [fm]; exact g5)
    hcap (Nat.le_of_eq (zB_one n).symm) hcap (by omega) (by omega) (Nat.le_refl _)
    (by rw [Nat.sub_self, Nat.pow_zero]; omega) g6 (by rw [fm]; exact hz0i)

end FvModexp.Amd64.ModInv
