import FvModexp.Proofs.Arm64.Exp.ModInvSeg

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): entry → Newton loop → `JS` / `J0` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem x0_eq (m : Memory) (xp xl : Nat) (hxl : 0 < xl) : m.readLE xp 8 = natVal m xp xl % Exp.B := by
  have := Exp.natVal_prefix m xp 1 xl hxl
  rw [Nat.pow_one] at this
  rw [← this]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem entry (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4608 ≤ kc)
    (hpc : s.pc = BitVec.ofNat 64 1797104)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 n)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s)
    (kS : JS impl R kc sqrC mulC b L zp zl zc st xp xl xc n s)
    (kB : J0 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s) :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, -, hn1, hn2, -, hzp, -, -, hx0, hxc, hxc40, -,
    ⟨-, hxa, hx48, -, hxw⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hxw hout
  simp only [K, A] at hw hout hxw hg3 hb' ha hga
  have hxa8 : s.mem.accessible xp 8 false = true := Memory.accessible_sub _ hxa (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hx0e := x0_eq s.mem xp xl hx0
  have hB : Exp.B = 2 ^ 64 := Exp.B_def
  have hrd := Util.readLE8_lt s.mem xp
  unfold Goal
  have e8 : (if n < 64 then BitVec.ofNat 64 n else 64#64) = BitVec.ofNat 64 (min 64 n) := by
    apply BitVec.eq_of_toNat_eq; split <;> simp only [BitVec.toNat_ofNat] <;> omega
  have et : BitVec.ofNat 64 (s.mem.readLE xp 8) - 1#64 =
      BitVec.ofNat 64 ((natVal s.mem xp xl % Exp.B + Exp.B - 1) % Exp.B) := by
    rw [← hx0e]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hB]; omega
  have ek : 2#64 - BitVec.ofNat 64 (s.mem.readLE xp 8) =
      BitVec.ofNat 64 ((2 + Exp.B - natVal s.mem xp xl % Exp.B) % Exp.B) := by
    rw [← hx0e]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hB]; omega
  janus_run until [1797196]
  refine newtonLoop_run impl (min 64 n) (by omega) 6 0 _ ((natVal s.mem xp xl % Exp.B + Exp.B - 1) % Exp.B)
    ((2 + Exp.B - natVal s.mem xp xl % Exp.B) % Exp.B) (by omega) (by omega)
    (by rw [hB]; exact Nat.mod_lt _ (by decide)) (by rw [hB]; exact Nat.mod_lt _ (by decide)) rfl ?_ ?_ ?_ ?_
    fun S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 => ?_
  · janus_simp
  · janus_simp; exact e8
  · janus_simp; exact et
  · janus_simp; exact ek
  have hk0 : Exp.newtonLoop (min 64 n) 0 ((natVal s.mem xp xl % Exp.B + Exp.B - 1) % Exp.B)
      ((2 + Exp.B - natVal s.mem xp xl % Exp.B) % Exp.B) = k0 s xp xl n := by
    simp only [k0, Exp.newton, Nat.mod_mod]
  rw [hk0] at a2
  have b0 : S'.regs 0 = BitVec.ofNat 64 zp := by rw [a3]; janus_simp
  have b2 : S'.regs 2 = BitVec.ofNat 64 zc := by rw [a4]; janus_simp
  have b3 : S'.regs 3 = BitVec.ofNat 64 st := by rw [a5]; janus_simp
  have b4 : S'.regs 4 = BitVec.ofNat 64 xp := by rw [a6]; janus_simp
  have b5 : S'.regs 5 = BitVec.ofNat 64 xl := by rw [a7]; janus_simp
  have b6 : S'.regs 6 = BitVec.ofNat 64 xc := by rw [a8]; janus_simp
  have b7 : S'.regs 7 = BitVec.ofNat 64 n := by rw [a9]; janus_simp
  have b18 : S'.regs 18 = s.regs 18 := by rw [a10]; janus_simp
  have b28 : S'.regs 28 = s.regs 28 := by rw [a11]; janus_simp
  have bsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240) := by
    rw [a14]; exact Expmc.sp_sub _ _ (by omega) (by omega)
  clear a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14
  have hF : MemFrame s.mem S'.mem (winA s (K kc) A) := by rw [a13]; simp only [winA, K, A]; janus_frame
  have hrg : S'.mem.regions = s.mem.regions := by rw [a13]; janus_simp
  have hfw : Fw0 s S'.mem := by rw [a13]; exact ⟨by janus_simp, by janus_simp⟩
  have r8 : S'.mem.readLE (s.sp.toNat + 8) 8 = zp := by rw [a13]; janus_simp
  have r40 : S'.mem.readLE (s.sp.toNat + 40) 8 = xp := by rw [a13]; janus_simp
  clear a13
  by_cases hs : n ≤ 64
  · refine kS _ hpre hs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | (janus_simp; first | exact hF | exact hrg | exact hfw)
  · janus_run [hs] until [1797212]
    refine kB _ hpre (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | (janus_simp; first | exact hF | exact hrg | exact hfw | exact r8 | exact r40)

end FvModexp.Arm64.ModInv
