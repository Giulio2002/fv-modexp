import FvModexp.Proofs.Amd64.Exp.ModInvSeg

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): entry → Newton loop → `JS` / `J0` (agent infra s53; twin of
`Arm64/Exp/ModInvEntry`)

```
+0x00  stack check; PUSHQ BP; MOVQ SP, BP; SUBQ $0xd8, SP; spill z.ptr (RSP+8), x.ptr (RSP+40)
+0x2a  CMPQ R10, $0x40; MOVL $0x40, DX; CMOVQCS R10, DX       // n0 := min(_W, n)
+0x40  TESTQ R8, R8; JLS panic                                // x[0] bounds check (len x > 0)
+0x49  MOVQ (SI), R11; LEAQ -2(R11), R12; NEGQ R12; DECQ R11   // k0 := 2 - x[0]; t := x[0] - 1
       MOVL $1, BX; JMP +0x6c                                  // i := 1
```
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem entry (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 0x5ea8c0)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (_h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 st) (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl)
    (h9 : s.regs 9 = BitVec.ofNat 64 xc) (h10 : s.regs 10 = BitVec.ofNat 64 n)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s)
    (kS : JS impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s)
    (kB : J0 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, hn1, hn2, -, -, -, -, hx0, -, -, -,
    ⟨-, hxa, hx48, -, hxw⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hra⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hxw hout
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hxw hgB hb' ha hga hgN hgR
  have hxa8 : s.mem.accessible xp 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hxa (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hx0e := x0_eq s.mem xp xl hx0
  have hB : Exp.B = 2 ^ 64 := Exp.B_def
  have hrd : s.mem.readLE xp 8 < 2 ^ 64 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem xp 8
  have e2 : (if n < 64 then BitVec.ofNat 64 n else 64#64) = BitVec.ofNat 64 (min 64 n) := by
    apply BitVec.eq_of_toNat_eq; split <;> simp only [BitVec.toNat_ofNat] <;> omega
  have hxB : natVal s.mem xp xl % Exp.B < 2 ^ 64 := by rw [hB]; exact Nat.mod_lt _ (by decide)
  have et : BitVec.ofNat 64 (natVal s.mem xp xl % Exp.B) - 1#64 =
      BitVec.ofNat 64 ((natVal s.mem xp xl % Exp.B + Exp.B - 1) % Exp.B) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hB]; omega
  have ek : 0#64 - (BitVec.ofNat 64 (natVal s.mem xp xl % Exp.B) - 2#64) =
      BitVec.ofNat 64 ((2 + Exp.B - natVal s.mem xp xl % Exp.B) % Exp.B) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hB]
    omega
  unfold Goal
  janus64_run until [0x5ea8c0 + 0x6c]
  refine newtonLoop_run impl (min 64 n) (by omega) 6 0 _ ((natVal s.mem xp xl % Exp.B + Exp.B - 1) % Exp.B)
    ((2 + Exp.B - natVal s.mem xp xl % Exp.B) % Exp.B) (by omega) (by omega)
    (by rw [hB]; exact Nat.mod_lt _ (by decide)) (by rw [hB]; exact Nat.mod_lt _ (by decide)) rfl ?_ ?_ ?_ ?_
    fun S' a1 a2 a3 => ?_
  · janus64_simp
  · janus64_simp; exact e2
  · janus64_simp; exact et
  · janus64_simp; exact ek
  have hk0 : Exp.newtonLoop (min 64 n) 0 ((natVal s.mem xp xl % Exp.B + Exp.B - 1) % Exp.B)
      ((2 + Exp.B - natVal s.mem xp xl % Exp.B) % Exp.B) = k0 s xp xl n := by
    simp only [k0, Exp.newton, Nat.mod_mod]
  rw [hk0] at a2
  obtain ⟨c0, c1, c4, c5, c6, c7, c8, c9, c10, c14, cm, cf, cx, cd⟩ := a3
  have b0 : S'.regs 0 = BitVec.ofNat 64 zp := by rw [c0]; try janus64_simp
  have b1 : S'.regs 1 = BitVec.ofNat 64 zc := by rw [c1]; try janus64_simp
  have b6 : S'.regs 6 = BitVec.ofNat 64 xp := by rw [c6]; try janus64_simp
  have b7 : S'.regs 7 = BitVec.ofNat 64 st := by rw [c7]; try janus64_simp
  have b8 : S'.regs 8 = BitVec.ofNat 64 xl := by rw [c8]; try janus64_simp
  have b9 : S'.regs 9 = BitVec.ofNat 64 xc := by rw [c9]; try janus64_simp
  have b10 : S'.regs 10 = BitVec.ofNat 64 n := by rw [c10]; try janus64_simp
  have b14 : S'.regs 14 = s.regs 14 := by rw [c14]; try janus64_simp
  have bf : S'.fsBase = s.fsBase := by rw [cf]; try janus64_simp
  have bx : S'.xmm 15 = s.xmm 15 := by rw [cx]; try janus64_simp
  have bd : S'.df = s.df := by rw [cd]; try janus64_simp
  have b4 : S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) := by
    rw [c4]; janus64_simp; try exact Expmc.sp_sub _ _ (by omega) (by omega)
  have b5 : S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) := by
    rw [c5]; janus64_simp; try exact Expmc.sp_sub _ _ (by omega) (by omega)
  clear c0 c1 c4 c5 c6 c7 c8 c9 c10 c14 cf cx cd
  have hF : MemFrame s.mem S'.mem (win s (K kc) A) := by rw [cm]; simp only [win, K, A]; janus_frame
  have hrg : S'.mem.regions = s.mem.regions := by rw [cm]; try janus64_simp
  have hfw : Fw0 s S'.mem := by rw [cm]; exact ⟨by janus64_simp, by janus64_simp⟩
  have r8 : S'.mem.readLE ((s.regs 4).toNat + 8) 8 = zp := by rw [cm]; try janus64_simp
  have r40 : S'.mem.readLE ((s.regs 4).toNat + 40) 8 = xp := by rw [cm]; try janus64_simp
  clear cm
  by_cases hs : n ≤ 64
  · exact kS _ hpre hs a1 ⟨b4, b5, ⟨b14, bf, bx, bd⟩, b0, b1, b7, b6, b8, b9, b10, a2, hF, hrg, hfw, r8, r40⟩
  · janus64_run [hs] until [0x5ea8c0 + 0x7b]
    refine kB _ hpre (by omega) ?_ ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals janus64_simp
    all_goals first | (with_reducible exact hF) | (with_reducible exact hrg) | (with_reducible exact hfw) | (with_reducible exact r8) | (with_reducible exact r40) | (with_reducible exact bf) | (with_reducible exact bx) | (with_reducible exact bd) | (with_reducible exact b14)

end FvModexp.Amd64.ModInv
