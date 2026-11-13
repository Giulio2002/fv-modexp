import FvModexp.Proofs.Amd64.Exp.W4K0

set_option autoImplicit false

/-!
# window-4 prologue (amd64): `toK` — from the `x` join `xJ` (fn+0x3fe) to the Newton loop's head `kHead`
(nat.go:1389-1394, 1273-1276; agent expmc s54; twin of `Arm64.W4XjR.toK`)

`R10 = [0x398]` (`len(y)`), `TESTQ R10; JE` (`len(y) == 0`, refuted); `TESTQ BX; JBE` (`len(m) == 0` → index panic,
refuted); `DX = [0x3a8]` (`m`), `R11 = m[0]`; Newton start `R12 = 2 - m0`, `R11 = m0 - 1`, `R13 = 1`; `JMP kHead`.
No memory is written.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- the `x` join (fn+0x3fe) -/
abbrev xJ : Nat := 6206558

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toK {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp ylen mp n m0 : Nat} {M : Memory}
    (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true)
    (hma : M.accessible mp 8 false = true) (hm48 : mp + 8 ≤ 2 ^ 48) (r398 : M.readLE (sp + 0x398) 8 = ylen) (r3a8 : M.readLE (sp + 0x3a8) 8 = mp)
    (hyl : 0 < ylen) (hn : 0 < n) (hn' : n < 2 ^ 64) (hm0 : M.readLE mp 8 = m0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h3 : S.regs 3 = BitVec.ofNat 64 n) (hdf : S.df = false)
    (KH : ∀ (S' : State), S'.rip = BitVec.ofNat 64 kHead → S'.mem = M →
      S'.regs 13 = BitVec.ofNat 64 (2 ^ 0) →
      S'.regs 11 = BitVec.ofNat 64 ((m0 + 18446744073709551616 - 1) % 18446744073709551616) →
      S'.regs 12 = BitVec.ofNat 64 ((2 + 18446744073709551616 - m0 % 18446744073709551616) % 18446744073709551616) →
      S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = false →
      (∀ i, i ≠ 2 → i ≠ 10 → i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 15 → S'.regs i = S.regs i) →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have hyl64 : ylen < 2 ^ 64 := by have := Janus.Arm64.Memory.readLE_lt S.mem (sp + 0x398) 8; rw [r398] at this; omega
  have hy0 : BitVec.ofNat 64 ylen ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hn0 : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [r398, r3a8, hm0, hy0, hn0] until [kHead]
  have hm64 : m0 < 2 ^ 64 := by have := Janus.Arm64.Memory.readLE_lt S.mem mp 8; rw [hm0] at this; omega
  refine KH _ rfl rfl ?_ ?_ ?_ rfl rfl ?_ ?_
  · simp only [setRegF_apply, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · simp
  · intro i a1 a2 a3 a4 a5 a6; simp [setRegF_apply, a1, a2, a3, a4, a5]

end FvModexp.Amd64.W4Pro
