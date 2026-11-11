import FvModexp.Proofs.Arm64.Exp.MontHyp
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `nat.montgomery` (arm64): the exit path (loop done, `i = n`), nat.go:212-218

```go
if c != 0 { subVV(z[:n], z[n:], m) } else { copy(z[:n], z[n:]) }
return z[:n]
```
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.MontExit

open FvModexp.Arm64.MontHyp


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exit (impl : List Segment) (R : RtInv)
    (hsub : Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ)
    (hmv : MemmoveLive (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibMont.program.link impl) ret) (s : State) (L : List (Nat × Nat)) (b : Nat)
    (S : State) (sp zp cap xp xc mp mc k n c : Nat) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 head) (hsp : S.sp = BitVec.ofNat 64 sp) (hsps : s.sp.toNat = sp + 192)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n)) (h2 : S.regs 2 = BitVec.ofNat 64 cap)
    (h7 : S.regs 7 = BitVec.ofNat 64 n) (h8 : S.regs 8 = BitVec.ofNat 64 c)
    (h9 : S.regs 9 = BitVec.ofNat 64 mp) (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = BitVec.ofNat 64 mc)
    (h13 : S.regs 13 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28) (hmem : S.mem = M)
    (hal : sp % 16 = 0) (hsp4 : 4096 ≤ sp) (hsp48 : sp + 312 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4096) (4096 + 312) true = true)
    (hret0 : M.readLE sp 8 = ret) (hfp : M.readLE (sp - 8) 8 = (s.regs 29).toNat)
    (hn : 0 < n) (hn2 : 2 * n ≤ cap) (hcap : cap < 2 ^ 40) (hc : c ≤ 1) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40)
    (hzp : zp + 8 * cap ≤ 2 ^ 48) (hzacc : M.accessible zp (8 * cap) true = true)
    (hmacc : M.accessible mp (8 * n) false = true) (hmp : mp + 8 * n ≤ 2 ^ 48)
    (hzm : Apart zp (8 * cap) mp (8 * n)) (hzs : Apart zp (8 * cap) (sp - 4096) (4096 + 312))
    (hms : Apart mp (8 * n) (sp - 4096) (4096 + 312))
    (r112 : M.readLE (sp + 112) 8 = cap) (r168 : M.readLE (sp + 168) 8 = zp) (r304 : M.readLE (sp + 304) 8 = n)
    (hg : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hgacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgs : Apart ((s.regs 28).toNat + 16) 8 (sp - 4096) (4096 + 312)) (hgz : Apart ((s.regs 28).toNat + 16) 8 zp (8 * cap))
    (hguard : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < sp)
    (hgrt : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hwin : Outside (sp - 4096) (4096 + 312) R.rt) (hzh : InRanges zp (8 * cap) L ∨ Outside zp (8 * cap) R.rt)
    (hLs : LiveSep L [(sp - 4096, sp + 312)])
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L M))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, zp + n * 8, 8 * n]) :
    Reaches ((LibMont.program.link impl).withExit ret) S (IsReturn fun s' =>
      s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
      s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 1 = BitVec.ofNat 64 n ∧ s'.regs 2 = BitVec.ofNat 64 cap ∧
      s'.mem.readLE zp (8 * n) = (if c ≠ 0 then (M.readLE (zp + 8 * n) (8 * n) + 2 ^ (64 * n) - M.readLE mp (8 * n)) % 2 ^ (64 * n)
        else M.readLE (zp + 8 * n) (8 * n)) ∧
      R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
      MemFrame M s'.mem (R.rt ++ [(sp - 4096, sp + 184), (sp + 200, sp + 312), (zp, zp + 8 * n)]) ∧
      LiveFrame M s'.mem L [(zp, zp + 8 * n)]) := by

  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hlt : ((n : Int) < (n : Int)) = False := by simp
  have hon : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  have h8n : 8 * n % 18446744073709551616 = 8 * n := by omega
  have hzh8 : InRanges zp (8 * n) L ∨ Outside zp (8 * n) R.rt :=
    hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hspq : BitVec.ofNat 64 sp + 192#64 = s.sp := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
  have hmin : (18446744073709551616 - n + 2 * n) % 18446744073709551616 = n := by omega
  janus_run [r112, r168, r304, hret0, hfp, hmin, hlt, hon, h8n, FvModexp.mask_sub_lt n cap (by omega) (by omega), FvModexp.asr63_mask n cap (n * 8) (by omega) (by omega) (by omega)]
    calls [hsub, hmv L b]
  · -- copy(z[:n], z[n:])
    refine ⟨hspq, ?_, (by janus_assumption : R.inv _ _ _ _), ?_, (by janus_assumption : LiveFrame _ _ _ _)⟩
    · rw [FvModexp.Expmc.readLE_of_copied (by janus_assumption : Mem.Copied _ _ _ _ _), Nat.mul_comm n 8]
    · exact FvModexp.Expmc.frame_widen2h (by janus_assumption : MemFrame M _ _) (by omega) (by omega) (by omega) (by omega)
  · -- subVV(z[:n], z[n:], m)
    exact ⟨hspq, (by janus_assumption : _ = _),
      FvModexp.Expmc.close_frame2 (by janus_frame) (by omega) (by omega) (by omega)
        (by rw [show sp + 312 - (sp - 4096) = 4096 + 312 by omega]; exact hwin) hzh8 hLs hinv⟩

end FvModexp.Arm64.MontExit
