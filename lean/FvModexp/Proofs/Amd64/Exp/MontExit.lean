import FvModexp.Proofs.Amd64.Exp.MontHyp
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `nat.montgomery` (amd64): the exit path (loop done, `i = n`), nat.go:212-218

```go
if c != 0 { subVV(z[:n], z[n:], m) } else { copy(z[:n], z[n:]) }
return z[:n]
```
Frame: `PUSHQ BP; MOVQ SP, BP; SUBQ $0xb0, SP`, so the body's `SP` is `sp = RSP₀ - 0xb8`; saved `BP` at `sp + 0xb0`,
return address at `sp + 0xb8`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.MontExit

open FvModexp.Amd64.MontHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exit (impl : List Amd64.Segment) (R : RtInv)
    (hsub : Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ)
    (hmv : MemmoveLive64 (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibMont.program.link impl) ret) (s : State) (L : List (Nat × Nat)) (b : Nat)
    (S : State) (sp zp cap mp mc n c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 head) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hsps : (s.regs 4).toNat = sp + 0xb8)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 cap) (h2 : S.regs 2 = BitVec.ofNat 64 n)
    (h3 : S.regs 3 = BitVec.ofNat 64 n) (h10 : S.regs 10 = BitVec.ofNat 64 (2 * n))
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 c)
    (h14 : S.regs 14 = s.regs 14) (h15 : S.xmm 15 = s.xmm 15) (hmem : S.mem = M)
    (hx15 : s.xmm 15 = 0#128) (hdf : S.df = false)
    (hal : sp % 8 = 0) (hsp4 : 4104 ≤ sp) (hsp48 : sp + 288 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4104) (4104 + 288) true = true)
    (hret0 : M.readLE (sp + 0xb8) 8 = ret) (hbp : M.readLE (sp + 0xb0) 8 = (s.regs 5).toNat)
    (hn : 0 < n) (hn2 : 2 * n ≤ cap) (hcap : cap < 2 ^ 40) (hc : c ≤ 1) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40)
    (hzp : zp + 8 * cap ≤ 2 ^ 48) (hzacc : M.accessible zp (8 * cap) true = true)
    (hmacc : M.accessible mp (8 * n) false = true) (hmp : mp + 8 * n ≤ 2 ^ 48)
    (hzm : Apart zp (8 * cap) mp (8 * n)) (hzs : Apart zp (8 * cap) (sp - 4104) (4104 + 288))
    (hms : Apart mp (8 * n) (sp - 4104) (4104 + 288))
    (r68 : M.readLE (sp + 0x68) 8 = cap) (ra0 : M.readLE (sp + 0xa0) 8 = zp) (rc0 : M.readLE (sp + 0xc0) 8 = mp)
    (rd0 : M.readLE (sp + 0xd0) 8 = mc) (re0 : M.readLE (sp + 0xe0) 8 = n)
    (htb : 8 ≤ S.fsBase.toNat ∧ S.fsBase.toNat ≤ 2 ^ 48) (htr : M.accessible (S.fsBase.toNat - 8) 8 false = true)
    (htg : M.readLE (S.fsBase.toNat - 8) 8 = (s.regs 14).toNat)
    (hts : Apart (S.fsBase.toNat - 8) 8 (sp - 4104) (4104 + 288)) (htz : Apart (S.fsBase.toNat - 8) 8 zp (8 * cap))
    (hg : (s.regs 14).toNat + 24 ≤ 2 ^ 48) (hgacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgs : Apart ((s.regs 14).toNat + 16) 8 (sp - 4104) (4104 + 288)) (hgz : Apart ((s.regs 14).toNat + 16) 8 zp (8 * cap))
    (hguard : M.readLE ((s.regs 14).toNat + 16) 8 + 4104 < sp)
    (hgrt : Outside ((s.regs 14).toNat + 16) 8 R.rt)
    (hwin : Outside (sp - 4104) (4104 + 288) R.rt) (hzh : InRanges zp (8 * cap) L ∨ Outside zp (8 * cap) R.rt)
    (hLs : LiveSep L [(sp - 4104, sp + 288)])
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L M))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, zp + n * 8, n * 8]) :
    Reaches ((LibMont.program.link impl).withExit ret) S (IsReturn fun s' =>
      s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
      s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 3 = BitVec.ofNat 64 n ∧ s'.regs 1 = BitVec.ofNat 64 cap ∧
      s'.mem.readLE zp (8 * n) = (if c ≠ 0 then (M.readLE (zp + 8 * n) (8 * n) + 2 ^ (64 * n) - M.readLE mp (8 * n)) % 2 ^ (64 * n)
        else M.readLE (zp + 8 * n) (8 * n)) ∧
      R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
      MemFrame M s'.mem (R.rt ++ [(sp - 4104, sp + 288), (zp, zp + 8 * n)]) ∧
      LiveFrame M s'.mem L [(zp, zp + 8 * n)]) := by
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 8 - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp - 8 + 8 ∨ sp - 8 + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hLs2 : ∀ r ∈ L, Outside r.1 (r.2 - r.1) ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [outside_cons, outside_nil, outside_append, and_true] at this ⊢
    omega
  have hzh8 : InRanges zp (8 * n) L ∨ Outside zp (8 * n) R.rt :=
    hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hzh8' : InRanges zp (n * 8) L ∨ Outside zp (n * 8) R.rt := by rw [Nat.mul_comm]; exact hzh8
  have hlt : ((n : Int) < (n : Int)) = False := by simp
  have hon : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  have h8n : 8 * n % 18446744073709551616 = 8 * n := by omega
  have hmin : (18446744073709551616 - n + 2 * n) % 18446744073709551616 = n := by omega
  have hspq : BitVec.ofNat 64 sp + 192#64 = s.regs 4 + 8#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus64_run [r68, ra0, rc0, rd0, re0, hret0, hbp, hmin, hlt, hon, h8n, FvModexp.two_sub_one n (by omega), ite_self, FvModexp.sshr_land_lt n cap (n * 8) (by omega) (by omega) (by omega), FvModexp.neg_sshr_land_lt (n * 8) n cap (by omega) (by omega) (by omega)] calls [hsub, hmv L b]
  · -- copy(z[:n], z[n:])
    refine ⟨hspq, ?_, (by janus_assumption : R.inv _ _ _ _), ?_, ?_⟩
    · rw [show 8 * n = n * 8 by omega, FvModexp.Expmc.readLE_of_copied (by janus_assumption : Mem.Copied _ _ _ _ _)]
      have := hzs; unfold Apart at this
      exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    · janus_frame
    · refine (LiveFrame.writeLE (LiveFrame.refl M L _) _ (FvModexp.Expmc.outside_of_liveSep (a := sp - 8) (k := 8) hLs (by omega) (by omega))).trans
        (FvModexp.Expmc.liveFrame_widen (by janus_assumption : LiveFrame _ _ L [(zp, zp + n * 8)]) (fun a k h => by
          simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)) (fun _ _ h => h)
  · -- subVV(z[:n], z[n:], m)
    exact ⟨hspq, by rw [Nat.mul_comm n 8],
      FvModexp.Expmc.close_frame (by janus_frame) (by rw [show sp + 288 - (sp - 4104) = 4104 + 288 by omega]; exact hwin)
        hzh8 hLs hinv⟩

end FvModexp.Amd64.MontExit
