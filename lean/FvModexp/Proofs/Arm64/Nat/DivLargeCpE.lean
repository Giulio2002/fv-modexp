import FvModexp.Proofs.Arm64.Nat.DivLargeCpF

/-!
# `divLarge` (arm64): copy path, `u[len uIn] = 0` (natdiv.go:612, `fn + 0x204`) → the alias test
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cpE (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (hclz : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0)
    (m3 m4 : Memory)
    (hMF1 : MemFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 (R.rt ++ csW s ++ [(t, t + 8 * vl)]))
    (hLF1 : LiveFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 Lk [(t, t + 8 * vl)])
    (hcp1 : Mem.Copied (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 t vp (8 * vl))
    (hMF2 : MemFrame m3 m4 (R.rt ++ csW s ++ [(P, P + 8 * il)]))
    (hLF2 : LiveFrame m3 m4 Lk [(P, P + 8 * il)])
    (hinv4 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m4))
    (hval : natVal m4 P il = natVal s.mem ip il)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x204)) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18)
    (h0 : X.regs 0 = BitVec.ofNat 64 t) (h1 : X.regs 1 = BitVec.ofNat 64 vl) (h2 : X.regs 2 = BitVec.ofNat 64 vl)
    (h3 : X.regs 3 = BitVec.ofNat 64 C) (h4 : X.regs 4 = BitVec.ofNat 64 (il + 1))
    (h5 : X.regs 5 = BitVec.ofNat 64 P) (h11 : X.regs 11 = BitVec.ofNat 64 0) (h12 : X.regs 12 = BitVec.ofNat 64 vl)
    (h13 : X.regs 13 = BitVec.ofNat 64 il) (hm : X.mem = m4) (hreg4 : m4.regions = s.mem.regions)
    (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C 0 S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hp48 := hU.p48; have hc40 := hU.c40
  obtain ⟨hmU, hUA, hvv, hvt, huv⟩ := cp_fin hE hS hclz hMF1 hLF1 hcp1 hMF2 hLF2 hinv4 hval
  have hacc : m4.accessible (P + 8 * il) 8 true = true := by
    rw [hMF2.accessible, hMF1.accessible, Memory.accessible_writeLE]
    exact Memory.accessible_mono _ hU.pacc (by omega) (by omega)
  have hPa : (P + 8 * il) % 2 ^ 64 = P + 8 * il := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, hPa] until [aliasPt]
  rw [show P + il * 8 = P + 8 * il by omega]
  exact k _ ⟨rfl, rfl, h28, h29, h18, h0, h1, h2, h3, h4, h5, h11, h12, hmU, hUA, hS.ext2, hS.bud2, by omega,
    hvv, hvt, huv, by simp only [Memory.regions_writeLE]; exact hreg4⟩

end FvModexp.Arm64.DivLarge
