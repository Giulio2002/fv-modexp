import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4ZcC
import FvModexp.Proofs.Arm64.Exp.W4ZcP

/-!
# window-4 prologue (arm64): the first-window `memmove` (fn+0x9c4 .. return fn+0x878... see below)

From fn+0x854 (`STR R17, 240(RSP)`, after the `BEQ` that skips the copy when `z` already is `powers[d]`) through the
six spills and `runtime.memmove(z, powers[d], 8n)` to its return (fn+0x878 = `W4ZcC.zr`), then `zcC`.
The post-call bookkeeping (slot reads through the memmove frame, frame composition) is done here on a small
context; the run itself has no continuation work.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the first spill after the copy test (fn+0x854) -/
abbrev zs : Nat := 1800644

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcB (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen zp zc zzp zzc yi k pd V : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g sp n M zp zc) (hk : k ≤ 15)
    (hzzc' : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi64 : yi < 2 ^ 64)
    (hpd : Inp R L sp n M pd) (hzd : Apart zp (8 * zc) pd (8 * n)) (hvd : M.readLE pd (8 * n) = V)
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r1016 : M.readLE (sp + 1016) 8 = mp)
    (r1032 : M.readLE (sp + 1032) 8 = mc)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, pd, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 zs) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zzp) (h15 : S.regs 15 = BitVec.ofNat 64 zzc)
    (h17 : S.regs 17 = BitVec.ofNat 64 (ylen - 1)) (h20 : S.regs 20 = BitVec.ofNat 64 yi)
    (h21 : S.regs 21 = BitVec.ofNat 64 (k + 1)) (h22 : S.regs 22 = BitVec.ofNat 64 k)
    (h23 : S.regs 23 = BitVec.ofNat 64 n) (h25 : S.regs 25 = BitVec.ofNat 64 pd)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (hmem : S.mem = (M.writeLE (sp + 144) 8 zc).writeLE (sp + 368) 8 zp)
    (KT : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 testL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 13 = BitVec.ofNat 64 n → S'.regs 14 = BitVec.ofNat 64 zc →
      S'.regs 1 = BitVec.ofNat 64 zzp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 15 = BitVec.ofNat 64 zzc →
      S'.regs 2 = BitVec.ofNat 64 n → S'.regs 9 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 mc →
      S'.regs 12 = BitVec.ofNat 64 k0 → S'.regs 16 = BitVec.ofNat 64 ylen →
      S'.regs 17 = BitVec.ofNat 64 (ylen - 1) → S'.regs 19 = BitVec.ofNat 64 yp →
      S'.regs 20 = BitVec.ofNat 64 ((yi * 2 ^ (64 - k * 4)) % 2 ^ 64) →
      S'.regs 21 = BitVec.ofNat 64 k - 1#64 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M M' L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE zp (8 * n) = V → M'.readLE (sp + 240) 8 = ylen - 1 →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have he0' := he
  have hz0 := hz
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  unfold Apart at hzd z6
  have hne : zp ≠ pd := by intro e; rw [e] at hzd; omega
  have hpa := hpd.1
  have hz8n : InRanges zp (8 * n) L ∨ Outside zp (8 * n) R.rt :=
    z5.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hza : M.accessible zp (8 * n) true = true := Memory.accessible_mono _ z3 (Nat.le_refl _) (by omega)
  have hpb := hpd.2.2.2
  unfold Apart at hpb
  janus_run [lsl3, e8n n hn16] until [zr] calls [hmv L b]
  rename_i _ _ _ m1 _ _ hF1 hL1 hI1 hC1
  obtain ⟨q368, q872, q1024, q144, q296, q1000, q240, q992, q184, q328, q232, q224, q1016, q1032, qF, qL, qv, qzw⟩ :=
    zcPost (k0 := k0) (mp := mp) (mc := mc) (yp := yp) he0' hz0 hk hzzc' hzzp hyl hyl' hyi64 hpd.2.2.2 hvd r1000 r992
      r1024 r224 r1016 r1032 hF1 hL1 hC1
  exact zcC impl R ret hret Q b L g sp n mp mc k0 yp ylen zp zc zzp zzc yi k V M m1 r18 r29 he0' hk hyl'
    q368 q872 q1024 q144 q296 q1000 q240 q992 q184 q328 q232 q224 q1016 q1032 qF qL hI1 hrg1 qv qzw
    _ (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) KT

end FvModexp.Arm64.W4Pro
