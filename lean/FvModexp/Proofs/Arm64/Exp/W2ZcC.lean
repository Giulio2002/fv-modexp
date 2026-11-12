import FvModexp.Proofs.Arm64.Exp.W2Defs
import FvModexp.Proofs.Arm64.Exp.W2ZcDefs

/-!
# window-2 prologue (arm64): after the first-window `memmove` (fn+0x878) → loop test (fn+0xaa0)

Reloads of the spills, `yi <<= 64 - 2k` (nat.go:1445), `k -= 1`, `[240] = i`, jump to the test. The memory facts
are taken as explicit reads of the post-call memory `m1` (no frame reasoning inside the run).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

/-- the return pc of the first-window `memmove` (fn+0x878) -/
abbrev zr : Nat := 1804072

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcC (impl : List Segment) (R : RtInv) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen zp zc zzp zzc yi k V : Nat) (M m1 : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hk : k ≤ 31) (hyl' : ylen < 2 ^ 40)
    (q368 : m1.readLE (sp + 368) 8 = zp) (q584 : m1.readLE (sp + 584) 8 = zzp) (q736 : m1.readLE (sp + 736) 8 = n)
    (q144 : m1.readLE (sp + 144) 8 = zc) (q296 : m1.readLE (sp + 296) 8 = zzc) (q712 : m1.readLE (sp + 712) 8 = ylen)
    (q240 : m1.readLE (sp + 240) 8 = ylen - 1) (q704 : m1.readLE (sp + 704) 8 = yp) (q184 : m1.readLE (sp + 184) 8 = yi)
    (q328 : m1.readLE (sp + 328) 8 = k + 1) (q232 : m1.readLE (sp + 232) 8 = k) (q224 : m1.readLE (sp + 224) 8 = k0)
    (q728 : m1.readLE (sp + 728) 8 = mp) (q744 : m1.readLE (sp + 744) 8 = mc)
    (hF : MemFrame M m1 (R.rt ++ cw sp ++ [(zp, zp + 8 * n)])) (hL : LiveFrame M m1 L [(zp, zp + 8 * n)])
    (hI : R.inv b L g (view R.rt L m1)) (hrg : m1.regions = M.regions) (hv : m1.readLE zp (8 * n) = V)
    (hzw : zp + 8 * n ≤ sp + 240 ∨ sp + 248 ≤ zp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 zr) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = m1)
    (KT : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 testL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 13 = BitVec.ofNat 64 n → S'.regs 14 = BitVec.ofNat 64 zc →
      S'.regs 1 = BitVec.ofNat 64 zzp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 15 = BitVec.ofNat 64 zzc →
      S'.regs 2 = BitVec.ofNat 64 n → S'.regs 9 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 mc →
      S'.regs 12 = BitVec.ofNat 64 k0 → S'.regs 16 = BitVec.ofNat 64 ylen →
      S'.regs 17 = BitVec.ofNat 64 (ylen - 1) → S'.regs 19 = BitVec.ofNat 64 yp →
      S'.regs 20 = BitVec.ofNat 64 ((yi * 2 ^ (64 - k * 2)) % 2 ^ 64) →
      S'.regs 21 = BitVec.ofNat 64 k - 1#64 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M M' L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE zp (8 * n) = V → M'.readLE (sp + 240) 8 = ylen - 1 →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have e64 : 64#64 - BitVec.ofNat 64 (k * 2) = BitVec.ofNat 64 (64 - k * 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h63b : (BitVec.ofNat 64 (64 - k * 2)).getLsbD 63 = false := by
    show (BitVec.ofNat 64 (64 - k * 2)).toNat.testBit 63 = false
    rw [BitVec.toNat_ofNat]; exact Nat.testBit_lt_two_pow (by omega)
  janus_run [q368, q584, q736, q144, q296, q712, q240, q704, q184, q328, q232, q224, q728, q744,
    e23 _ hk, e64, h63b, lsl2] until [testL]
  refine KT _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?lf ?iv ?rg ?vl ?r2
  case mf =>
    refine hF.writeLE_inRanges _ ?_
    exact ⟨(sp + 240, sp + 248), by simp [cw], by simp only; omega, by simp only; omega⟩
  case lf => exact hL.writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
  case iv => exact FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) hI
  case rg => rw [Memory.regions_writeLE]; exact hrg
  case vl => rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hv
  case r2 => rw [FvModexp.Expmc.readLE_writeLE_same rfl]; omega
  all_goals first | (janus_simp [e20 yi _ hk, e21' _ hk]; done) | skip

end FvModexp.Arm64.W2Pro
