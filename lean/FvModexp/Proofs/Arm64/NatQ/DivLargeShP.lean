import FvModexp.Proofs.Arm64.NatQ.DivLargeCallees
import FvModexp.Proofs.Arm64.NatQ.DivLargeCall

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivLargeShP.lean, TIGHT COSTS, asm s38)
# `divLarge` (arm64): the precondition of `lshVU.abi0` / `rshVU.abi0` called from the frame (pure)

Arguments in the ABI0 area `SP' + 8 … SP' + 56` (`SP' = entry SP - 304`), result word `SP' + 64`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}

set_option maxHeartbeats 4000000 in
theorem lsh_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1)
    {Lk : List (Nat × Nat)} {bk : Nat} (S : State) (hspn : S.sp.toNat = s.sp.toNat - 304) (h28 : S.regs 28 = s.regs 28)
    {z x n sh : Nat} (hz : S.mem.readLE (S.sp.toNat + 8) 8 = z) (hn : S.mem.readLE (S.sp.toNat + 16) 8 = n)
    (hx : S.mem.readLE (S.sp.toNat + 32) 8 = x) (hs : S.mem.readLE (S.sp.toNat + 56) 8 = sh)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 56)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hzacc : S.mem.accessible z (8 * n) true = true) (hxacc : S.mem.accessible x (8 * n) false = true)
    (hsh1 : 1 ≤ sh) (hsh63 : sh ≤ 63) (hzx : x ≤ z ∨ Apart z (8 * n) x (8 * n)) (hzx' : z ≤ x ∨ Apart z (8 * n) x (8 * n))
    (hzw : z + 8 * n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ z)
    (hxw : x + 8 * n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ x)
    (hzh : Held R Lk z (8 * n)) (hzg : Apart z (8 * n) ((s.regs 28).toNat + 16) 8)
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) :
    LshLPre R bk Lk S ∧ RshLPre R bk Lk S := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hE.pre.ce
  unfold Apart at hga
  have hfacc : S.mem.accessible (S.sp.toNat + 8) 64 true = true := by
    rw [hacc]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hro : Outside (S.sp.toNat + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hrg : Apart (S.sp.toNat + 64) 8 ((S.regs 28).toNat + 16) 8 := by rw [h28]; unfold Apart; omega
  have hal' : S.sp.toNat % 16 = 0 := by omega
  have hct : LshVUSum.Ctx S z x n sh := ⟨hz, hn, hx, hs, h30a, h30b, hal', by omega, hfacc, hzacc, hxacc, hsh1, hsh63, hzx,
    by unfold Apart; omega, by unfold Apart; omega⟩
  have hct' : RshVUSum.Ctx S z x n sh := ⟨hz, hn, hx, hs, h30a, h30b, hal', by omega, hfacc, hzacc, hxacc, hsh1, hsh63,
    hzx', by unfold Apart; omega, by unfold Apart; omega⟩
  refine ⟨⟨?_, by rw [h28]; exact hinv, by rw [hz, hn]; exact hzh, hro, by rw [hz, hn, h28]; exact hzg, hrg⟩,
    ⟨?_, by rw [h28]; exact hinv, by rw [hz, hn]; exact hzh, hro, by rw [hz, hn, h28]; exact hzg, hrg⟩⟩
  · unfold LshVUSum.Pre; rw [hz, hn, hx, hs]; exact hct
  · unfold RshVUSum.Pre; rw [hz, hn, hx, hs]; exact hct'

end FvModexp.Arm64.Q.DivLarge
