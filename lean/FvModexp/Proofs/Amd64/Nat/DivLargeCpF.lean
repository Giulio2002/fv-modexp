import FvModexp.Proofs.Amd64.Nat.DivLargeCpRel
import FvModexp.Proofs.Common.TzWord

set_option autoImplicit false

/-!
# `divLarge` (amd64): the copy path's memory facts at the alias test (pure)

From `AtV` (after `copy(v, vIn)`, memory `V.mem`): optionally `memmove(P, uIn, 8 il)` (memory `m4`; `m4 = V.mem` when
`P = uIn`), then `u[il] := 0` (`+0x330`) → `MemU`, `UArr`, the values of `v` and `u` (`shift = 0`), as `AtAl` needs.
Port of `Arm64/Nat/DivLargeCpF.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

namespace FvModexp.Amd64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem cp_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {V : State}
    (hV : AtV R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C V)
    (hclz : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0)
    {m4 : Memory} {cs : List (Nat × Nat)}
    (hMF2 : MemFrame V.mem m4 (R.rt ++ cs ++ [(P, P + 8 * il)]))
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 41272 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 209)
    (hLF2 : LiveFrame V.mem m4 Lk [(P, P + 8 * il)])
    (hinv4 : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk m4))
    (hval : natVal m4 P il = natVal s.mem ip il) :
    MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C 0 (m4.writeLE (P + 8 * il) 8 0) ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C (m4.writeLE (P + 8 * il) 8 0) ∧
      natVal (m4.writeLE (P + 8 * il) 8 0) t vl = natVal s.mem vp vl * 2 ^ 0 ∧
      2 ^ 63 ≤ (m4.writeLE (P + 8 * il) 8 0).readLE (t + 8 * (vl - 1)) 8 ∧
      natVal (m4.writeLE (P + 8 * il) 8 0) P (il + 1) = natVal s.mem ip il * 2 ^ 0 := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvil := hl.vil; have hil9 := hl.il9
  have hU := hV.ua
  have hcap := hU.cap; have hp48 := hU.p48
  have hpvt := hU.pvt
  unfold Apart at hpvt
  have hLL : ∀ a n, InRanges a n L → InRanges a n Lk := fun a n h => hV.ext2.inRanges_old (hE.ext.inRanges_old h)
  -- the `u` memmove
  obtain ⟨hJ4, hU4⟩ := MemU.call hE hV.mem hU hMF2 hcs
    (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega) hLF2 hLL hinv4
  -- the store `u[il] = 0`
  have hW2 : MemFrame m4 (m4.writeLE (P + 8 * il) 8 0) (R.rt ++ [] ++ [(P + 8 * il, P + 8 * il + 8)]) := by
    simp only [List.append_nil]
    exact (show MemFrame m4 (m4.writeLE (P + 8 * il) 8 0) [(P + 8 * il, P + 8 * il + 8)] by janus_frame).mono
      fun a n h => by simp only [outside_append] at h; exact h.2
  have hLW : LiveFrame m4 (m4.writeLE (P + 8 * il) 8 0) Lk [(P + 8 * il, P + 8 * il + 8)] :=
    ⟨fun a n _ h => (show MemFrame m4 (m4.writeLE (P + 8 * il) 8 0) [(P + 8 * il, P + 8 * il + 8)] by janus_frame).readLE a n h⟩
  have hinv5 : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk (m4.writeLE (P + 8 * il) 8 0)) :=
    inv_store_held hinv4 (hU4.pheld.sub (by omega) (by omega))
  obtain ⟨hJ5, hU5⟩ := MemU.call hE hJ4 hU4 hW2 (fun r hr => by simp at hr)
    (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega) hLW hLL hinv5
  -- `v` is untouched by both
  have hvt : ∀ o n, o + n ≤ 8 * vl → (m4.writeLE (P + 8 * il) 8 0).readLE (t + o) n = V.mem.readLE (t + o) n := by
    intro o n h
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have hin : Held R Lk (t + o) n := (hV.ext2.held hl.theld).sub (by omega) (by omega)
    rcases hin with hi | ho
    · exact hLF2.readLE _ _ hi (by simp only [outside_cons, outside_nil, and_true]; omega)
    · have htw := hl.tw
      refine hMF2.readLE _ _ ?_
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨ho, outside_of_forall fun r hr => ?_⟩, by omega⟩
      have := hcs r hr; omega
  have htop : 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 := by
    have hlt := Janus.Arm64.Memory.readLE_lt s.mem (vp + 8 * (vl - 1)) 8
    rcases Nat.lt_or_ge (s.mem.readLE (vp + 8 * (vl - 1)) 8) (2 ^ 63) with h63 | h63
    · have := FvModexp.Exp.clzNat_of_lt 63 _ h63 1
      rw [show 63 + 1 = 64 by rfl, hclz] at this
      omega
    · exact h63
  refine ⟨hJ5, hU5, ?_, ?_, ?_⟩
  · have := hvt 0 (8 * vl) (by omega)
    simp only [Nat.add_zero] at this
    simp only [natVal, Nat.pow_zero, Nat.mul_one]; rw [this]; exact hV.vval
  · rw [hvt _ _ (by omega), hV.vtop]; exact htop
  · rw [natVal_succ, Janus.Arm64.Memory.readLE_writeLE_self]
    have : natVal (m4.writeLE (P + 8 * il) 8 0) P il = natVal m4 P il := by
      unfold natVal; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    rw [this, hval]; simp

end FvModexp.Amd64.DivLarge
