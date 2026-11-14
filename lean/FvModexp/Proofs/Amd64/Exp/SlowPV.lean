import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.Exp.SlowPVR

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): **`segV`** — `KV` (`aSet`, after `z.set(x)`) → `KT1` at `j = 0` (agent expmc s80;
twin of arm64 `SlowPV`/`SlowPVQ`)

`runV` (see `SlowPVR`), the frame writes `FV sp` through `WC.own`, `zz, r, q := nil`; the model invariant
`outerLoop 1 (stepM X M) Y 64 (len y - 1) v w X = expNNSlow X Y M` (`expNNSlow_eq`, `SubMod2N.norm_nlen`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem dl_nil {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M : Memory} {L1 : List (Nat × Nat)} :
    DL R L st zp zc M L1 0 0 :=
  ⟨by decide, fun h => absurd h (by decide), Or.inr (Or.inr ⟨rfl, rfl⟩), fun h => absurd h (by decide), fun _ => rfl⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`segV`: `KV` → `KT1`** (see the module doc) -/
theorem segV {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 pZ cZ : Nat}
    (hk : KV R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 pZ cZ)
    (KT : ∀ (S' : State) (v : BitVec 64) (w : Nat), stCap S'.mem st = stCap S.mem st →
      KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 0 w v pZ xl cZ
        (natVal s.mem xp xl) 0 0 0 0 0 0 0 0 0 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 (yl - 1) v.toNat w
        (natVal s.mem xp xl) = Exp.expNNSlow (natVal s.mem xp xl) (natVal s.mem yp yl) (natVal s.mem mp ml) →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hyN : NatNorm s.mem yp yl := hP.2.2.2.2.2.2.2.2.2.1
  have hya : s.mem.accessible yp (8 * yl) false = true := hP.2.2.2.2.2.2.2.1
  have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.1
  obtain ⟨hstw, -⟩ := hP.stkF
  have hwacc := hP.cenv0.2.2.2.1
  have hjc := hk.jc
  have hw := hjc.wc
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  have hyw := y_words hP hw (yl - 1) (by omega)
  have ea : yp + yl * 8 - 8 = yp + 8 * (yl - 1) := by omega
  have hya1 : S.mem.accessible (yp + yl * 8 - 8) 8 false = true := by
    rw [hw.fr.accessible, ea]; exact Janus.Arm64.Memory.accessible_mono _ hya (by omega) (by omega)
  have ht0 : Exp.wd (natVal s.mem yp yl) (yl - 1) ≠ 0 := by
    rcases hyN with h0 | htop
    · omega
    · rw [← Expmc.readLE_wd s.mem yp (yl - 1) yl (by omega)]; exact htop
  have htl : Exp.wd (natVal s.mem yp yl) (yl - 1) < 2 ^ 64 := by
    rw [← hyw]
    have := Expmc.readLE_lt_B S.mem (yp + 8 * (yl - 1)) 1
    rw [Nat.mul_one, Nat.pow_one, Exp.B_def] at this; exact this
  have hsl := hjc.esl
  refine runV ret0 Q sp yp yl _ S.mem hacc (by omega) hK5 hyl0 hyl hsl.2.2.2.1 hsl.2.2.1 hya1 (by rw [ea]; exact hyw)
    ht0 htl hy48 S hk.pc hjc.esp rfl ?_
  intro S2 pc2 sp2 hF hrg r138 ra8 ra0 r90 r168 r160 r78 r70 r150 f0 f1 f2 f3 f8 f10 f6 f7 f9 f11 f12 f13 f15
    f14 ffs fx fdf
  have hFo : ∀ a k, (a + k ≤ sp - 8 - K ∨ sp + 0x220 ≤ a ∨ sp + 0x170 ≤ a ∨ (a + k ≤ sp + 0x70)) →
      Outside a k (FV sp) := by
    intro a k ha
    simp only [FV, outside_cons, outside_nil, and_true]; omega
  obtain ⟨hw2, hdl2, hln2⟩ := WC.own hP hw hF hrg (fun q hq => by
    simp only [FV, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → S2.mem.readLE a k = S.mem.readLE a k :=
    fun a k h1 _ => hF.readLE a k (hFo a k (Or.inr (Or.inr (Or.inl (by omega)))))
  have ecap : stCap S2.mem st = stCap S.mem st := by
    unfold Apart at hstw
    exact hF.readLE _ _ (hFo _ _ (by omega))
  have hj2 := hjc.call (S' := S2) (sp2.trans hjc.esp.symm) f14 ffs fx fdf hw2 kF
  have hB : BB R L st zp zc S2.mem L1 pZ xl cZ (natVal s.mem xp xl) 0 0 0 0 0 0 0 0 0 :=
    ⟨hln2 _ _ _ _ hk.bz, dl_nil, Nat.le_refl _, dl_nil, Nat.le_refl _, dl_nil, Nat.le_refl _,
      fun _ h => absurd h (by decide), fun _ h => absurd h (by decide), fun _ h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  have hbl := (clz_bl' _ htl ht0).2
  refine KT S2 (S2.regs 13) (wN (Exp.wd (natVal s.mem yp yl) (yl - 1))) ecap
    ⟨hj2, hB, by unfold wN; omega, r138, pc2, Nat.le_max_left xl ml, Nat.zero_le _, f0.trans hk.r0,
      f10.trans hk.r10, f8.trans hk.r1, r150, r70, r78, r160, r90, f2, r168, ra0, ra8, f1, rfl, f15,
      f3.trans hk.r2, f6.trans hk.r6, f7.trans hk.r7, f9.trans hk.r9, f11, f12⟩ ?_
  rw [f13, expNNSlow_eq, SubMod2N.norm_nlen _ _ _ hyN]

end

end FvModexp.Amd64.ExpSlow
