import FvModexp.Proofs.Arm64.Int.IntASB

/-!
# `(*Int).Add` / `(*Int).Sub` (arm64): the comparison `x.abs.cmp(y.abs)` (`+0xa4`) and the dispatch to paths B / C
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

open FvModexp.Arm64.RunIface (Serves)

/-- `CmpSum.Pre` at the call of `nat.cmp` (`SP = s.sp - 96`) -/
theorem cmpPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s S : State} (hpre : Pre R b L z x y s)
    (hA : AtCall s S z x) {r : Nat} (h30 : S.regs 30 = BitVec.ofNat 64 r) (hr4 : r % 4 = 0) (hr : r < 2 ^ 48)
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem x)) (h1 : S.regs 1 = BitVec.ofNat 64 (hL s.mem x))
    (h3 : S.regs 3 = BitVec.ofNat 64 (hP s.mem y)) (h4 : S.regs 4 = BitVec.ofNat 64 (hL s.mem y)) :
    CmpSum.Pre S := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, hx, hy, -⟩ := hpre
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, hxa, hx48, -, -, hxo⟩ := hx
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, hya, hy48, -, -, hyo⟩ := hy
  simp only [win, outside_cons, outside_nil, and_true] at hxo hyo
  unfold Apart at hga
  have hspT : S.sp.toNat = s.sp.toNat - 96 := by rw [hA.sp]; exact sp96 hb'
  have hmf := hA.mf
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hmf.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  unfold CmpSum.Pre GuardOK StackOK CmpSum.SliceOK
  rw [h30, h0, h1, h3, h4, hA.r28, hspT, tN (by omega), tN (by omega), tN (by omega), tN (by omega), tN (by omega)]
  refine ⟨hr4, by omega, ⟨hg1, by rw [hmf.accessible]; exact hg2, by rw [hgS]; omega⟩,
    ⟨by omega, by omega, by omega, by rw [hmf.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩,
    Or.inr ⟨by rw [hmf.accessible]; exact hxa, by unfold Apart; omega⟩,
    Or.inr ⟨by rw [hmf.accessible]; exact hya, by unfold Apart; omega⟩⟩

/-- the sign bit of `nat.cmp`'s result: `x < y` by length first, then value -/
theorem cmp_bit (m n X Y : Nat) :
    (((CmpSum.cmpRes m n X Y).getLsbD 63 == true) = true) ↔ (m < n ∨ (m = n ∧ X < Y)) := by
  unfold CmpSum.cmpRes
  by_cases h1 : m < n <;> by_cases h2 : n < m <;> by_cases h3 : X < Y <;> by_cases h4 : Y < X <;>
    simp [h1, h2, h3, h4] <;> first | decide | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the comparison and paths B / C, from the entry of `nat.cmp` to `RET` -/
theorem pathBC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) (hpre : Pre R b L z x y s)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hc : sub = true ↔ hNeg s.mem x = hNeg s.mem y)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1782608) (h30 : S.regs 30 = BitVec.ofNat 64 (entry sub + 0xa8))
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem x)) (h1 : S.regs 1 = BitVec.ofNat 64 (hL s.mem x))
    (h3 : S.regs 3 = BitVec.ofNat 64 (hP s.mem y)) (h4 : S.regs 4 = BitVec.ofNat 64 (hL s.mem y))
    (hA : AtCall s S z x) (hxs : S.mem.readLE (s.sp.toNat + 16) 8 = x)
    (hys : S.mem.readLE (s.sp.toNat + 24) 8 = y) :
    ReachesRet (LibIntAS.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post sub R b L z x y s s' := by
  have hcpre := cmpPre_of hpre hA h30 (by cases sub <;> simp [entry]) (by cases sub <;> simp [entry]) h0 h1 h3 h4
  refine ReachesRet.call_regions (cmpSum impl hap) hpc hcpre fun S1 hr hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  have hsp0 : 4560 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  simp only [CmpSum.frame, hspT] at hf
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 96 - 24 ∨ s.sp.toNat - 96 - 8 ≤ a) →
      (a + n ≤ s.sp.toNat - 96 + 8 ∨ s.sp.toNat - 96 + 16 ≤ a) →
      (a + n ≤ s.sp.toNat - 96 + 32 ∨ s.sp.toNat - 96 + 40 ≤ a) → m.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hf.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hA2 : ∀ S1 : State, S1.sp = S.sp → S1.regs 28 = S.regs 28 → S1.regs 29 = S.regs 29 → S1.regs 18 = S.regs 18 →
      S1.mem = m → AtCall s S1 z x := by
    intro S1 e1 e2 e3 e4 e5
    subst e5
    refine ⟨e1.trans hA.sp, e2.trans hA.r28, e3.trans hA.r29, e4.trans hA.r18, hA.mf.trans hf fun a n ho => ?_,
      by rw [hrg]; exact hA.reg, ?_, ?_, ?_, ?_⟩
    · simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨ho, by omega, by omega, by omega⟩
    · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hA.fp
    · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hA.lr
    · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hA.zs
    · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hA.ng
  have hmx : m.readLE (s.sp.toNat + 16) 8 = x := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hxs
  have hmy : m.readLE (s.sp.toNat + 24) 8 = y := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hys
  have hmz : m.readLE (s.sp.toNat + 8) 8 = z := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact hA.zs
  have hsp := hA.sp
  have hsp96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := sp96 hsp0
  have hacc : ∀ a n w, m.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hf.accessible, hA.mf.accessible]
  have hmw : m.accessible (s.sp.toNat - 4560) (4560 + 32) true = true := by rw [hacc]; exact hpre.1.2.1.2.2.2
  have hmzA : m.accessible z 32 false = true := by
    rw [hacc]; exact Memory.accessible_weaken _ hpre.2.2.2.2.2.1
  have hmxA : m.accessible x 32 false = true := by rw [hacc]; exact hpre.2.2.2.1.2.1
  have hmyA : m.accessible y 32 false = true := by rw [hacc]; exact hpre.2.2.2.2.1.2.1
  have hal : s.sp.toNat % 16 = 0 := hpre.1.2.1.1
  have hsa : s.sp.toNat + 32 ≤ 2 ^ 48 := hpre.1.2.1.2.2.1
  have hzo := hpre.2.2.2.2.2.2.2.1
  have hxo := hpre.2.2.2.1.2.2.2.1
  have hyo := hpre.2.2.2.2.1.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  have hz48 : z + 32 ≤ 2 ^ 48 := hpre.2.2.2.2.2.2.1
  have hx48 : x + 32 ≤ 2 ^ 48 := hpre.2.2.2.1.2.2.1
  have hy48 : y + 32 ≤ 2 ^ 48 := hpre.2.2.2.2.1.2.2.1
  rw [h30]
  have hx := hpre.2.2.2.1
  have hy := hpre.2.2.2.2.1
  have hzx := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc0 : 0 < hC s.mem z → _ := fun h => (hzx h).2.2
  have hnx := hx.1
  have hny := hy.1
  have hXn := hx.2.2.2.2.2.2.2.2.2.2.1
  have hYn := hy.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hx.2.2.2.2.1
  have hyl := hy.2.2.2.2.1
  have hxa := hx.2.2.2.2.2.2.2.2.2.2.2
  have hya := hy.2.2.2.2.2.2.2.2.2.2.2
  simp only [win, outside_cons, outside_nil, and_true] at hxa hya
  have hmfA := hA.mf
  have hlvx : Asm.lv S.mem (hP s.mem x) (hL s.mem x) = natVal s.mem (hP s.mem x) (hL s.mem x) :=
    hmfA.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hlvy : Asm.lv S.mem (hP s.mem y) (hL s.mem y) = natVal s.mem (hP s.mem y) (hL s.mem y) :=
    hmfA.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hdr : ∀ a, (a + 32 ≤ s.sp.toNat - 4560 ∨ s.sp.toNat + 32 ≤ a) → ∀ k, k + 8 ≤ 32 →
      S.mem.readLE (a + k) 8 = s.mem.readLE (a + k) 8 := fun a ha k hk =>
    hmfA.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hz8 := hdr z hzo 8 (by omega); have hz16 := hdr z hzo 16 (by omega); have hz24 := hdr z hzo 24 (by omega)
  have hx8 := hdr x hxo 8 (by omega); have hx16 := hdr x hxo 16 (by omega); have hx24 := hdr x hxo 24 (by omega)
  have hy8 := hdr y hyo 8 (by omega); have hy16 := hdr y hyo 16 (by omega); have hy24 := hdr y hyo 24 (by omega)
  have hpreB : Box (Pre R b L z x y s) := ⟨hpre⟩
  have hAB : Box (AtCall s S z x) := ⟨hA⟩
  have hxB : Box (OpR R L s x) := ⟨hx⟩
  have hyB : Box (OpR R L s y) := ⟨hy⟩
  clear hpre hA hcpre hx hy hmfA
  cases sub <;> simp only [entry, Bool.false_eq_true, ↓reduceIte] <;>
    janus_run [hmx, hmy, hmz, hsp, hsp96, hmw, hmzA, hmxA, hmyA] until [1781872]
  · have hlt := (SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).1 (by rw [← hlvx, ← hlvy]; exact (cmp_bit _ _ _ _).1 hbr)
    refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hl4 hl48 y x 0x128 (1 - hNeg s.mem x) hyB.h hxB.h
      (fun h => (hzc0 h).2) (fun h => (hzc0 h).1) ?_ (by omega) ?_ (Or.inr rfl) (by simp) (by omega) ?_ _ rfl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, entry] <;> decide)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hA2 _ hsp.symm (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setReg_apply, Nat.reduceEqDiff,
        ↓reduceIte]) rfl)
    · rcases (cmp_bit _ _ _ _).1 hbr with h | ⟨h, -⟩ <;> omega
    · have : hL s.mem x ≤ hL s.mem y := by rcases (cmp_bit _ _ _ _).1 hbr with h | ⟨h, -⟩ <;> omega
      omega
    · rw [intZ_eq, intZ_eq]; exact resC _ hnx hny (by simpa using hc) hlt
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | rw [hz8] | rw [hz16] | rw [hz24] | rw [hx8] | rw [hx16] | rw [hx24] | rw [hy8] | rw [hy16] | rw [hy24]
  · have hge : ¬ (hL s.mem x < hL s.mem y ∨ (hL s.mem x = hL s.mem y ∧
        natVal s.mem (hP s.mem x) (hL s.mem x) < natVal s.mem (hP s.mem y) (hL s.mem y))) := by
      rw [← hlvx, ← hlvy, ← cmp_bit]; simpa using hbr
    have hle := fun h => hge ((SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).2 h)
    have hyx : hL s.mem y ≤ hL s.mem x := Nat.le_of_not_lt fun h => hge (Or.inl h)
    have hYX : natVal s.mem (hP s.mem y) (hL s.mem y) ≤ natVal s.mem (hP s.mem x) (hL s.mem x) :=
      Nat.le_of_not_lt fun h => hle h
    refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hl4 hl48 x y 0xd4 (hNeg s.mem x) hxB.h hyB.h
      (fun h => (hzc0 h).1) (fun h => (hzc0 h).2) hyx hYX (by omega) (Or.inl rfl) (by simp) hnx ?_ _ rfl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, entry] <;> decide)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hA2 _ hsp.symm (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setReg_apply, Nat.reduceEqDiff,
        ↓reduceIte]) rfl)
    · rw [intZ_eq, intZ_eq]; exact resB _ hnx hny (by simpa using hc) hYX
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | rw [hz8] | rw [hz16] | rw [hz24] | rw [hx8] | rw [hx16] | rw [hx24] | rw [hy8] | rw [hy16] | rw [hy24]
  · have hlt := (SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).1 (by rw [← hlvx, ← hlvy]; exact (cmp_bit _ _ _ _).1 hbr)
    refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hl4 hl48 y x 0x128 (1 - hNeg s.mem x) hyB.h hxB.h
      (fun h => (hzc0 h).2) (fun h => (hzc0 h).1) ?_ (by omega) ?_ (Or.inr rfl) (by simp) (by omega) ?_ _ rfl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, entry] <;> decide)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hA2 _ hsp.symm (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setReg_apply, Nat.reduceEqDiff,
        ↓reduceIte]) rfl)
    · rcases (cmp_bit _ _ _ _).1 hbr with h | ⟨h, -⟩ <;> omega
    · have : hL s.mem x ≤ hL s.mem y := by rcases (cmp_bit _ _ _ _).1 hbr with h | ⟨h, -⟩ <;> omega
      omega
    · rw [intZ_eq, intZ_eq]; exact resC _ hnx hny (by simpa using hc) hlt
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | rw [hz8] | rw [hz16] | rw [hz24] | rw [hx8] | rw [hx16] | rw [hx24] | rw [hy8] | rw [hy16] | rw [hy24]
  · have hge : ¬ (hL s.mem x < hL s.mem y ∨ (hL s.mem x = hL s.mem y ∧
        natVal s.mem (hP s.mem x) (hL s.mem x) < natVal s.mem (hP s.mem y) (hL s.mem y))) := by
      rw [← hlvx, ← hlvy, ← cmp_bit]; simpa using hbr
    have hle := fun h => hge ((SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).2 h)
    have hyx : hL s.mem y ≤ hL s.mem x := Nat.le_of_not_lt fun h => hge (Or.inl h)
    have hYX : natVal s.mem (hP s.mem y) (hL s.mem y) ≤ natVal s.mem (hP s.mem x) (hL s.mem x) :=
      Nat.le_of_not_lt fun h => hle h
    refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hl4 hl48 x y 0xd4 (hNeg s.mem x) hxB.h hyB.h
      (fun h => (hzc0 h).1) (fun h => (hzc0 h).2) hyx hYX (by omega) (Or.inl rfl) (by simp) hnx ?_ _ rfl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, entry] <;> decide)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hA2 _ hsp.symm (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setReg_apply, Nat.reduceEqDiff,
        ↓reduceIte]) rfl)
    · rw [intZ_eq, intZ_eq]; exact resB _ hnx hny (by simpa using hc) hYX
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | rw [hz8] | rw [hz16] | rw [hz24] | rw [hx8] | rw [hx16] | rw [hx24] | rw [hy8] | rw [hy16] | rw [hy24]

end FvModexp.Arm64.IntAS
