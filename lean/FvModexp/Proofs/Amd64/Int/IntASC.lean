import FvModexp.Proofs.Amd64.Int.IntASB
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): the comparison `x.abs.cmp(y.abs)` and paths B / C

From the entry of `nat.cmp` (asm's `CmpSum.cmp_summary`; return `+0xb7`), the sign test `TESTQ AX, AX; JL`, the
reloads from the spills `0x60/0x68/0x70(SP)` and the `nat.sub` call set-up, then `pathSub` with `(u, v) = (x, y)`
(`+0xf4`) or `(y, x)` (`+0x15d`). Twin of the arm64 `IntAS.pathBC`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.IntAS

/-- `AtCall` after `nat.cmp` returned and the `CALL` of `nat.sub` pushed its return address -/
theorem atCall_cmp {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s S S' : State}
    (hpre : Pre R b L z x y s) (hA : AtCall s S z x) {m : Arm64.Memory} (hf : MemFrame S.mem m (CmpSum.frame S))
    (r : Nat) (hsp : S'.regs 4 = s.regs 4 - 96#64) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hdf : S'.df = s.df) (hx15 : S'.xmm 15 = s.xmm 15) (h5 : S'.regs 5 = s.regs 4 - 8#64)
    (hm : S'.mem = m.writeLE ((s.regs 4).toNat - 96) 8 r) (hreg : m.regions = S.mem.regions) :
    AtCall s S' z x := by
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hspT : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  simp only [CmpSum.frame, hspT] at hf
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 56 ≤ a) →
      S'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h
    rw [hm, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hf.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hF2 : MemFrame m S'.mem [((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by rw [hm]; janus_frame
  refine ⟨hsp, h14, hfs, hdf, hx15, h5, ((hA.mf.trans (rs'' := win s 4536 32) hf fun a n ho => ?_).trans hF2 fun a n ho => ?_),
    by rw [hm, Arm64.Memory.regions_writeLE, hreg]; exact hA.reg, ?_, ?_, ?_, ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho, by omega, by omega, by omega⟩
  · simp only [win, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho, by omega⟩
  · rw [hrd _ _ (by omega)]; exact hA.mbp
  · rw [hrd _ _ (by omega)]; exact hA.ra
  · rw [hrd _ _ (by omega)]; exact hA.zs
  · rw [hrd _ _ (by omega)]; exact hA.ng

/-- the sign bit of `nat.cmp`'s result: `x < y` by length first, then value -/
theorem cmp_msb (m n X Y : Nat) :
    (CmpSum.cmpRes m n X Y).msb = true ↔ (m < n ∨ (m = n ∧ X < Y)) := by
  unfold CmpSum.cmpRes
  by_cases h1 : m < n
  · rw [if_pos h1]; exact ⟨fun _ => Or.inl h1, fun _ => by decide⟩
  · by_cases h2 : n < m
    · rw [if_neg h1, if_pos h2]; exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
    · by_cases h3 : X < Y
      · rw [if_neg h1, if_neg h2, if_pos h3]; exact ⟨fun _ => Or.inr ⟨by omega, h3⟩, fun _ => by decide⟩
      · by_cases h4 : Y < X
        · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          exact ⟨fun h => absurd h (by decide), fun h => by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the comparison and paths B / C, from the entry of `nat.cmp` to `RET` -/
theorem pathBC (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) (hpre : Pre R b L z x y s)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hc : sub = true ↔ hNeg s.mem x = hNeg s.mem y)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6184128) (hrd : S.mem.readLE (S.regs 4).toNat 8 = entry sub + 0xb7)
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem x)) (h3 : S.regs 3 = BitVec.ofNat 64 (hL s.mem x))
    (h7 : S.regs 7 = BitVec.ofNat 64 (hP s.mem y)) (h6 : S.regs 6 = BitVec.ofNat 64 (hL s.mem y))
    (hA : AtCall s S z x) (hxs : S.mem.readLE ((s.regs 4).toNat + 16) 8 = x)
    (hys : S.mem.readLE ((s.regs 4).toNat + 24) 8 = y) :
    ReachesRet (LibIntAS.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Post sub R b L z x y s s' := by
  have hcpre := cmpPre_of hpre hA hrd (by cases sub <;> simp [entry]) h0 h3 h7 h6
  refine ReachesRet.call_regions (cmpSum impl hap) hpc hcpre fun S1 hr hq hrg => ?_
  obtain ⟨v1, v2, v6, f, m, rfl, hf⟩ := hq
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hspT : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  have hfB := Box.mk hf
  simp only [CmpSum.frame, hspT] at hf
  have hrdm : ∀ a n, (a + n ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 56 ≤ a) → m.readLE a n = S.mem.readLE a n :=
    fun a n h => hf.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hmx : m.readLE ((s.regs 4).toNat + 16) 8 = x := by rw [hrdm _ _ (by omega)]; exact hxs
  have hmy : m.readLE ((s.regs 4).toNat + 24) 8 = y := by rw [hrdm _ _ (by omega)]; exact hys
  have hmz : m.readLE ((s.regs 4).toNat + 8) 8 = z := by rw [hrdm _ _ (by omega)]; exact hA.zs
  have hsp := hA.sp
  have hsp96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := sp96 hsp0
  have hacc : ∀ a n w, m.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hf.accessible, hA.mf.accessible]
  have hmw : m.accessible ((s.regs 4).toNat - 4536) (4536 + 32) true = true := by rw [hacc]; exact hpre.1.2.1.2.2
  have hmzA : m.accessible z 32 false = true := by
    rw [hacc]; exact Arm64.Memory.accessible_weaken _ hpre.2.2.2.2.2.1
  have hmxA : m.accessible x 32 false = true := by rw [hacc]; exact hpre.2.2.2.1.2.1
  have hmyA : m.accessible y 32 false = true := by rw [hacc]; exact hpre.2.2.2.2.1.2.1
  have hzo := hpre.2.2.2.2.2.2.2.1
  have hxo := hpre.2.2.2.1.2.2.2.1
  have hyo := hpre.2.2.2.2.1.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  have hdr : ∀ a, (a + 32 ≤ (s.regs 4).toNat - 4536 ∨ (s.regs 4).toNat + 32 ≤ a) → ∀ k, k + 8 ≤ 32 →
      m.readLE (a + k) 8 = s.mem.readLE (a + k) 8 := fun a ha k hk => by
    rw [hrdm _ _ (by omega)]
    exact hA.mf.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hz8 := hdr z hzo 8 (by omega); have hz16 := hdr z hzo 16 (by omega); have hz24 := hdr z hzo 24 (by omega)
  have hx8 := hdr x hxo 8 (by omega); have hx16 := hdr x hxo 16 (by omega); have hx24 := hdr x hxo 24 (by omega)
  have hy8 := hdr y hyo 8 (by omega); have hy16 := hdr y hyo 16 (by omega); have hy24 := hdr y hyo 24 (by omega)
  have hx := hpre.2.2.2.1
  have hy := hpre.2.2.2.2.1
  have hzx := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc0 : 0 < hC s.mem z → _ := fun h => (hzx h).2.2.2
  have hnx := hx.1
  have hny := hy.1
  have hXn := hx.2.2.2.2.2.2.2.2.2.2.1
  have hYn := hy.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hx.2.2.2.2.1
  have hyl := hy.2.2.2.2.1
  have hxa := hx.2.2.2.2.2.2.2.2.2.2.2
  have hya := hy.2.2.2.2.2.2.2.2.2.2.2
  simp only [win, outside_cons, outside_nil, and_true] at hxa hya
  have hlvx : Asm.lv S.mem (hP s.mem x) (hL s.mem x) = natVal s.mem (hP s.mem x) (hL s.mem x) :=
    hA.mf.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hlvy : Asm.lv S.mem (hP s.mem y) (hL s.mem y) = natVal s.mem (hP s.mem y) (hL s.mem y) :=
    hA.mf.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hpreB : Box (Pre R b L z x y s) := ⟨hpre⟩
  have hAB : Box (AtCall s S z x) := ⟨hA⟩
  have hxB : Box (OpR R L s x) := ⟨hx⟩
  have hyB : Box (OpR R L s y) := ⟨hy⟩
  have hsa : (s.regs 4).toNat + 32 ≤ 2 ^ 48 := hpre.1.2.1.2.1
  have hz48 : z + 32 ≤ 2 ^ 48 := hpre.2.2.2.2.2.2.1
  have hx48 : x + 32 ≤ 2 ^ 48 := hpre.2.2.2.1.2.2.1
  have hy48 : y + 32 ≤ 2 ^ 48 := hpre.2.2.2.2.1.2.2.1
  rw [hspT] at hrd
  clear hpre hA hcpre hf hrdm hdr hacc hx hy hzx
  cases sub
  · simp only [entry, Bool.false_eq_true, ↓reduceIte] at hr hrd ⊢
    janus64_run [hrd, hmx, hmy, hmz, hsp, hsp96, hmw, hmzA, hmxA, hmyA, hz8, hz16, hz24, hx8, hx16, hx24, hy8, hy16, hy24]
      until [6183136]
    · (
        have hlt := (SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).1
           (by rw [← hlvx, ← hlvy]; exact (cmp_msb _ _ _ _).1 hbr)
        have hxy : hL s.mem x ≤ hL s.mem y := by rcases (cmp_msb _ _ _ _).1 hbr with h | ⟨h, -⟩ <;> omega
        refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hx15 hdf hra47 y x 0x15d (1 - hNeg s.mem x)
          hyB.h hxB.h (fun h => (hzc0 h).2) (fun h => (hzc0 h).1) hxy (by omega) (by omega) (Or.inr rfl) (by simp)
          (by omega) ?_ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          (atCall_cmp hpreB.h hAB.h hfB.h _ ?_ ?_ ?_ ?_ ?_ ?_ rfl hrg)
        · rw [intZ_eq, intZ_eq]; exact resC _ hnx hny (by simpa [entry] using hc) hlt
        · (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self, entry]) <;> decide
        all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
        all_goals first | exact hAB.h.g | exact hAB.h.fs | exact hAB.h.df | exact hAB.h.x15 | exact hAB.h.bp)
    · (
        have hge : ¬ (hL s.mem x < hL s.mem y ∨ (hL s.mem x = hL s.mem y ∧
            natVal s.mem (hP s.mem x) (hL s.mem x) < natVal s.mem (hP s.mem y) (hL s.mem y))) := by
          rw [← hlvx, ← hlvy, ← cmp_msb]; simpa using hbr
        have hle := fun h => hge ((SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).2 h)
        have hyx : hL s.mem y ≤ hL s.mem x := Nat.le_of_not_lt fun h => hge (Or.inl h)
        have hYX : natVal s.mem (hP s.mem y) (hL s.mem y) ≤ natVal s.mem (hP s.mem x) (hL s.mem x) :=
          Nat.le_of_not_lt fun h => hle h
        refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hx15 hdf hra47 x y 0xf4 (hNeg s.mem x)
          hxB.h hyB.h (fun h => (hzc0 h).1) (fun h => (hzc0 h).2) hyx hYX (by omega) (Or.inl rfl) (by simp) hnx ?_ _ rfl
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          (atCall_cmp hpreB.h hAB.h hfB.h _ ?_ ?_ ?_ ?_ ?_ ?_ rfl hrg)
        · rw [intZ_eq, intZ_eq]; exact resB _ hnx hny (by simpa [entry] using hc) hYX
        · (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self, entry]) <;> decide
        all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
        all_goals first | exact hAB.h.g | exact hAB.h.fs | exact hAB.h.df | exact hAB.h.x15 | exact hAB.h.bp)
  · simp only [entry, Bool.false_eq_true, ↓reduceIte] at hr hrd ⊢
    janus64_run [hrd, hmx, hmy, hmz, hsp, hsp96, hmw, hmzA, hmxA, hmyA, hz8, hz16, hz24, hx8, hx16, hx24, hy8, hy16, hy24]
      until [6183136]
    · (
        have hlt := (SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).1
           (by rw [← hlvx, ← hlvy]; exact (cmp_msb _ _ _ _).1 hbr)
        have hxy : hL s.mem x ≤ hL s.mem y := by rcases (cmp_msb _ _ _ _).1 hbr with h | ⟨h, -⟩ <;> omega
        refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hx15 hdf hra47 y x 0x15d (1 - hNeg s.mem x)
          hyB.h hxB.h (fun h => (hzc0 h).2) (fun h => (hzc0 h).1) hxy (by omega) (by omega) (Or.inr rfl) (by simp)
          (by omega) ?_ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          (atCall_cmp hpreB.h hAB.h hfB.h _ ?_ ?_ ?_ ?_ ?_ ?_ rfl hrg)
        · rw [intZ_eq, intZ_eq]; exact resC _ hnx hny (by simpa [entry] using hc) hlt
        · (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self, entry]) <;> decide
        all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
        all_goals first | exact hAB.h.g | exact hAB.h.fs | exact hAB.h.df | exact hAB.h.x15 | exact hAB.h.bp)
    · (
        have hge : ¬ (hL s.mem x < hL s.mem y ∨ (hL s.mem x = hL s.mem y ∧
            natVal s.mem (hP s.mem x) (hL s.mem x) < natVal s.mem (hP s.mem y) (hL s.mem y))) := by
          rw [← hlvx, ← hlvy, ← cmp_msb]; simpa using hbr
        have hle := fun h => hge ((SubMod2N.cmp_lt_iff s.mem _ _ _ _ hXn hYn).2 h)
        have hyx : hL s.mem y ≤ hL s.mem x := Nat.le_of_not_lt fun h => hge (Or.inl h)
        have hYX : natVal s.mem (hP s.mem y) (hL s.mem y) ≤ natVal s.mem (hP s.mem x) (hL s.mem x) :=
          Nat.le_of_not_lt fun h => hle h
        refine pathSub impl hap R hmk hmv hwb _ b L z x y s hpreB.h hx15 hdf hra47 x y 0xf4 (hNeg s.mem x)
          hxB.h hyB.h (fun h => (hzc0 h).1) (fun h => (hzc0 h).2) hyx hYX (by omega) (Or.inl rfl) (by simp) hnx ?_ _ rfl
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          (atCall_cmp hpreB.h hAB.h hfB.h _ ?_ ?_ ?_ ?_ ?_ ?_ rfl hrg)
        · rw [intZ_eq, intZ_eq]; exact resB _ hnx hny (by simpa [entry] using hc) hYX
        · (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self, entry]) <;> decide
        all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
        all_goals first | exact hAB.h.g | exact hAB.h.fs | exact hAB.h.df | exact hAB.h.x15 | exact hAB.h.bp)

end FvModexp.Amd64.IntAS
