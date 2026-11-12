import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4XnR

/-!
# window-4 prologue (arm64): path B of the `x` normalisation, `copy(rr, x); clear(rr[len x:])` (nat.go:1383-1385)

`xnB`: from the return of `rr := stk.nat(n)` (`bSnRet`) to `xJ`; `xnBpost`: the pure post (frames, value).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

abbrev mvRet : Nat := 1799152

/-- the ranges written between `bSnRet` and `xJ` -/
@[reducible] def xbW (sp rr n : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24), (sp + 208, sp + 216), (sp + 424, sp + 432), (rr, rr + 8 * n)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnBpost {R : RtInv} {L : List (Nat × Nat)} {g sp n xp xl rr b : Nat} {M m1 m2 : Memory}
    (he : W4Loop.Env R L g sp M) (hn : n ≤ 128) (hxl : xl < n)
    (hxh : InRanges xp (8 * xl) L ∨ Outside xp (8 * xl) R.rt) (hxw : Apart xp (8 * xl) (sp - 4288) (4288 + 1040))
    (hrh : InRanges rr (8 * n) L ∨ Outside rr (8 * n) R.rt) (hrw : Apart rr (8 * n) (sp - 4288) (4288 + 1040))
    (hrx : Apart rr (8 * n) xp (8 * xl))
    (hF1 : MemFrame ((M.writeLE (sp + 208) 8 n).writeLE (sp + 424) 8 rr) m1
      (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24)] ++ [(rr, rr + 8 * xl)]))
    (hL1 : LiveFrame ((M.writeLE (sp + 208) 8 n).writeLE (sp + 424) 8 rr) m1 L [(rr, rr + 8 * xl)])
    (hC1 : Mem.Copied ((M.writeLE (sp + 208) 8 n).writeLE (sp + 424) 8 rr) m1 rr xp (8 * xl))
    (hrg1 : m1.regions = ((M.writeLE (sp + 208) 8 n).writeLE (sp + 424) 8 rr).regions)
    (hF2 : MemFrame m1 m2
      (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 16)] ++ [(rr + 8 * xl, rr + 8 * xl + 8 * (n - xl))]))
    (hL2 : LiveFrame m1 m2 L [(rr + 8 * xl, rr + 8 * xl + 8 * (n - xl))])
    (hI2 : R.inv b L g (view R.rt L m2)) (hZ2 : Mem.Zeroed m2 (rr + 8 * xl) (8 * (n - xl)))
    (hrg2 : m2.regions = m1.regions) :
    MemFrame M m2 (R.rt ++ xbW sp rr n) ∧ LiveFrame M m2 L [(rr, rr + 8 * n)] ∧ R.inv b L g (view R.rt L m2) ∧
      m2.regions = M.regions ∧ m2.readLE rr (8 * n) = M.readLE xp (8 * xl) := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have u1 := hrw; have u2 := hxw; have u3 := hrx
  unfold Apart at u1 u2 u3
  have hw0 : MemFrame M ((M.writeLE (sp + 208) 8 n).writeLE (sp + 424) 8 rr) (R.rt ++ xbW sp rr n) := by
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 208, sp + 216)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 424, sp + 432)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  have hLw : LiveFrame M ((M.writeLE (sp + 208) 8 n).writeLE (sp + 424) 8 rr) L [(rr, rr + 8 * n)] := by
    repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  refine ⟨?_, ?_, hI2, by rw [hrg2, hrg1]; simp only [Memory.regions_writeLE], ?_⟩
  · refine (hw0.trans hF1 (fun a k h => ⟨h, ?_⟩)).trans hF2 (fun a k h => ⟨h, ?_⟩)
    · simp only [xbW, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, by omega, by omega⟩, by omega⟩
    · simp only [xbW, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, by omega, by omega⟩, by omega⟩
  · refine (hLw.trans ⟨fun a k hin hout => hL1.readLE a k hin ?_⟩ (fun _ _ h => h)).trans
      ⟨fun a k hin hout => hL2.readLE a k hin ?_⟩ (fun _ _ h => h)
    · simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
    · simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
  · rw [show 8 * n = 8 * xl + 8 * (n - xl) by omega, Memory.readLE_add, FvModexp.Expmc.readLE_zeroed hZ2,
      Nat.mul_zero, Nat.add_zero]
    have e2 : m2.readLE rr (8 * xl) = m1.readLE rr (8 * xl) := by
      rcases hrh with h | h
      · exact hL2.readLE _ _ (h.sub (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)
      · exact hF2.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨h.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
    rw [e2, FvModexp.Expmc.readLE_of_copied hC1]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem xnB (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hclr : MemclrNoHeapPointersLive (LibW.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (L : List (Nat × Nat)) (g sp n xp xl rr st ylen mp : Nat) (M : Memory)
    (he : W4Loop.Env R L g sp M) (hn : n ≤ 128) (hxl : xl < n)
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48)
    (hxh : InRanges xp (8 * xl) L ∨ Outside xp (8 * xl) R.rt) (hxw : Apart xp (8 * xl) (sp - 4288) (4288 + 1040))
    (hra : M.accessible rr (8 * n) true = true) (hr48 : rr + 8 * n ≤ 2 ^ 48)
    (hrh : InRanges rr (8 * n) L ∨ Outside rr (8 * n) R.rt) (hrw : Apart rr (8 * n) (sp - 4288) (4288 + 1040))
    (hrx : Apart rr (8 * n) xp (8 * xl)) (hrx' : rr ≠ xp) (hrG : Apart rr (8 * n) (g + 16) 8)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [rr, xp, 8 * xl])
    (hokc : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rr + 8 * xl, 8 * (n - xl)])
    (b : Nat) (hinv : R.inv b L g (view R.rt L M))
    (r1024 : M.readLE (sp + 1024) 8 = n) (r312 : M.readLE (sp + 312) 8 = xl) (r896 : M.readLE (sp + 896) 8 = xp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 bSnRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 rr) (h1 : S.regs 1 = BitVec.ofNat 64 n) (h2 : S.regs 2 = BitVec.ofNat 64 n)
    (r960 : M.readLE (sp + 960) 8 = st) (r1000 : M.readLE (sp + 1000) 8 = ylen) (r1016 : M.readLE (sp + 1016) 8 = mp)
    (r18 r29 : BitVec 64) (h18 : S.regs 18 = r18) (h29 : S.regs 29 = r29)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (KX : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 xJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 rr → S'.regs 5 = BitVec.ofNat 64 n →
      S'.regs 6 = BitVec.ofNat 64 n → S'.regs 8 = BitVec.ofNat 64 ylen → S'.regs 10 = BitVec.ofNat 64 mp →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 →
      S'.mem = M' → MemFrame M M' (R.rt ++ xbW sp rr n) → LiveFrame M M' L [(rr, rr + 8 * n)] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions → M'.readLE rr (8 * n) = M.readLE xp (8 * xl) →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hLs2 : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 16 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have u1 := hrw; have u2 := hxw; have u3 := hrx
  unfold Apart at u1 u2 u3
  have hr8 : InRanges rr (8 * xl) L ∨ Outside rr (8 * xl) R.rt :=
    hrh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hra8 : M.accessible rr (8 * xl) true = true := Memory.accessible_mono _ hra (Nat.le_refl _) (by omega)
  have hrc : InRanges (rr + 8 * xl) (8 * (n - xl)) L ∨ Outside (rr + 8 * xl) (8 * (n - xl)) R.rt :=
    hrh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have hne : BitVec.ofNat 64 rr ≠ BitVec.ofNat 64 xp := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hm : (xl &&& ((BitVec.ofNat 64 xl - BitVec.ofNat 64 n).sshiftRight 63).toNat) = xl := by
    have hsr : (BitVec.ofNat 64 xl - BitVec.ofNat 64 n).sshiftRight 63 = BitVec.allOnes 64 := by
      have hmsb : (BitVec.ofNat 64 xl - BitVec.ofNat 64 n).msb = true := by
        rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      ext i hi
      rw [BitVec.getElem_sshiftRight, BitVec.getElem_allOnes]
      split
      · obtain rfl : i = 0 := by omega
        rw [BitVec.msb_eq_getLsbD_last] at hmsb
        simpa using hmsb
      · exact hmsb
    rw [hsr, BitVec.toNat_allOnes, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hsub : (18446744073709551616 - xl + n) % 18446744073709551616 = n - xl := by omega
  have hrr : (rr + 8 * xl) % 18446744073709551616 = rr + 8 * xl := Nat.mod_eq_of_lt (by omega)
  have hca : M.accessible (rr + 8 * xl) (8 * (n - xl)) true = true :=
    M.accessible_sub hra (Or.inr rfl) (by omega) (by omega)
  janus_run [r1024, r312, r896, lsl3, e8n xl (by omega), e8n (n - xl) (by omega), hne] until [mvRet]
    calls [hmv L b]
  rename_i _ _ _ m1 _ _ hF1 hL1 hI1 hC1
  have hg1' : m1.readLE (g + 16) 8 + 4096 < sp := by
    have hgw' := hgw; unfold Apart at hgw'
    have ho : Outside (g + 16) 8 (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24)] ++ [(rr, rr + 8 * xl)]) := by
      have hrG' := hrG; unfold Apart at hrG'
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hgrt, by omega, by omega⟩, by omega⟩
    rw [hF1.readLE _ _ ho]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; omega
  janus_run [r1024, r312, r896, r960, r1000, r1016, hm, hsub, hrr, e8n (n - xl) (by omega)] until [xJ]
    calls [hclr L b]
  rename_i _ _ _ m2 _ _ hF2 hL2 hI2 hZ2
  obtain ⟨p1, p2, p3, p4, p5⟩ := xnBpost he hn hxl hxh hxw hrh hrw hrx hF1 hL1 hC1 hrg1 hF2 hL2 hI2 hZ2
    hrg2
  refine KX _ m2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl p1 p2 p3 p4 p5
  all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.W4Pro
