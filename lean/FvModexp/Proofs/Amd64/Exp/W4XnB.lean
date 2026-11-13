import FvModexp.Proofs.Amd64.Exp.W4XnR
import FvModexp.Proofs.Amd64.Exp.W4Defs

set_option autoImplicit false

/-!
# window-4 prologue (amd64): path B of the `x` normalisation, `copy(rr, x); clear(rr[len x:])` (nat.go:1383-1385)
(agent expmc s55; twin of `Arm64.W4XnB1`)

`xnB`: from the return of `rr := stk.nat(n)` (`bSnRet` = fn+0x325) to `xJ`: the capacity check (`cap rr = n`), the
spills 0xc8 = `cap rr`, 0x1a0 = `rr`, `rr ≠ xp` (so the copy runs), `memmove(rr, xp, 8·len x)` (return `mvRet`),
`memclrNoHeapPointers(rr + 8·len x, 8·(n - len x))` (return `clrRet`; `len x < n`), the reloads.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf)

abbrev mvRet : Nat := 6206413
abbrev clrRet : Nat := 6206491

/-- the ranges written between `bSnRet` and `xJ` -/
@[reducible] def xbW (sp rr n : Nat) : List (Nat × Nat) :=
  [(sp - 8 - 4096, sp + 24), (sp + 0xc8, sp + 0xd0), (sp + 0x1a0, sp + 0x1a8), (rr, rr + 8 * n)]

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem xnB (impl : List Amd64.Segment) {R : RtInv}
    (hmv : MemmoveLive64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hclr : MemclrNoHeapPointersLive64 (LibW.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    {ret : W64} {Q : State → Prop}
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n xp xl rr st zp zc : Nat) (M : Memory)
    (he : Env R L g fs sp M) (hn : n ≤ 128) (hxl : xl < n)
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48)
    (hxw : Apart xp (8 * xl) (sp - 4296) (4296 + 0x3c0))
    (hra : M.accessible rr (8 * n) true = true) (hr48 : rr + 8 * n ≤ 2 ^ 48)
    (hrh : InRanges rr (8 * n) L ∨ Outside rr (8 * n) R.rt) (hrw : Apart rr (8 * n) (sp - 4296) (4296 + 0x3c0))
    (hrx : Apart rr (8 * n) xp (8 * xl)) (hrx' : rr ≠ xp) (hrG : Apart rr (8 * n) (g + 16) 8)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [rr, xp, 8 * xl])
    (hokc : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rr + 8 * xl, 8 * (n - xl)])
    (hinv : R.inv b L g (view R.rt L M))
    (hacc2 : M.accessible (sp + 0x3c0) 0x20 false = true) (hcrt : Outside (sp + 0x3c0) 0x20 R.rt)
    (hrc2 : Apart rr (8 * n) (sp + 0x3c0) 0x20)
    (r3b0 : M.readLE (sp + 0x3b0) 8 = n) (r130 : M.readLE (sp + 0x130) 8 = xl) (r368 : M.readLE (sp + 0x368) 8 = xp)
    (r3d8 : M.readLE (sp + 0x3d8) 8 = st) (r3c0 : M.readLE (sp + 0x3c0) 8 = zp) (r3d0 : M.readLE (sp + 0x3d0) 8 = zc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 bSnRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 rr) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (KX : ∀ (S' : State), S'.rip = BitVec.ofNat 64 xJ → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 6 = BitVec.ofNat 64 rr → S'.regs 8 = BitVec.ofNat 64 n → S'.regs 9 = BitVec.ofNat 64 n →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 n →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      MemFrame M S'.mem (R.rt ++ xbW sp rr n) → LiveFrame M S'.mem L [(rr, rr + 8 * n)] →
      R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions →
      S'.mem.readLE rr (8 * n) = M.readLE xp (8 * xl) →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have u1 := hrw; have u2 := hxw; have u3 := hrx
  unfold Apart at u1 u2 u3
  have hr8 : InRanges rr (8 * xl) L ∨ Outside rr (8 * xl) R.rt :=
    hrh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hrc : InRanges (rr + 8 * xl) (8 * (n - xl)) L ∨ Outside (rr + 8 * xl) (8 * (n - xl)) R.rt :=
    hrh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have hca : M.accessible (rr + 8 * xl) (8 * (n - xl)) true = true :=
    M.accessible_sub hra (Or.inr rfl) (by omega) (by omega)
  have hne : (BitVec.ofNat 64 rr = BitVec.ofNat 64 xp) = False := by
    simp only [eq_iff_iff, iff_false]; intro h
    have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hlt : (BitVec.ofNat 64 n < BitVec.ofNat 64 n) = False := by simp
  have e8 : BitVec.ofNat 64 xl <<< 3 = BitVec.ofNat 64 (8 * xl) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
      ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hLs2 : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
      ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 16)] ++ [(sp - 8, sp - 8 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  subst hmem
  janus64_run [r3b0, r130, r368, hne, hlt, e8] until [mvRet] calls [hmv L b]
  rename_i _ _ _ _ m1 _ _ hF1 hL1 hI1 hC1
  have hsub : (18446744073709551616 - xl + n) % 18446744073709551616 = n - xl := by omega
  have hrr : (rr + 8 * xl) % 18446744073709551616 = rr + 8 * xl := Nat.mod_eq_of_lt (by omega)
  have hm : (((BitVec.ofNat 64 xl - BitVec.ofNat 64 n).sshiftRight 63).toNat &&& xl * 8) = xl * 8 := by
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
    rw [hsr, BitVec.toNat_allOnes, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hrr' : (xl * 8 + rr) % 18446744073709551616 = rr + 8 * xl := by omega
  have hn8 : (n - xl) * 8 = 8 * (n - xl) := by omega
  janus64_run [r3b0, r130, r368, hsub, hrr, hm, hrr', hn8] until [clrRet] calls [hclr L b]
  rename_i _ _ _ _ m2 _ _ hF2 hL2 hI2 hZ2
  have u4 := hrc2
  unfold Apart at u4
  have rd : ∀ a, (sp + 24 ≤ a ∧ a + 8 ≤ sp + 0x3c0 ∨ sp + 0x3c0 ≤ a ∧ a + 8 ≤ sp + 0x3e0) →
      m2.readLE a 8 = ((S.mem.writeLE (sp + 200) 8 n).writeLE (sp + 416) 8 rr).readLE a 8 := by
    intro a ha
    have ho : Outside a 8 R.rt := by
      rcases ha with h | h
      · exact hwrt.of_sub (by omega) (by omega)
      · exact hcrt.of_sub (by omega) (by omega)
    rw [hF2.readLE a 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨ho, by omega, by omega⟩, by omega⟩)]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hF1.readLE a 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨ho, by omega, by omega⟩, by omega⟩)]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
  have q1a0 : m2.readLE (sp + 0x1a0) 8 = rr := by
    rw [rd _ (Or.inl ⟨by omega, by omega⟩)]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have qc8 : m2.readLE (sp + 0xc8) 8 = n := by
    rw [rd _ (Or.inl ⟨by omega, by omega⟩)]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have rk : ∀ a v, (sp + 24 ≤ a ∧ a + 8 ≤ sp + 0xc8 ∨ sp + 0x1a8 ≤ a ∧ a + 8 ≤ sp + 0x3c0 ∨
      sp + 0x3c0 ≤ a ∧ a + 8 ≤ sp + 0x3e0) → S.mem.readLE a 8 = v → m2.readLE a 8 = v := by
    intro a v ha h
    rw [rd _ (by omega)]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    exact h
  have q3b0 := rk _ _ (by omega) r3b0
  have q3c0 := rk _ _ (by omega) r3c0
  have q3d0 := rk _ _ (by omega) r3d0
  have q3d8 := rk _ _ (by omega) r3d8
  janus64_run [q1a0, qc8, q3b0, q3c0, q3d0, q3d8] until [xJ]
  have hw0 : MemFrame S.mem ((S.mem.writeLE (sp + 200) 8 n).writeLE (sp + 416) 8 rr) (R.rt ++ xbW sp rr n) := by
    refine MemFrame.writeLE ?_ _ (r := (sp + 0x1a0, sp + 0x1a8)) (by simp) (by simp only; omega) (by simp only; omega)
    refine MemFrame.writeLE ?_ _ (r := (sp + 0xc8, sp + 0xd0)) (by simp) (by simp only; omega) (by simp only; omega)
    exact MemFrame.refl _ _
  have hw1 : MemFrame ((S.mem.writeLE (sp + 200) 8 n).writeLE (sp + 416) 8 rr)
      (((S.mem.writeLE (sp + 200) 8 n).writeLE (sp + 416) 8 rr).writeLE (sp - 8) 8 6206413) (R.rt ++ xbW sp rr n) :=
    MemFrame.writeLE (MemFrame.refl _ _) _ (r := (sp - 8 - 4096, sp + 24)) (by simp) (by simp only; omega)
      (by simp only; omega)
  have hw2 : MemFrame m1 (m1.writeLE (sp - 8) 8 6206491) (R.rt ++ xbW sp rr n) :=
    MemFrame.writeLE (MemFrame.refl _ _) _ (r := (sp - 8 - 4096, sp + 24)) (by simp) (by simp only; omega)
      (by simp only; omega)
  have hFall : MemFrame S.mem m2 (R.rt ++ xbW sp rr n) := by
    refine (((hw0.trans hw1 (fun a k h => ⟨h, h⟩)).trans hF1 (fun a k h => ⟨h, ?_⟩)).trans hw2
      (fun a k h => ⟨h, h⟩)).trans hF2 (fun a k h => ⟨h, ?_⟩)
    · simp only [xbW, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, by omega, by omega⟩, by omega⟩
    · simp only [xbW, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, by omega, by omega⟩, by omega⟩
  have hoL : ∀ a k, sp - 4296 ≤ a → a + k ≤ sp + 0x3c0 → Outside a k L := fun a k h1 h2 =>
    FvModexp.Expmc.outside_of_liveSep hLs h1 h2
  have hLall : LiveFrame S.mem m2 L [(rr, rr + 8 * n)] := by
    have l0 : LiveFrame S.mem (((S.mem.writeLE (sp + 200) 8 n).writeLE (sp + 416) 8 rr).writeLE (sp - 8) 8 6206413)
        L [(rr, rr + 8 * n)] :=
      (((LiveFrame.refl _ _ _).writeLE _ (hoL _ _ (by omega) (by omega))).writeLE _
        (hoL _ _ (by omega) (by omega))).writeLE _ (hoL _ _ (by omega) (by omega))
    refine (((l0.trans ⟨fun a k hin hout => hL1.readLE a k hin ?_⟩ (fun _ _ h => h)).writeLE _
      (hoL _ _ (by omega) (by omega))).trans ⟨fun a k hin hout => hL2.readLE a k hin ?_⟩ (fun _ _ h => h))
    · simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
    · simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
  have hval : m2.readLE rr (8 * n) = S.mem.readLE xp (8 * xl) := by
    rw [show 8 * n = 8 * xl + 8 * (n - xl) by omega, Arm64.Memory.readLE_add, FvModexp.Expmc.readLE_zeroed hZ2,
      Nat.mul_zero, Nat.add_zero]
    have e2 : m2.readLE rr (8 * xl) = m1.readLE rr (8 * xl) := by
      rcases hrh with h | h
      · rw [hL2.readLE _ _ (h.sub (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)]
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
      · rw [hF2.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨h.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [e2, FvModexp.Expmc.readLE_of_copied hC1]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
  refine KX _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hFall hLall hI2 (by rw [hrg2, hrg1]) hval
  all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals first | exact BitVec.sub_add_cancel _ _ | exact hsp | exact h14 | exact hx15 | exact hdf | exact hfs | rfl

end FvModexp.Amd64.W4Pro
