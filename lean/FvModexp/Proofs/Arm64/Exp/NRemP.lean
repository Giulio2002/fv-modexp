import FvModexp.Proofs.Arm64.Exp.NCall
import FvModexp.Proofs.Arm64.Exp.NCPre
import FvModexp.Proofs.Arm64.Exp.NStk

set_option autoImplicit false

/-!
# `nat.expNN` (arm64): the `y == 1` path — `z.rem(stk, x, m)` (nat.go:686) to expNN's return

From `nat.rem`'s entry (`NStk.stk`'s `KR`: `z'` = the entry `z` kept by the alias test or `nil`, `u = x`, `v = m`):
`callC` with asm's `NHyp.RemHyp` (value `X % M = X ^ 1 % M`). `zq_keep`: the `ZQ`/`ZArg` facts of a kept-or-nil `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
/-- the entry `z` kept by the alias test (`ZOK` when non-empty), or `nil`: callee `z` argument facts -/
theorem zq_keep {R : RtInv} {L L1 : List (Nat × Nat)} {g sp K st zp zc xp xl yp yl mp n zp' zc' : Nat}
    {M0 M : Memory} (hzc : zc < 2 ^ 40) (hx : LiveExt R L L1)
    (hacc : ∀ a k w, M.accessible a k w = M0.accessible a k w)
    (ew : stW M st = stW M0 st) (el : stLen M st = stLen M0 st) (ec : stCap M st = stCap M0 st)
    (hz : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g sp K st zp zc xp xl yp yl mp n M0)) ∨ (zp' = 0 ∧ zc' = 0)) :
    ZQ R L1 g sp K st xp xl yp yl mp n M zp' zc' ∧ ZArg R L sp K zp zc zp' zc' := by
  rcases hz with ⟨rfl, rfl, hzk⟩ | ⟨rfl, rfl⟩
  · rcases Nat.eq_zero_or_pos zp' with - | -
    all_goals
      rcases Nat.eq_zero_or_pos zc' with h0 | h0
      · exact ⟨⟨by omega, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩, Or.inl ⟨h0, Or.inr ⟨rfl, h0⟩⟩⟩
      · obtain ⟨⟨hH, hw, hst, hfr⟩, ha, h48, h8, -, hg, hm, hy, hxx, hgA⟩ := hzk h0
        refine ⟨⟨hzc, fun _ => ⟨h8, hx.held hH, by rw [hacc]; exact ha, h48⟩, fun _ => ⟨hw, by unfold Apart at hg ⊢; omega,
          hst, ?_, hgA, hxx, hy, hm⟩⟩, Or.inr (Or.inl ⟨rfl, rfl, hw⟩)⟩
        show Apart zp' (8 * zc') (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
        rw [ew, el, ec]; exact hfr
  · exact ⟨⟨by omega, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩

/-- `rem`'s `NoAlias` for the `z` kept by expNN's entry alias test (`¬alias(z, x)`, nat.go:640) -/
theorem noAlias_keep {zp zc xp xc yp yc : Nat}
    (hk : zc = 0 ∨ ((xc = 0 ∨ (xp + 8 * (xc - 1)) % 2 ^ 64 ≠ (zp + 8 * (zc - 1)) % 2 ^ 64) ∧
      (yc = 0 ∨ (yp + 8 * (yc - 1)) % 2 ^ 64 ≠ (zp + 8 * (zc - 1)) % 2 ^ 64))) :
    NHyp.NoAlias zp zc xp xc := by
  intro h0 h1 he
  rcases hk with h | ⟨h | h, -⟩
  · omega
  · omega
  · exact h he.symm

/-- `rem`'s `NoAlias` for the `nil` `z` of the alias branch -/
theorem noAlias_nil (xp xc : Nat) : NHyp.NoAlias 0 0 xp xc := fun h => absurd h (Nat.lt_irrefl 0)

theorem tN' {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `rem` path from `nat.rem`'s entry to expNN's return -/
theorem remPath (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} {stk : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    (hRem : NHyp.RemHyp impl R ns stk 112 needR costR)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hn11 : ns.contains Extracted.seg11.name = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 zp' zl' zc' : Nat} {s S : State}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hstk : stk ≤ K + 1056)
    (hF : MemFrame s.mem S.mem (wN sp K)) (hrg : S.mem.regions = s.mem.regions)
    (hz : (zp' = zp ∧ zl' = zl ∧ zc' = zc ∧ (0 < zc → ZOK R L g sp K st zp zc xp xl yp yl mp n s.mem)) ∨
      (zp' = 0 ∧ zl' = 0 ∧ zc' = 0))
    (hna : NHyp.NoAlias zp' zc' xp xc)
    (hy : yl = 1 ∧ s.mem.readLE yp 8 = 1)
    (hpc : S.pc = BitVec.ofNat 64 remA) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h1 : S.regs 1 = BitVec.ofNat 64 zl') (h2 : S.regs 2 = BitVec.ofNat 64 zc')
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 mp) (h8 : S.regs 8 = BitVec.ofNat 64 n)
    (h9 : S.regs 9 = BitVec.ofNat 64 mc) (h28 : S.regs 28 = s.regs 28) (h30 : S.regs 30 = BitVec.ofNat 64 1787296)
    (h29v : S.mem.readLE (sp + 1048) 8 = f29) (h30v : S.mem.readLE (sp + 1056) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, -, -, -, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, -, -⟩, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, -, hm48, -, -, -, -, -, hyl, -, hxO, -, -, -, hxl, hxp, hxc, hzp, hzlc, hzc, -,
    -, -, hst0, hst48, hsok, hstw, -, harr, hc0, -, -, -, -, -, hnR, -, -, hbud, hinv⟩ := hP'
  have hs : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have hg : (s.regs 28).toNat = g := by rw [hs28, BitVec.toNat_ofNat]; omega
  have hLF0 : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hF (liveSep_wN hLs)
  have hF0 : MemFrame s.mem S.mem (R.rt ++ wN sp K) := hF.mono fun a k ho => by rw [outside_append] at ho; exact ho.2
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0 hF0 (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have hzl' : zl' ≤ zc' := by rcases hz with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl⟩ <;> omega
  have hzc' : zc' < 2 ^ 64 := by rcases hz with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩ <;> omega
  have hzp' : zp' < 2 ^ 64 := by rcases hz with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  obtain ⟨hZQ, hZA⟩ := zq_keep (L1 := L) hzc (LiveExt.refl R L) hF0.accessible ew el ec
    (hz.imp (fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩) (fun h => ⟨h.1, h.2.2⟩))
  have hinvS : R.inv b L g (view R.rt L S.mem) :=
    Expmc.inv_frame hF (fun r hr => Or.inr (out_rt_wN hwrt r hr)) hinv
  have hrdx : natVal S.mem xp xl = natVal s.mem xp xl := rd_held hxO.1 hLF0 hF0 hxO.2.1
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  have hE := hRem b L (BitVec.ofNat 64 zp') (BitVec.ofNat 64 zl') (BitVec.ofNat 64 zc') (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 mp) (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 mc)
  rw [tN' hzp', tN' (by omega : zl' < 2 ^ 64), tN' hzc', tN' (by omega : st < 2 ^ 64), tN' hxp,
    tN' (by omega : xl < 2 ^ 64), tN' (by omega : xc < 2 ^ 64), tN' (by omega : n < 2 ^ 64), tN' (by omega : mp < 2 ^ 64),
    show segAddr Extracted.program NHyp.fnRem = remA by decide] at hE
  have hacc2 : S.mem.accessible (sp + 1048) 256 true = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  refine callC impl hap hns hn11 ret0 hret F hs hal hKs (by omega) hsp2 hLs hwrt hsok hstw hF0 hLF0 (LiveExt.refl R L)
    (mk := 0) (Nat.sub_le _ _) hZA hstk h28 ?_ ?_ (Or.inl rfl) hE hpc hSsp h30 ?_ ⟨⟨?_, by omega⟩, hna, hst0⟩ (fun s' h => cpostG_of hzp' h)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1) hacc2 h29v h30v hsl hEk
  · rw [hrdx, hrdm]
    obtain ⟨rfl, hy0⟩ := hy
    have e : natVal s.mem yp 1 = 1 := hy0
    rw [e, Nat.pow_one]
  · rw [el]; unfold NCost; omega
  · simp only [ArgsFrom]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩
  · exact cpre_at hP hF0 hLF0 hrg (LiveExt.refl R L) hinvS hSsp (h28.trans hs28) hstk hZQ hzl'
      (fun p k hpk => by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hpk
        rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩))
      hnR (by rw [el]; omega)

end FvModexp.Arm64.ExpN
