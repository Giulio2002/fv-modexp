import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64): the two `return z.setWord(1)` paths (`y == 0`: fn+0x538, `x == 1`: fn+0xd4)

`z.setWord(1)` (nat.go:74-79) = `z.make(1)` (reuse when `cap z ≠ 0`, else `makeslice(Word, 1, 1)`), `z[0] = 1`; the
result `(p, 1, c)` is stored to the result slots (`SP' + 176..200`) and returned (`LDP` FP/LR, `ADD $256`, `RET`).
Continuation form: `FA` (reuse) / `FB` (fresh block, the contract's raw facts).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

theorem out_inR' {a n p k : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hin : InRanges p k rs) :
    a + n ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem h hr
  omega

theorem out_sub' {a n b k : Nat} : ∀ {rs : List (Nat × Nat)}, Outside a n rs → a ≤ b → b + k ≤ a + n → Outside b k rs
  | [], _, _, _ => trivial
  | (_, _) :: _, ⟨h1, h2⟩, hb, hk => ⟨by omega, out_sub' h2 hb hk⟩

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `return z.setWord(1)` from `pc0 ∈ {fn+0xd4, fn+0x538}` (`SP' = sp + 1056`, `z = (zp, zc)` in `X0`/`X2`) -/
theorem one (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibN.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp zp zc f29 pc0 : Nat) (M : Memory) (r18 : BitVec 64)
    (hpc0 : pc0 = 1786756 ∨ pc0 = 1787880)
    (hal : sp % 16 = 0) (hK : 4304 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 1432) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 1432) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 1432))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hd : Extracted.program.DataLoaded M) (hro : RoOut R) (hty : Outside StackNat.wT 16 R.rt)
    (hzc : zc < 2 ^ 64) (hzp : zp < 2 ^ 64)
    (hz : 0 < zc → M.accessible zp 8 true = true ∧ zp + 8 ≤ 2 ^ 48 ∧ Apart zp 8 (sp - K) (K + 1432))
    (hok : zc = 0 → R.ok (Extracted.program.contractAddr "runtime.makeslice") [StackNat.wT, 1, 1] ∧
      blockSize 8 true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (h29v : M.readLE (sp + 1048) 8 = f29) (h30v : M.readLE (sp + 1056) 8 = ret0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pc0) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (FA : 0 < zc → ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 1312) → s'.regs 29 = BitVec.ofNat 64 f29 →
      s'.regs 0 = BitVec.ofNat 64 zp → s'.regs 1 = 1#64 → s'.regs 2 = BitVec.ofNat 64 zc → s'.regs 18 = r18 →
      s'.regs 28 = BitVec.ofNat 64 g → MemFrame M s'.mem [(zp, zp + 8), (sp + 1232, sp + 1256)] →
      s'.mem.readLE zp 8 = 1 → s'.mem.regions = M.regions → F s')
    (FB : zc = 0 → ∀ (s' : State) (p r : Nat) (m : Memory),
      LiveFrame M m L [] → MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1088)]) →
      m.regions = M.regions → ApartAll p r L → InRanges p r R.rt → p + r ≤ 2 ^ 48 → M.accessible p r true = true →
      p % 8 = 0 → 8 ≤ r → r = blockSize 8 true → R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m) →
      s'.sp = BitVec.ofNat 64 (sp + 1312) → s'.regs 29 = BitVec.ofNat 64 f29 →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = 1#64 → s'.regs 2 = 1#64 → s'.regs 18 = r18 →
      s'.regs 28 = BitVec.ofNat 64 g → MemFrame m s'.mem [(p, p + 8), (sp + 1232, sp + 1256)] →
      s'.mem.readLE p 8 = 1 → s'.mem.regions = M.regions → F s') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have es : BitVec.ofNat 64 (sp + 1056) - 8#64 = BitVec.ofNat 64 (sp + 1048) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 1056) + 256#64 = BitVec.ofNat 64 (sp + 1312) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hfa : Apart (sp + 1048) 16 (sp + 1232) 24 := by unfold Apart; omega
  by_cases hc : 0 < zc
  · obtain ⟨hza, hz48, hzw⟩ := hz hc
    unfold Apart at hzw
    have h29' : (M.writeLE zp 8 1).readLE (sp + 1048) 8 = f29 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h29v
    have h30' : (M.writeLE zp 8 1).readLE (sp + 1056) 8 = ret0 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h30v
    rcases hpc0 with rfl | rfl
    all_goals
      janus_run [es, es2, h29', h30']
      refine FA hc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | (janus_simp; done) | skip
      all_goals first
        | (repeat (first
            | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega)
            | refine MemFrame.writeLE ?_ _ (r := (zp, zp + 8)) (by simp) (by simp only; omega) (by simp only; omega))
           exact MemFrame.refl _ _)
        | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
            BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
  · have hz0 : zc = 0 := by omega
    obtain ⟨hok1, hbs⟩ := hok hz0
    have hwt : Apart StackNat.wT 16 (sp - K) (K + 1432) := apart_of_data hd 1 (by decide) (by decide) hwacc
    janus_data hd
    janus_eval_nat h_t : StackNat.wT
    rw [h_t] at hty hok1 hwt
    unfold Apart at hwt hgw
    have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp + 1056 - 4096 ∨ sp + 1048 ≤ r.1) ∧
        (r.1 + (r.2 - r.1) ≤ sp + 1064 ∨ sp + 1064 + 24 ≤ r.1) := by
      intro r hr
      have := hLs r hr
      simp only [Outside, and_true] at this
      omega
    subst hz0
    rcases hpc0 with rfl | rfl
    all_goals
      janus_run [es, es2] until [1786784, 1787908] calls [hmk.pos]
      rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ _
      have hfo : Outside (sp + 1048) 16 (R.rt ++ [(sp - 3040, sp + 1048), (sp + 1056 + 8, sp + 1056 + 8 + 24)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨out_sub' hwrt (by omega) (by omega), by omega, by omega⟩
      have m29 : m.readLE (sp + 1048) 8 = f29 := by
        rw [hMF.readLE _ _ (out_sub' hfo (Nat.le_refl _) (by omega))]; exact h29v
      have m30 : m.readLE (sp + 1056) 8 = ret0 := by
        rw [hMF.readLE _ _ (out_sub' hfo (by omega) (by omega))]; exact h30v
      have hMF' : MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1088)]) :=
        hMF.mono fun a k ho => by
          simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
      have hpw : sp - K + (K + 1432) ≤ ptr.toNat ∨ ptr.toNat + 8 ≤ sp - K := out_inR' hwrt hIn
      have m29' : (m.writeLE ptr.toNat 8 1).readLE (sp + 1048) 8 = f29 := by
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact m29
      have m30' : (m.writeLE ptr.toNat 8 1).readLE (sp + 1056) 8 = ret0 := by
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact m30
      have hr48 := hret.user
      janus_run [es, es2, m29', m30']
      refine FB rfl _ ptr.toNat 8 m hLF hMF' hrg1 hAp hIn (by omega) hacc h8 (by decide) (by decide) hinv' ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | (janus_simp; done) | skip
      all_goals first
        | (repeat (first
            | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega)
            | refine MemFrame.writeLE ?_ _ (r := (ptr.toNat, ptr.toNat + 8)) (by simp) (by simp only; omega)
                (by simp only; omega))
           exact MemFrame.refl _ _)
        | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
            BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
        | (simp only [Memory.regions_writeLE]; exact hrg1)

end FvModexp.Arm64.ExpN
