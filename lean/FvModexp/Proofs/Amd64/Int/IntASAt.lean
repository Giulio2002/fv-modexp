import FvModexp.Proofs.Amd64.Int.IntASCall

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): the state at a callee entry of the body and the frames after the call

`AtCall s S z x`: at a callee entry `RSP = RSP₀ - 96` (`PUSHQ BP; SUBQ $0x50`; the `CALL` pushed the return address),
`BP = RSP₀ - 8` (the saved `BP` at `RSP₀ - 8`), the spill `0x60(RSP') = RSP₀ + 8 := z` and the sign byte
`0x4f(RSP') = RSP₀ - 9 := x.neg`; memory changed in the window only. `frames_after`: a callee at `RSP₀ - 96` whose post
frame is `R.rt ++ win S stk1 80 ++ [z.abs]` (`stk1 ≤ 4440`) keeps the spills and gives the caller's frames.
(Twin of the arm64 `IntASA.AtCall` / `frames_after` / `frames_wider`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.IntAS

/-- see the module doc -/
structure AtCall (s S : State) (z x : Nat) : Prop where
  sp : S.regs 4 = s.regs 4 - 96#64
  g : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  x15 : S.xmm 15 = s.xmm 15
  bp : S.regs 5 = s.regs 4 - 8#64
  mf : MemFrame s.mem S.mem (win s 4536 32)
  reg : S.mem.regions = s.mem.regions
  mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  zs : S.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  ng : S.mem.readLE ((s.regs 4).toNat - 9) 1 = s.mem.readLE x 1

theorem sp96 {s : State} (h : 4536 ≤ (s.regs 4).toNat) : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl

/-- the frames after a callee at `RSP₀ - 96` whose post frame is `R.rt ++ win S stk1 80 ++ [z.abs]` -/
theorem frames_after {R : RtInv} {L : List (Nat × Nat)} {s S S' : State} {zp zc stk1 : Nat} {x z : Nat}
    (hce : CallEnv R L s 4536 32) (hk : stk1 ≤ 4440) (hA : AtCall s S z x)
    (hF : MemFrame S.mem S'.mem (R.rt ++ [((S.regs 4).toNat - stk1, (S.regs 4).toNat + 80)] ++ [(zp, zp + 8 * zc)]))
    (hLF : LiveFrame S.mem S'.mem L [(zp, zp + 8 * zc)]) (hzo : Outside zp (8 * zc) (win s 4536 32)) :
    MemFrame s.mem S'.mem (R.rt ++ win s 4536 32 ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem S'.mem L [(zp, zp + 8 * zc)] ∧
      S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ S'.mem.readLE ((s.regs 4).toNat + 8) 8 = z ∧
      S'.mem.readLE ((s.regs 4).toNat - 9) 1 = s.mem.readLE x 1 := by
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hce.2.1.1
  have hout := hce.2.2.2.2.1
  have hLs := hce.2.2.2.2.2.2.2.1
  have hspT : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  rw [hspT] at hF
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  have rd : ∀ a n, (s.regs 4).toNat - 4536 ≤ a → a + n ≤ (s.regs 4).toNat + 32 →
      (a + n ≤ (s.regs 4).toNat - 96 - stk1 ∨ (s.regs 4).toNat - 96 + 80 ≤ a) →
      S'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hF.readLE a n (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), h3⟩, by omega⟩)
  have e1 : S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [rd _ _ (by omega) (by omega) (by omega)]; exact hA.mbp
  have e3 : S'.mem.readLE ((s.regs 4).toNat + 8) 8 = z := by
    rw [rd _ _ (by omega) (by omega) (by omega)]; exact hA.zs
  have e4 : S'.mem.readLE ((s.regs 4).toNat - 9) 1 = s.mem.readLE x 1 := by
    rw [rd _ _ (by omega) (by omega) (by omega)]; exact hA.ng
  refine ⟨MemFrame.trans hA.mf hF fun a n ho => ?_, ⟨fun a n hin ho => ?_⟩, e1, e3, e4⟩
  · simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨o1, o2⟩, o4⟩ := ho
    refine ⟨o2, ⟨o1, ?_⟩, o4⟩; omega
  · rw [hLF.readLE a n hin ho]
    refine hA.mf.readLE a n ?_
    obtain ⟨r, hr, a1, a2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢
    omega

/-- a write set `[zp, zp + 8·min k c)` is inside `[zp, zp + 8·min k' c)` for `k ≤ k'` -/
theorem frames_wider {R : RtInv} {L ws : List (Nat × Nat)} {m m' : Arm64.Memory} {zp k c k' : Nat}
    (hF : MemFrame m m' (R.rt ++ ws ++ [(zp, zp + 8 * min k c)])) (hLF : LiveFrame m m' L [(zp, zp + 8 * min k c)])
    (hk : k ≤ k') :
    MemFrame m m' (R.rt ++ ws ++ [(zp, zp + 8 * min k' c)]) ∧ LiveFrame m m' L [(zp, zp + 8 * min k' c)] := by
  have hmo : ∀ a n, Outside a n [(zp, zp + 8 * min k' c)] → Outside a n [(zp, zp + 8 * min k c)] := fun a n ho => by
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  exact ⟨hF.mono fun a n ho => by simp only [outside_append] at ho ⊢; exact ⟨ho.1, hmo a n ho.2⟩,
    ⟨fun a n hin ho => hLF.readLE a n hin (hmo a n ho)⟩⟩

set_option maxRecDepth 20000 in
/-- `CmpSum.Pre` at the call of `nat.cmp` (`RSP = RSP₀ - 96`, return address `r` pushed): `AX, BX = x.abs.ptr, len`,
`DI, SI = y.abs.ptr, len` -/
theorem cmpPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s S : State} (hpre : Pre R b L z x y s)
    (hA : AtCall s S z x) {r : Nat} (hra : S.mem.readLE (S.regs 4).toNat 8 = r) (hr : r < 2 ^ 47)
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem x)) (h3 : S.regs 3 = BitVec.ofNat 64 (hL s.mem x))
    (h7 : S.regs 7 = BitVec.ofNat 64 (hP s.mem y)) (h6 : S.regs 6 = BitVec.ofNat 64 (hL s.mem y)) :
    CmpSum.Pre S := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, hx, hy, -⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hb' ha hw
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, hxa, hx48, -, -, hxo⟩ := hx
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, hya, hy48, -, -, hyo⟩ := hy
  simp only [win, outside_cons, outside_nil, and_true] at hxo hyo
  have hspT : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hA.sp]; exact sp96 hb'
  have hmf := hA.mf
  unfold CmpSum.Pre CmpSum.SliceOK
  rw [hra, h0, h3, h7, h6, hspT, tN (by omega), tN (by omega), tN (by omega), tN (by omega)]
  refine ⟨hr, by omega, by omega,
    by rw [hmf.accessible]; exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega),
    Or.inr ⟨by rw [hmf.accessible]; exact hxa, by unfold Apart; omega⟩,
    Or.inr ⟨by rw [hmf.accessible]; exact hya, by unfold Apart; omega⟩⟩

end FvModexp.Amd64.IntAS
