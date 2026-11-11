import FvModexp.Proofs.Arm64.Int.IntASCall
import FvModexp.Proofs.Arm64.Int.IntASTail
import FvModexp.Proofs.Arm64.Int.IntASVal

/-!
# `(*Int).Add` / `(*Int).Sub` (arm64): path A — the call `z.abs = z.abs.add(x.abs, y.abs)` (`+0x54`) and the tail

From the entry of `nat.add` (agent divmc's `NatAdd.ensR`) with `SP = s.sp - 96`, the spills of the prologue in place:
the call, then `tail` at `+0x58`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

open FvModexp.Arm64.RunIface (Serves)

/-- the frame and spill facts at a callee entry of the function body (`SP = s.sp - 96`) -/
structure AtCall (s S : State) (z x : Nat) : Prop where
  sp : S.sp = s.sp - 96#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 104#64
  r18 : S.regs 18 = s.regs 18
  mf : MemFrame s.mem S.mem (winA s 4560 32)
  reg : S.mem.regions = s.mem.regions
  fp : S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat
  lr : S.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat
  zs : S.mem.readLE (s.sp.toNat + 8) 8 = z
  ng : S.mem.readLE (s.sp.toNat - 9) 1 = s.mem.readLE x 1

theorem sp96 {s : State} (h : 4560 ≤ s.sp.toNat) : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl

/-- the frames after a callee at `SP - 96` whose post frame is `R.rt ++ winA S stk1 80 ++ [z.abs]` (`stk1 ≤ 4464`) -/
theorem frames_after {R : RtInv} {L : List (Nat × Nat)} {s S S' : State} {zp zc stk1 : Nat} {x z : Nat}
    (hce : CallEnv R L s 4560 32) (hk : stk1 ≤ 4464) (hA : AtCall s S z x)
    (hF : MemFrame S.mem S'.mem (R.rt ++ [(S.sp.toNat - stk1, S.sp.toNat - 8), (S.sp.toNat + 8, S.sp.toNat + 80)] ++
      [(zp, zp + 8 * zc)]))
    (hLF : LiveFrame S.mem S'.mem L [(zp, zp + 8 * zc)]) (hzo : Outside zp (8 * zc) (win s 4560 32)) :
    MemFrame s.mem S'.mem (R.rt ++ winA s 4560 32 ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem S'.mem L [(zp, zp + 8 * zc)] ∧
      S'.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat ∧ S'.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat ∧
      S'.mem.readLE (s.sp.toNat + 8) 8 = z ∧ S'.mem.readLE (s.sp.toNat - 9) 1 = s.mem.readLE x 1 := by
  have hsp0 : 4560 ≤ s.sp.toNat := hce.2.1.2.1
  have hout := hce.2.2.2.1
  have hLs := hce.2.2.2.2.2.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  rw [hspT] at hF
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  have rd : ∀ a n, s.sp.toNat - 4560 ≤ a → a + n ≤ s.sp.toNat + 32 → (a + n ≤ s.sp.toNat - 96 - stk1 ∨
      s.sp.toNat - 96 - 8 ≤ a) → (a + n ≤ s.sp.toNat - 96 + 8 ∨ s.sp.toNat - 96 + 80 ≤ a) →
      S'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3 h4
    exact hF.readLE a n (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), h3, h4⟩, by omega⟩)
  have e1 : S'.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
    rw [rd _ _ (by omega) (by omega) (by omega) (by omega)]; exact hA.fp
  have e2 : S'.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
    rw [rd _ _ (by omega) (by omega) (by omega) (by omega)]; exact hA.lr
  have e3 : S'.mem.readLE (s.sp.toNat + 8) 8 = z := by
    rw [rd _ _ (by omega) (by omega) (by omega) (by omega)]; exact hA.zs
  have e4 : S'.mem.readLE (s.sp.toNat - 9) 1 = s.mem.readLE x 1 := by
    rw [rd _ _ (by omega) (by omega) (by omega) (by omega)]; exact hA.ng
  refine ⟨MemFrame.trans hA.mf hF fun a n ho => ?_, ⟨fun a n hin ho => ?_⟩, e1, e2, e3, e4⟩
  · simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨o1, o2, o3⟩, o4⟩ := ho
    refine ⟨⟨o2, o3⟩, ⟨o1, ?_, ?_⟩, o4⟩ <;> omega
  · rw [hLF.readLE a n hin ho]
    refine hA.mf.readLE a n ?_
    obtain ⟨r, hr, a1, a2⟩ := hin
    have := hLs r hr
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path A from the entry of `nat.add` to `RET` -/
theorem pathA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) (hpre : Pre R b L z x y s)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hc : sub = true ↔ hNeg s.mem x ≠ hNeg s.mem y)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1781184) (h30 : S.regs 30 = BitVec.ofNat 64 (entry sub + 0x58))
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem z)) (h1 : S.regs 1 = BitVec.ofNat 64 (hL s.mem z))
    (h2 : S.regs 2 = BitVec.ofNat 64 (hC s.mem z)) (h3 : S.regs 3 = BitVec.ofNat 64 (hP s.mem x))
    (h4 : S.regs 4 = BitVec.ofNat 64 (hL s.mem x)) (h5 : S.regs 5 = BitVec.ofNat 64 (hC s.mem x))
    (h6 : S.regs 6 = BitVec.ofNat 64 (hP s.mem y)) (h7 : S.regs 7 = BitVec.ofNat 64 (hL s.mem y))
    (h8 : S.regs 8 = BitVec.ofNat 64 (hC s.mem y)) (hA : AtCall s S z x) :
    ReachesRet (LibIntAS.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post sub R b L z x y s s' := by
  have hS' := hypSum hap add_names (NatAdd.ensR impl hap R hmk hmv b L (BitVec.ofNat 64 (hP s.mem z))
    (BitVec.ofNat 64 (hL s.mem z)) (BitVec.ofNat 64 (hC s.mem z)) (BitVec.ofNat 64 (hP s.mem x))
    (BitVec.ofNat 64 (hL s.mem x)) (BitVec.ofNat 64 (hC s.mem x)) (BitVec.ofNat 64 (hP s.mem y))
    (BitVec.ofNat 64 (hL s.mem y)) (BitVec.ofNat 64 (hC s.mem y)))
  rw [show segAddr Extracted.program NatAdd.fn = 1781184 by decide] at hS'
  have hce := hpre.1
  have hsp0 : 4560 ≤ s.sp.toNat := hce.2.1.2.1
  have hx := hpre.2.2.2.1
  have hy := hpre.2.2.2.2.1
  have hzo := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxv := (opR_at (hA.mf.mono fun a n ho => by
    simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hx).2.2.2.2.2.2
  have hyv := (opR_at (hA.mf.mono fun a n ho => by
    simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hy).2.2.2.2.2.2
  obtain ⟨hnx, -, -, -, hxlc, hxc, hxl16, -, hx48, -, -, -⟩ := hx
  obtain ⟨hny, -, -, -, hylc, hyc, hyl16, -, hy48, -, -, -⟩ := hy
  have hzp : hP s.mem z < 2 ^ 64 := by have := Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hzl : hL s.mem z < 2 ^ 64 := by have := Memory.readLE_lt s.mem (z + 16) 8; simpa using this
  refine ReachesRet.call_regions hS' hpc ⟨?_, ?_, addPre_of hpre (by rw [hA.sp]; exact sp96 hsp0) hA.r28
    (hA.mf.mono fun a n ho => by simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hA.reg⟩
    fun S' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ _ => ?_
  · rw [h30, tN (by cases sub <;> simp [entry])]
    exact ra_of hap (by decide) sub 22 (by omega)
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  obtain ⟨p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
  simp only [NatAdd.mx, NatAdd.need] at hln hb hr1 hr2
  simp only [tN hzp, tN (show hC s.mem z < 2 ^ 64 by omega), tN (show hP s.mem x < 2 ^ 64 by omega),
    tN (show hL s.mem x < 2 ^ 64 by omega), tN (show hP s.mem y < 2 ^ 64 by omega),
    tN (show hL s.mem y < 2 ^ 64 by omega)] at hv hln hb hinv hor hF hLF hr1 hr2
  rw [hxv, hyv] at hv
  simp only [winA] at hF
  rw [hA.r28] at hinv
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := frames_after hce (stk1 := 4464) (Nat.le_refl _) hA hF hLF hzo
  have hp64 : p' < 2 ^ 64 := by rw [← q0]; exact BitVec.isLt _
  have hcA := asCost_add (hL s.mem x) (hL s.mem y)
  unfold asNeed at hcA
  refine tail impl R hwb sub 0x58 (Or.inl rfl) b L z x y s (hNeg s.mem x) _ _ p' n' c' b' L' S'
    ⟨hpre, hl4, hl48, e1.trans hA.sp, e2.trans hA.r28, e3.trans hA.r29, e4.trans hA.r18,
      by rw [← q0]; exact (ofNat_toNat64 _).symm, hp64, by rw [← q1]; exact (ofNat_toNat64 _).symm,
      by rw [← q2]; exact (ofNat_toNat64 _).symm, f3, f4, f5, f6, hv, hn, hlc, by rw [← q2]; exact hr2 (by omega),
      hln, hLE, hb, hcA, hinv, hlive, hor, fun h => ?_, f1, f2, hnx, resA sub hnx hny hc⟩ (by rw [hr, h30]) (by simp)
  obtain ⟨a1, a2⟩ := hr1 (by unfold asNeed at h; exact h)
  exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

end FvModexp.Arm64.IntAS
