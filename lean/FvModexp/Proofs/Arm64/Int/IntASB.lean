import FvModexp.Proofs.Arm64.Int.IntASA

/-!
# `(*Int).Add` / `(*Int).Sub` (arm64): paths B and C — the call `z.abs = z.abs.sub(u.abs, v.abs)` and the tail

`(u, v) = (x, y)` (B, call at `+0xd0`, return `+0xd4`) or `(y, x)` (C, `+0x124` / `+0x128`): from the entry of
`nat.sub` (agent divmc's `NatSub.ensR`), the call, then `tail`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

open FvModexp.Arm64.RunIface (Serves)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- paths B / C from the entry of `nat.sub` to `RET` -/
theorem pathSub (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) (hpre : Pre R b L z x y s)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (u v off nb : Nat) (hu : OpR R L s u) (hv : OpR R L s v)
    (hzu : 0 < hC s.mem z → (hP s.mem z = hP s.mem u ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem u) (8 * hL s.mem u)))
    (hzv : 0 < hC s.mem z → (hP s.mem z = hP s.mem v ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem v) (8 * hL s.mem v)))
    (hvl : hL s.mem v ≤ hL s.mem u)
    (hvu : natVal s.mem (hP s.mem v) (hL s.mem v) ≤ natVal s.mem (hP s.mem u) (hL s.mem u))
    (hum : hL s.mem u = max (hL s.mem x) (hL s.mem y))
    (hoff : off = 0xd4 ∨ off = 0x128) (hnb : nb = if off = 0x128 then 1 - hNeg s.mem x else hNeg s.mem x)
    (hnb1 : nb ≤ 1)
    (hres : (if nb = 0 ∨ natVal s.mem (hP s.mem u) (hL s.mem u) - natVal s.mem (hP s.mem v) (hL s.mem v) = 0 then
        ((natVal s.mem (hP s.mem u) (hL s.mem u) - natVal s.mem (hP s.mem v) (hL s.mem v) : Nat) : Int) else
        -((natVal s.mem (hP s.mem u) (hL s.mem u) - natVal s.mem (hP s.mem v) (hL s.mem v) : Nat) : Int)) =
      resZ sub (intZ s.mem x) (intZ s.mem y))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1781872) (h30 : S.regs 30 = BitVec.ofNat 64 (entry sub + off))
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem z)) (h1 : S.regs 1 = BitVec.ofNat 64 (hL s.mem z))
    (h2 : S.regs 2 = BitVec.ofNat 64 (hC s.mem z)) (h3 : S.regs 3 = BitVec.ofNat 64 (hP s.mem u))
    (h4 : S.regs 4 = BitVec.ofNat 64 (hL s.mem u)) (h5 : S.regs 5 = BitVec.ofNat 64 (hC s.mem u))
    (h6 : S.regs 6 = BitVec.ofNat 64 (hP s.mem v)) (h7 : S.regs 7 = BitVec.ofNat 64 (hL s.mem v))
    (h8 : S.regs 8 = BitVec.ofNat 64 (hC s.mem v)) (hA : AtCall s S z x) :
    ReachesRet (LibIntAS.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post sub R b L z x y s s' := by
  have hS' := hypSum hap sub_names (NatSub.ensX impl hap R hmk hmv b L (BitVec.ofNat 64 (hP s.mem z))
    (BitVec.ofNat 64 (hL s.mem z)) (BitVec.ofNat 64 (hC s.mem z)) (BitVec.ofNat 64 (hP s.mem u))
    (BitVec.ofNat 64 (hL s.mem u)) (BitVec.ofNat 64 (hC s.mem u)) (BitVec.ofNat 64 (hP s.mem v))
    (BitVec.ofNat 64 (hL s.mem v)) (BitVec.ofNat 64 (hC s.mem v)))
  rw [show segAddr Extracted.program NatSub.fn = 1781872 by decide] at hS'
  have hce := hpre.1
  have hsp0 : 4560 ≤ s.sp.toNat := hce.2.1.2.1
  have hzo := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcs := asCost_sub (hL s.mem x) (hL s.mem y)
  rw [← hum] at hcs
  have huv := (opR_at (hA.mf.mono fun a n ho => by
    simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hu).2.2.2.2.2.2
  have hvv := (opR_at (hA.mf.mono fun a n ho => by
    simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hv).2.2.2.2.2.2
  have hpre' := subPre_of hpre hu hv hzu hzv hvl hvu (by omega) (by rw [hA.sp]; exact sp96 hsp0) hA.r28
    (hA.mf.mono fun a n ho => by simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega) hA.reg
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, -, hx48, -, -, -⟩ := hu
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, -, hy48, -, -, -⟩ := hv
  have hzp : hP s.mem z < 2 ^ 64 := by have := Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  refine ReachesRet.call_regions hS' hpc ⟨?_, ?_, hpre'⟩ fun S' hr ⟨⟨e1, e2, e3, e4⟩, ⟨hq, hr1, hr2⟩, hF, hLF⟩ _ => ?_
  · rw [h30, tN (by rcases hoff with rfl | rfl <;> cases sub <;> simp [entry])]
    rcases hoff with rfl | rfl
    · exact ra_of hap (by decide) sub 53 (by omega)
    · exact ra_of hap (by decide) sub 74 (by omega)
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  obtain ⟨p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, -, -⟩ := hq
  simp only [tN hzp, tN (show hC s.mem z < 2 ^ 64 by omega), tN (show hP s.mem u < 2 ^ 64 by omega),
    tN (show hL s.mem u < 2 ^ 64 by omega), tN (show hP s.mem v < 2 ^ 64 by omega),
    tN (show hL s.mem v < 2 ^ 64 by omega)] at hv hln hb hinv hor hF hLF hr1 hr2
  rw [huv, hvv] at hv
  simp only [winA] at hF
  rw [hA.r28] at hinv
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := frames_after hce (stk1 := 4304) (by omega) hA hF hLF
    (hzo.of_sub (Nat.le_refl _) (by omega))
  obtain ⟨f1, f2⟩ := frames_wider f1 f2 (k' := max (hL s.mem x) (hL s.mem y) + 1) (by omega)
  have hp64 : p' < 2 ^ 64 := by rw [← q0]; exact BitVec.isLt _
  refine tail impl R hwb sub off (Or.inr hoff) b L z x y s nb _ _ p' n' c' b' L' S'
    ⟨hpre, hl4, hl48, e1.trans hA.sp, e2.trans hA.r28, e3.trans hA.r29, e4.trans hA.r18,
      by rw [← q0]; exact (ofNat_toNat64 _).symm, hp64, by rw [← q1]; exact (ofNat_toNat64 _).symm,
      by rw [← q2]; exact (ofNat_toNat64 _).symm, f3, f4, f5, f6, hv, hn, hlc, by rw [← q2]; exact hr2 (by omega),
      by omega, hLE, hb, hcs, hinv, hlive, hor, fun h => ?_, f1, f2, hnb1, by rw [← hres]⟩ (by rw [hr, h30]) hnb
  have hnd : hL s.mem u ≤ asNeed (hL s.mem x) (hL s.mem y) := by unfold asNeed; split <;> omega
  obtain ⟨a1, a2⟩ := hr1 (by omega)
  exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

end FvModexp.Arm64.IntAS
