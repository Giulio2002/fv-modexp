import FvModexp.Proofs.Amd64.Int.IntASCallH
import FvModexp.Proofs.Amd64.Int.IntASAt
import FvModexp.Proofs.Amd64.Int.IntASTail
import FvModexp.Proofs.Amd64.Int.IntASVal

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): path A — the call `z.abs = z.abs.add(x.abs, y.abs)` (`+0x51`) and the tail

From the entry of `nat.add` (divmc's `NatAdd.ensX`, exact write set) with `RSP = RSP₀ - 96`, the prologue's spills in
place (`AtCall`): the call (return `+0x56`), then `tail`. Twin of the arm64 `IntAS.pathA`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.IntAS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path A from the entry of `nat.add` to `RET` -/
theorem pathA (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) (hpre : Pre R b L z x y s)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hc : sub = true ↔ hNeg s.mem x ≠ hNeg s.mem y)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6182240) (hrd : S.mem.readLE (S.regs 4).toNat 8 = entry sub + 0x56)
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem z)) (h3 : S.regs 3 = BitVec.ofNat 64 (hL s.mem z))
    (h1 : S.regs 1 = BitVec.ofNat 64 (hC s.mem z)) (h7 : S.regs 7 = BitVec.ofNat 64 (hP s.mem x))
    (h6 : S.regs 6 = BitVec.ofNat 64 (hL s.mem x)) (h8 : S.regs 8 = BitVec.ofNat 64 (hC s.mem x))
    (h9 : S.regs 9 = BitVec.ofNat 64 (hP s.mem y)) (h10 : S.regs 10 = BitVec.ofNat 64 (hL s.mem y))
    (h11 : S.regs 11 = BitVec.ofNat 64 (hC s.mem y)) (hA : AtCall s S z x) :
    ReachesRet (LibIntAS.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Post sub R b L z x y s s' := by
  have hce := hpre.1
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hce.2.1.1
  have hx := hpre.2.2.2.1
  have hy := hpre.2.2.2.2.1
  have hzo := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxv := (opR_at hA.mf hx).2.2.2.2.2.2
  have hyv := (opR_at hA.mf hy).2.2.2.2.2.2
  obtain ⟨hnx, -, -, -, hxlc, hxc, hxl16, -, hx48, -, -, -⟩ := hx
  obtain ⟨hny, -, -, -, hylc, hyc, hyl16, -, hy48, -, -, -⟩ := hy
  have hzp : hP s.mem z < 2 ^ 64 := by have := Arm64.Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hzl : hL s.mem z < 2 ^ 64 := by have := Arm64.Memory.readLE_lt s.mem (z + 16) 8; simpa using this
  have hsp : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  have hapre := addPre_of hpre hsp hA.g hA.fs hA.mf hA.reg
  refine addCall hap hmk hmv (ra_of hap sub (by cases sub <;> decide) 0x56 (by omega)) hzp (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpc hrd h0 h3 h1 h7 h6 h8 h9 h10 h11
    (by rw [hA.x15]; exact hx15) (by rw [hA.df]; exact hdf) rfl rfl rfl hapre ?_
  intro s' p' n' c' L' b' hr e4 e5 e14 ex15 efs edf _ q0 q3 q1 hv hn hlc hln hLE hb hinv hlive hor hF hLF hr1 hc40 hp64
  rw [hsp] at hF
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := frames_after hce (stk1 := 4440) (Nat.le_refl _) hA
    (by rw [hsp]; exact hF) hLF (hzo.of_sub (Nat.le_refl _) (by omega))
  have hcA := asCost_add (hL s.mem x) (hL s.mem y)
  unfold asNeed at hcA
  rw [hA.g] at hinv
  refine tail impl R hwb sub 0x56 (Or.inl rfl) b L z x y s (hNeg s.mem x) _ _ p' n' c' b' L' s'
    ⟨hpre, ?_, e14.trans hA.g, efs.trans hA.fs, edf.trans hA.df, ex15.trans hA.x15, e5.trans hA.bp, q0, hp64, q3, q1,
      f4, f3, f5, f6, by rw [hv, hxv, hyv], hn, hlc, hc40, hln, hLE, hb, hcA, hinv, hlive, hor, fun h => ?_, f1, f2, hnx,
      resA sub hnx hny hc⟩ hr (by simp) hra47
  · rw [e4]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  · exact hr1 (by unfold asNeed at h; exact h)

end FvModexp.Amd64.IntAS
