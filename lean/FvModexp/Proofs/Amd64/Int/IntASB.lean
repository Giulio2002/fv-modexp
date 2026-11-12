import FvModexp.Proofs.Amd64.Int.IntASA

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): paths B and C — the call `z.abs = z.abs.sub(u.abs, v.abs)` and the tail

`(u, v) = (x, y)` (B, return `+0xf4`) or `(y, x)` (C, return `+0x15d`): from the entry of `nat.sub` (divmc's
`NatSub.ensX`, exact write set), the call, then `tail`. Twin of the arm64 `IntAS.pathSub`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.IntAS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- paths B / C from the entry of `nat.sub` to `RET` -/
theorem pathSub (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) (hpre : Pre R b L z x y s)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (u v off nb : Nat) (hu : OpR R L s u) (hv : OpR R L s v)
    (hzu : 0 < hC s.mem z → (hP s.mem z = hP s.mem u ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem u) (8 * hL s.mem u)))
    (hzv : 0 < hC s.mem z → (hP s.mem z = hP s.mem v ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem v) (8 * hL s.mem v)))
    (hvl : hL s.mem v ≤ hL s.mem u)
    (hvu : natVal s.mem (hP s.mem v) (hL s.mem v) ≤ natVal s.mem (hP s.mem u) (hL s.mem u))
    (hum : hL s.mem u = max (hL s.mem x) (hL s.mem y))
    (hoff : off = 0xf4 ∨ off = 0x15d) (hnb : nb = if off = 0x15d then 1 - hNeg s.mem x else hNeg s.mem x)
    (hnb1 : nb ≤ 1)
    (hres : (if nb = 0 ∨ natVal s.mem (hP s.mem u) (hL s.mem u) - natVal s.mem (hP s.mem v) (hL s.mem v) = 0 then
        ((natVal s.mem (hP s.mem u) (hL s.mem u) - natVal s.mem (hP s.mem v) (hL s.mem v) : Nat) : Int) else
        -((natVal s.mem (hP s.mem u) (hL s.mem u) - natVal s.mem (hP s.mem v) (hL s.mem v) : Nat) : Int)) =
      resZ sub (intZ s.mem x) (intZ s.mem y))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6183136) (hrd : S.mem.readLE (S.regs 4).toNat 8 = entry sub + off)
    (h0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem z)) (h3 : S.regs 3 = BitVec.ofNat 64 (hL s.mem z))
    (h1 : S.regs 1 = BitVec.ofNat 64 (hC s.mem z)) (h7 : S.regs 7 = BitVec.ofNat 64 (hP s.mem u))
    (h6 : S.regs 6 = BitVec.ofNat 64 (hL s.mem u)) (h8 : S.regs 8 = BitVec.ofNat 64 (hC s.mem u))
    (h9 : S.regs 9 = BitVec.ofNat 64 (hP s.mem v)) (h10 : S.regs 10 = BitVec.ofNat 64 (hL s.mem v))
    (h11 : S.regs 11 = BitVec.ofNat 64 (hC s.mem v)) (hA : AtCall s S z x) :
    ReachesRet (LibIntAS.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Post sub R b L z x y s s' := by
  have hce := hpre.1
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hce.2.1.1
  have hzo := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcs := asCost_sub (hL s.mem x) (hL s.mem y)
  rw [← hum] at hcs
  have huv := (opR_at hA.mf hu).2.2.2.2.2.2
  have hvv := (opR_at hA.mf hv).2.2.2.2.2.2
  have hsp : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hA.sp]; exact sp96 hsp0
  have hspre := subPre_of hpre hu hv hzu hzv hvl hvu (by omega) hsp hA.g hA.fs hA.mf hA.reg
  obtain ⟨-, -, -, -, hulc, huc, hul16, -, hu48, -, -, -⟩ := hu
  obtain ⟨-, -, -, -, hvlc, hvc, hvl16, -, hv48, -, -, -⟩ := hv
  have hzp : hP s.mem z < 2 ^ 64 := by have := Arm64.Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hzl : hL s.mem z < 2 ^ 64 := by have := Arm64.Memory.readLE_lt s.mem (z + 16) 8; simpa using this
  refine subCall hap hmk hmv (ra_of hap sub (by cases sub <;> decide) off (by omega)) hzp (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hpc hrd h0 h3 h1 h7 h6 h8 h9 h10 h11
    (by rw [hA.x15]; exact hx15) (by rw [hA.df]; exact hdf) rfl rfl rfl hspre ?_
  intro s' p' n' c' L' b' hr e4 e5 e14 ex15 efs edf _ q0 q3 q1 hv hn hlc hln hLE hb hinv hlive hor hF hLF hr1 hc40 hp64
  rw [hsp] at hF
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := frames_after hce (stk1 := 4288) (by omega) hA
    (by rw [hsp]; exact hF) hLF (hzo.of_sub (Nat.le_refl _) (by omega))
  obtain ⟨f1, f2⟩ := frames_wider f1 f2 (k' := max (hL s.mem x) (hL s.mem y) + 1) (by omega)
  rw [hA.g] at hinv
  refine tail impl R hwb sub off (Or.inr hoff) b L z x y s nb _ _ p' n' c' b' L' s'
    ⟨hpre, ?_, e14.trans hA.g, efs.trans hA.fs, edf.trans hA.df, ex15.trans hA.x15, e5.trans hA.bp, q0, hp64, q3, q1,
      f4, f3, f5, f6, by rw [hv, huv, hvv], hn, hlc, hc40, by omega, hLE, hb, hcs, hinv, hlive, hor, fun h => ?_, f1, f2,
      hnb1, by rw [← hres]⟩ hr hnb hra47
  · rw [e4]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  · have hnd : hL s.mem u ≤ asNeed (hL s.mem x) (hL s.mem y) := by unfold asNeed; split <;> omega
    exact hr1 (by omega)

end FvModexp.Amd64.IntAS
