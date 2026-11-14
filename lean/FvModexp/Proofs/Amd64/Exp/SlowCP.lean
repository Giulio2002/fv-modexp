import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.Exp.LibCallsQ

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): callee preconditions at a call from the slow frame (agent expmc s80; twin of arm64
`SlowCP`, facts as asm's amd64 `EvNP.arr_at` / `EvMiP.miOp` / `EvMulP.stkPreA` on the slow frame)

Callee entry `S'` with `RSP = sp - 8`, window `[sp - 8 - W, sp - 8 + A)` (`W ≤ K`, `A ≤ 0x70`).
* `arr_atS`: the stack's array at a `WC` point is apart from our window, the guard and the TLS word.
* `stkS`: divmc's `Q.NatSqr.StkPre`.
* `Loc.tls`: a located buffer is apart from the TLS word; `DL.sep`: a non-empty destination's `StkSep`.
* `sqrPreS`: `Q.NatSqr.SPre` for `zz.sqr(stk, z)` with `0 < len z` (`len z = 0` is the empty path, see `SlowSqG`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

theorem apS {a k b n k' : Nat} (h : Apart a k b n) (hk : k' ≤ k) : Apart a k' b n := by
  unfold Apart at *; omega

theorem apR {a k b n n' : Nat} (h : Apart a k b n) (hn : n' ≤ n) : Apart a k b n' := by
  unfold Apart at *; omega

theorem out0 (xs : List (Nat × Nat)) : Outside 0 0 xs := by
  induction xs with
  | nil => trivial
  | cons r rs ih => obtain ⟨lo, hi⟩ := r; exact ⟨Or.inl (Nat.zero_le _), ih⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the stack's array at `M` (kept or fresh) is apart from the window, the guard and the TLS word -/
theorem arr_atS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 8 - K) (K + 0x228) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧ Apart (stW M st) (8 * stCap M st) (fs - 8) 8 := by
  have hce := hP.cenv0
  have hout := hP.win_rt
  obtain ⟨-, -, -, harr, -⟩ := hP.stkF
  intro hc
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · rw [e2] at hc; rw [e1, e2]; exact harr hc
  · exact ⟨(hin.apart hout).symm, (hin.apart hce.2.2.2.2.2.2.2.2.2.1).symm,
      (hin.apart hce.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm⟩

set_option maxRecDepth 20000 in
/-- **`StkPre`** at a callee entry `S'` (`RSP = sp - 8`, window `[sp - 8 - W, sp - 8 + A)`, `W ≤ K`, `A ≤ 0x70`) -/
theorem stkS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S' : State} (tsp : (S'.regs 4).toNat = sp - 8)
    (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs) (fm : S'.mem = M) {W A : Nat} (hW : W ≤ K)
    (hA : A ≤ 0x70) : StkPre R L1 S' W A st := by
  have hk := hP.kf
  have hc0 := WC.cap0 hP h
  have har := arr_atS hP h
  have hok := h.sok
  have hsok := hP.stk0
  obtain ⟨hstw, hstg, hsttl, -, hwbacc, hstwb, -⟩ := hP.stkF
  have hstf := free_apart h hsok.2.1 hP.stkF.2.2.2.2.2.2
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hogA, -, -, -, -, -, -, -, -, hst0, -⟩ := hP'
  have hfgA := (free_apart h hogA.1 hogA.2.2.2).symm
  have hlc := hok.2.2.2.2.2.1
  have hnl := hok.2.2.2.2.1
  subst fm
  simp only [StkPre, Q.BasicSqr.freeP, Q.BasicSqr.freeN, Q.NatSqr.guard, Q.NatSqr.tls, win, tsp, tg, tfs]
  simp only [free] at hstf hfgA
  unfold Apart at hstw
  refine ⟨hst0, hok, by simp only [outside_cons, outside_nil, and_true]; omega, hstg, fun hc => ?_, ?_, ?_,
    hstf, hstwb, ?_, (hogA.2.2.1).symm, hfgA, hsttl, fun hc => (har hc).2.2, ?_⟩
  · obtain ⟨a1, a2, -⟩ := har hc
    unfold Apart at a1
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, a2⟩
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [hc0 e, e]; unfold Apart; omega
    · have := (har e).2.1; unfold Apart at this ⊢; omega
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · simp only [outside_cons, outside_nil, and_true]; rw [hc0 e, e]; omega
    · have := (har e).1; unfold Apart at this
      simp only [outside_cons, outside_nil, and_true]; omega
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [hc0 e, e, show stLen S'.mem st = 0 by omega]; exact Or.inr (out0 _)
    · exact (hnl e).2.1.sub (by omega) (by omega)
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [e, hc0 e]; unfold Apart; omega
    · have := (har e).2.2; unfold Apart at this ⊢; omega

/-- a non-empty located buffer is apart from the TLS word -/
theorem Loc.tls (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : Loc R L zp zc p c) (hc : 0 < c) : Apart p (8 * c) (fs - 8) 8 := by
  rcases h with ⟨rfl, rfl, hz0⟩ | ⟨hin, -⟩ | ⟨-, rfl⟩
  · exact ((hP.zF hz0).2.2.2.2.2.1).symm
  · exact (hin.apart hP.cenv0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm
  · omega

set_option maxRecDepth 20000 in
/-- a non-empty destination (a prefix `k'` of it): `StkSep` at the current memory -/
theorem DL.sep (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (hd : DL R L st zp zc M L1 p c) (hc : 0 < c) {k' : Nat} (hk : k' ≤ 8 * c) : StkSep M st p k' := by
  obtain ⟨-, w2, -, w4, -⟩ := Loc.ap hP hd.2.2.1 hc
  have hfr := (hd.2.2.2.1 hc).2.1
  simp only [free] at hfr
  exact ⟨(apS w2 hk).symm, by simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; exact apS hfr hk, apS w4 hk⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.sqr`'s Q-form precondition** at the callee entry `S'` (`RSP = sp - 8`): `zz.sqr(stk, z)`, `0 < len z` -/
theorem sqrPreS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {W : Nat} (hWK : W ≤ K)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M) {pd cd px lx cx vx : Nat} (hd : DL R L st zp zc M L1 pd cd)
    (hx : LN R L st zp zc M L1 px lx cx vx) (hdx : Pw px cx pd cd) (hl0 : 0 < lx)
    (hlx : lx ≤ 2 ^ 12) (hsW : sqrW lx ≤ W) (hs16 : ℓ + 4 * (2 * lx) + 64 ≤ 2 ^ 16) {H : Nat}
    (hH : ℓ + 4 * (2 * lx) + 64 ≤ H) (hb : sqrCQ lx + stkR H M st ≤ b1) :
    Q.NatSqr.SPre R b1 H L1 W pd cd st px lx cx S' := by
  have hk := hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.1
  have hadx : M.accessible Callees.adxAddr 1 false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.1
  have hK8 : K ≤ sp - 8 := Nat.le_sub_of_add_le hk.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := W) (above := 64) hWK (by decide)
    (Nat.le_trans hWK hK8)
  have hgl := hw.globals hP (w := win S' W 64) (fun a n ho => by
    simp only [win, tsp, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hsk := stkS hP hw tsp tg tfs fm (W := W) (A := 64) hWK (by decide)
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hcx : 0 < cx := Nat.lt_of_lt_of_le hl0 hx.2.1
  obtain ⟨-, xH, xacc, x48⟩ := hx.1.2.1 hcx
  have hxw := Loc.win hP hx.1.2.2.1
  have hdw := Loc.win hP hd.2.2.1
  unfold Apart at hxw hdw
  have hxs := DL.sep hP hx.1 hcx (Nat.mul_le_mul_left 8 hx.2.1)
  subst fm
  refine ⟨hce, hsW, hsv, hgl, hwT, hx.2.1, hx.1.1, hlx, ?_, fun _ => ⟨xH, x48⟩, fun _ => ?_, hd.1, hd.2.1, ?_,
    fun hc => ⟨?_, ?_, DL.sep hP hd hc (Nat.le_refl _)⟩, ?_, hsk, fun _ => hxs, by rw [hlen]; exact hs16,
    ⟨by rw [hlen]; exact hH, hb⟩, hadx, by rw [tg]; exact hw.inv⟩
  · exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ xacc (Nat.le_refl _)
      (by have := hx.2.1; omega))
  · simp only [win, tsp, outside_cons, outside_nil, and_true]; omega
  · simp only [win, tsp, outside_cons, outside_nil, and_true]; omega
  · simp only [Q.NatSqr.guard, tg]; exact (Loc.ap hP hd.2.2.1 hc).2.2.1
  · simp only [Q.NatSqr.tls, tfs]; exact Loc.tls hP hd.2.2.1 hc
  · exact Or.inr fun hc hl => apR (hdx hcx hc).symm (Nat.mul_le_mul_left 8 hx.2.1)

end

end FvModexp.Amd64.ExpSlow
