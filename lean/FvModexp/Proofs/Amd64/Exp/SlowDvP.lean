import FvModexp.Proofs.Amd64.Exp.SlowMuP
import FvModexp.Proofs.Amd64.Exp.SlowK
import FvModexp.Proofs.Amd64.NatQ.DivGDefsQ

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): `nat.div`'s empty-tolerant precondition `DivPreGQ` for `zz.div(stk, r, z, m)` at a call
from the slow frame (agent expmc s81; twin of `sqrPreS`)

Callee entry `S'` (`RSP = sp - 8`, window `[sp - 8 - W, sp - 8 + 0x70)`): destinations `zz` (quotient) and `r`
(remainder, `DL`), dividend the loop's `z` (`LN`, possibly empty, normalised), divisor the input `m` (entry facts `OE`,
via `obj_at`); the stack arguments `u = z`, `v = m` at `sp + 0 … sp + 0x28`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem offs {sp : Nat} (h : 8 ≤ sp) : sp - 8 + 8 = sp ∧ sp - 8 + 16 = sp + 8 ∧ sp - 8 + 24 = sp + 16 ∧
    sp - 8 + 32 = sp + 24 ∧ sp - 8 + 40 = sp + 32 ∧ sp - 8 + 48 = sp + 40 := by omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.div`'s Q-form precondition** at the callee entry `S'` (`RSP = sp - 8`): `zz.div(stk, r, z, m)` -/
theorem divPreS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {W : Nat} (hWK : W ≤ K)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M) {pd ld cd pe le ce pz lz cz vz : Nat} (hd : DL R L st zp zc M L1 pd cd) (hld : ld ≤ cd)
    (he : DL R L st zp zc M L1 pe ce) (hle : le ≤ ce) (hz : LN R L st zp zc M L1 pz lz cz vz)
    (hde : Pw pd cd pe ce) (hzd : Pw pz cz pd cd) (hze : Pw pz cz pe ce) (hlz : lz ≤ 2 ^ 9)
    (hs16 : ℓ + 16 * lz + 64 ≤ 2 ^ 16) {H c : Nat} (hH : ℓ + 16 * lz + 64 ≤ H) (hb : c ≤ b1)
    (r1 : M.readLE sp 8 = pz) (r2 : M.readLE (sp + 8) 8 = lz) (r3 : M.readLE (sp + 16) 8 = cz)
    (r4 : M.readLE (sp + 24) 8 = mp) (r5 : M.readLE (sp + 32) 8 = ml) (r6 : M.readLE (sp + 40) 8 = mc) :
    DivPreGQ R b1 H c L1 W 0x70 pd ld cd st pe le ce pz lz cz mp ml mc S' := by
  have hk := hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hadx : M.accessible Callees.adxAddr 1 false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.1
  have hK8 : K ≤ sp - 8 := Nat.le_sub_of_add_le hk.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := W) (above := 0x70) hWK (by decide)
    (Nat.le_trans hWK hK8)
  have hgl := hw.globals hP (w := win S' W 0x70) (glW tsp hWK hk.2.2.1 (by decide))
  have hsk := stkS hP hw tsp tg tfs fm (W := W) (A := 0x70) hWK (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -, k11, k12, k13, k14, k15⟩ := hsk
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hml0 : 0 < ml := hP.2.2.2.2.1
  have hmP := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hmO, hmacc, hm48, hmN, hzm, -⟩ := hmP
  have hmo := obj_at hP hw hmO hmacc hm48 hmN (Nat.le_trans hml (by decide)) hzm tsp fm (stk := W) (above := 0x70) hWK (by decide)
  have hmfr := free_apart hw hmO.1 hmO.2.2.2
  simp only [free] at hmfr
  have hc0 := WC.cap0 hP hw
  subst fm
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := offs (Nat.le_trans (Nat.le_add_left 8 K) hk.2.2.1)
  have hW1 : ∀ p n, Apart p n (sp - 8 - K) (K + 0x228) → Outside p n (win S' W 0x70) :=
    fun p n h => apWin tsp hWK hk.2.2.1 (by decide) h
  have wo : ∀ p c, DL R L st zp zc S'.mem L1 p c →
      EvenHyp.WrOut R L1 S' W 0x70 p c ∧ (0 < c → Apart p (8 * c) RunIface.gA 32) := by
    intro p c h
    refine ⟨⟨h.1, h.2.1, fun hc => ⟨hW1 _ _ (Loc.win hP h.2.2.1), by rw [tg]; exact (Loc.ap hP h.2.2.1 hc).2.2.1,
      by rw [tfs]; exact Loc.tls hP h.2.2.1 hc⟩⟩, fun hc => (Loc.ap hP h.2.2.1 hc).2.2.2.1⟩
  have dap : ∀ p c, DL R L st zp zc S'.mem L1 p c → Pw pz cz p c → 0 < c →
      (0 < lz → Apart p (8 * c) pz (8 * lz)) ∧ Apart p (8 * c) mp (8 * ml) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW S'.mem st + 8 * stLen S'.mem st) (8 * (stCap S'.mem st - stLen S'.mem st)) := by
    intro p c h hpw hc
    have hob := (h.2.2.2.1 hc).2.1
    simp only [free] at hob
    exact ⟨fun hl => apR (hpw (Nat.lt_of_lt_of_le hl hz.2.1) hc).symm (Nat.mul_le_mul_left 8 hz.2.1),
      (Loc.ap hP h.2.2.1 hc).2.2.2.2.2.2, (Loc.ap hP h.2.2.1 hc).2.1, hob⟩
  refine ⟨by rw [tsp, o1]; exact r1, by rw [tsp, o2]; exact r2, by rw [tsp, o3]; exact r3,
    by rw [tsp, o4]; exact r4, by rw [tsp, o5]; exact r5, by rw [tsp, o6]; exact r6,
    hce, hsv, hgl, hld, hle, (wo _ _ hd).1, (wo _ _ he).1, ⟨Nat.lt_of_le_of_lt hz.2.1 hz.1.1, fun h0 => ?_⟩,
    hmo.1, hlz, hml0, Nat.le_trans hml (by decide), hz.2.2.2, hmo.2.1, k2, k3, k5, by rw [hlen]; exact hs16, hc0, fun h0 => ?_,
    hmO.2.2.1, hmfr, k1, ⟨k4, k9, k8⟩, ⟨k13, k15⟩, (wo _ _ hd).2, (wo _ _ he).2, k11, k12, hde, ?_,
    ⟨by rw [hlen]; exact hH, hb⟩, hadx, k14, by rw [tg]; exact hw.inv⟩
  · have hc : 0 < cz := Nat.lt_of_lt_of_le h0 hz.2.1
    obtain ⟨-, zH, zacc, z48⟩ := hz.1.2.1 hc
    exact ⟨Nat.lt_of_le_of_lt hz.2.1 hz.1.1,
      Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ zacc (Nat.le_refl _)
        (le8 hz.2.1)), Nat.le_trans (le8 hz.2.1) z48,
      zH.sub (Nat.le_refl _) (le8 hz.2.1),
      (hW1 _ _ (Loc.win hP hz.1.2.2.1)).of_sub (Nat.le_refl _) (le8 hz.2.1)⟩
  · have hsep := DL.sep hP hz.1 (Nat.lt_of_lt_of_le h0 hz.2.1) (Nat.mul_le_mul_left 8 hz.2.1)
    exact ⟨hsep.1.symm, hsep.2.1⟩
  · intro p c hm hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact dap _ _ hd hzd hc
    · exact dap _ _ he hze hc

end

end FvModexp.Amd64.ExpSlow
