import FvModexp.Proofs.Amd64.Exp.P2PreBld

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): calling `gcWriteBarrier2` (agent divmc s62; twin of infra's
`Arm64/Exp/P2PreWbC`)

`wbCall`: the live `gcWriteBarrier2` contract called at `S` (`RSP_c = RSP - 184`, the return address pushed): the context
after the call and the caller's two stores into the returned buffer, and the reads of `powers`, `buf` and the frame
(`RdR`) kept.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

/-- the ranges whose reads a segment needs kept: `powers`, `buf`, the frame above the callee window -/
@[reducible] def RdR (s : State) (pw pl lm bp a n : Nat) : Prop :=
  (pw ≤ a ∧ a + n ≤ pw + 24 * pl) ∨ (bp ≤ a ∧ a + n ≤ bp + 8 * NB pl lm) ∨
    ((s.regs 4).toNat - 184 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 80)

/-- the two buffer stores after the barrier -/
@[reducible] def W2 (m : Memory) (buf v1 v2 : Nat) : Memory := (m.writeLE buf 8 v1).writeLE (buf + 8) 8 v2

/-- reads of a held range are kept by a store into a runtime range apart from the live set -/
theorem rd_rtw {R : RtInv} {L1 : List (Nat × Nat)} {M : Memory} {a k v c n : Nat} (hin : InRanges a k R.rt)
    (hap : ApartAll a k L1) (hh : Held R L1 c n) (h0 : 0 < n) (hk : 0 < k) :
    (M.writeLE a k v).readLE c n = M.readLE c n := by
  refine Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_
  rcases hh with hL | hO
  · have := hap.apart_of_inRanges hL; unfold Apart at this; omega
  · have := hin.apart hO; unfold Apart at this; omega

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the ranges of `RdR` are held and apart from the barrier's window `[RSP_c - 4096, RSP_c)` -/
theorem rdr_held (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {a n : Nat} (h0 : 0 < n)
    (h : RdR s pw pl lm bp a n) :
    Held R L1 a n ∧ (a + n ≤ (s.regs 4).toNat - 184 - 4096 ∨ (s.regs 4).toNat - 184 ≤ a) := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hrt := hf.w.rt
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hrt hpww
  rcases h with h | h | h
  · exact ⟨Or.inr (hf.pwrt.of_sub h.1 h.2), by omega⟩
  · have hwok := wok_buf (zp := a) (zn := n) hc.scr h.1 h.2
    have hwin := wok_win hwok hf.w (by simp only; omega)
    simp only [K, A] at hwin
    exact ⟨hc.scr.held.sub h.1 h.2, by omega⟩
  · exact ⟨Or.inr (hrt.of_sub (by omega) (by omega)), by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`gcWriteBarrier2`** called at `S` (`RSP_c = RSP - 184`, return address at `[RSP_c]`, context at `S.mem`) -/
theorem wbCall (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {r : W64} {Q : State → Prop}
    {S : State} (hpc : S.rip = BitVec.ofNat 64 wbE) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 184)
    (h14 : S.regs 14 = s.regs 14) (hm : S.mem = M) (hra : M.readLE ((s.regs 4).toNat - 184) 8 < 2 ^ 47)
    (k : ∀ (buf : W64) (f : Flags) (xm yh : Nat → BitVec 128) (m' : Memory) (zh : Nat → BitVec 256)
      (kr : Nat → W64),
      buf.toNat + 16 ≤ 2 ^ 48 → buf.toNat % 8 = 0 → m'.accessible buf.toNat 16 true = true →
      (∀ v1 v2, Ctx R kc L st pw pl lm x xl s bp (W2 m' buf.toNat v1 v2) L1 b1) →
      (∀ v1 v2 a n, 0 < n → RdR s pw pl lm bp a n → (W2 m' buf.toNat v1 v2).readLE a n = M.readLE a n) →
      ReachesRet (LibW.program.link impl) r (wbRetX64 S buf f xm yh m' zh kr) Q) :
    ReachesRet (LibW.program.link impl) r S Q := by
  have hf := pf_of hpre (by omega)
  have hce := cenv_ctx hpre hc
  obtain ⟨hal, hb', ha8, hw, -, -, -, hout, -, -, hLs, -⟩ := hce
  have hsv := hpre.2.1
  have hok : R.ok wbE [2] := by rw [← wbE_eq]; exact hsv.2.2.2.2.2.1 [2]
  refine ReachesRet.call_regions (hwb L1 (b1 + stkR (HP (stLen s.mem st) pl lm) M st)) hpc
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hok, ?_, ?_, ?_⟩ ?_
  · rw [hsp, hm]; exact hra
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hm]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [h14, hm]; exact hc.inv
  · intro r' hr'
    have := hLs r' hr'
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    rw [hsp]; omega
  · intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    rw [hsp]; exact hout.of_sub (by omega) (by simp only; omega)
  intro S2 _ ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩ hrg0
  subst hs2
  rw [hm, hsp] at hfr2
  rw [hm] at hlf2
  rw [h14] at hinvS
  have hsl' := hsl
  obtain ⟨hbR, hb48, hbacc, hbal⟩ := hsl'
  have hrg : m'.regions = M.regions := by rw [← hm]; exact hrg0
  refine k buf f2 x2 yh2 m' zh2 kr2 hb48 hbal hbacc (fun v1 v2 => ?_) (fun v1 v2 a n h0 hr => ?_)
  · exact ctx_wb hc hf (by omega) hsp (by rw [hsp]; exact hfr2) hlf2 hrg hsl hapL hinvS v1 v2
  · obtain ⟨hh, hwin⟩ := rdr_held hpre hkc hc h0 hr
    have hh' : Held R L1 a n := hh
    simp only [W2]
    rw [rd_rtw (hbR.sub (a := buf.toNat + 8) (n := 8) (by omega) (by omega))
        (ApartAll.sub' (a := buf.toNat + 8) (n := 8) hapL (by omega) (by omega)) hh' h0 (by omega),
      rd_rtw (hbR.sub (a := buf.toNat) (n := 8) (Nat.le_refl _) (by omega))
        (ApartAll.sub' (a := buf.toNat) (n := 8) hapL (Nat.le_refl _) (by omega)) hh' h0 (by omega)]
    rcases hh with hL | hO
    · exact lf_read hlf2 hL (by simp)
    · refine frame_read hfr2 fun r' hr' hr'' => ?_
      simp only [List.mem_append, List.mem_singleton] at hr'
      rcases hr' with hr' | rfl
      · have := MemFrame.outside_mem hO hr'; omega
      · simp only at hr'' ⊢; omega

end

end FvModexp.Amd64.P2Pre
