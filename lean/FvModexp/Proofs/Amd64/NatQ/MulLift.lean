import FvModexp.Proofs.Amd64.NatQ.MulOps
import FvModexp.Proofs.Amd64.NatQ.SqrKPre

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulLift.lean — TIGHT COSTS] The mul SCC (amd64): `MPre` one frame down, `MPost` one frame up

`mpre_down`: the caller's `MPre` (window `W`) gives the callee's `MPre` at `S1` (`RSP - f`, window `W1`, memory
changed in the caller's window only; `g`, `fsBase` kept). `mpost_up`: the callee's `MPost` (from `S1` to `s2`) and
window-only stores until the caller's return `s'` give the caller's `MPost`. `mul_keeps`: an inner `nat.mul` keeps the
caller's frame above the callee's window.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep stkOK_frame outside_of_liveSep apart_of_apartAll inv_frame_win
  globals_frame)

set_option maxRecDepth 20000 in
/-- `MPre` at a callee `f` bytes down (window `W1`), memory changed in the caller's window only -/
theorem mpre_down {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s S1 : State}
    {f W1 : Nat} (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s)
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hF : MemFrame s.mem S1.mem (win s W 88))
    (hreg : S1.mem.regions = s.mem.regions) (hk : f + W1 ≤ W) (hf8 : f % 8 = 0)
    (hw1 : mulW64 xl yl ≤ W1) :
    MPre R b H L W1 zp zc st xp xl xc yp yl yc S1 := by
  obtain ⟨hce, -, hsv, hglb, hty, hops, hstk, hcost, hadx, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  have hF1 : MemFrame s.mem S1.mem (R.rt ++ win s W 88) := hF.mono fun a n h => by
    simp only [outside_append] at h; exact h.2
  have hLF : LiveFrame s.mem S1.mem L [] := lf_win' [] hF hLs
  have hsub := win_sub (ab := 88) hsp hk (by omega) (by omega) (stk1 := W1) (above1 := 88)
  obtain ⟨eW, eL, eC⟩ := hdr_keep hstk.2.1 hstk.2.2.1 hF1 hLF
  have htd : NatSqr.tls S1 = NatSqr.tls s := by simp only [NatSqr.tls]; rw [hfs]
  refine ⟨callEnv_shift hce hLs hF1 hsp hg hfs hreg hk (by omega) hf8, hw1, hsv,
    globals_frame hglb hF1 (by obtain ⟨-, -, -, -, -, -, -, -, -, hgw, -⟩ := hglb; exact hgw) hsub, hty, ?_,
    stkPre_shift hstk hF1 hLF hg hfs hsub,
    ⟨by rw [eL]; exact hcost.1, by rw [stkR_congr eC]; exact hcost.2⟩, by rw [hF.accessible]; exact hadx, ?_⟩
  · rw [hg, htd]; exact (hops.mono hsub).move eW eL eC hF.accessible
  · rw [hg]; exact inv_frame_win hF hout (by omega) (by decide) hinv

/-- a window-only frame chain around a callee frame -/
theorem frame3 {m0 m1 m2 m3 : Memory} {wa rs : List (Nat × Nat)} (h1 : MemFrame m0 m1 wa)
    (h2 : MemFrame m1 m2 rs) (h3 : MemFrame m2 m3 wa) {rs' : List (Nat × Nat)}
    (hs : ∀ a n, Outside a n rs' → Outside a n wa ∧ Outside a n rs) : MemFrame m0 m3 rs' :=
  MemFrame.trans (MemFrame.trans h1 h2 (rs'' := rs') hs) h3 fun a n h => ⟨h, (hs a n h).1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`MPost` one frame up**: the callee's `MPost` (`S1 → s2`, window `W1` at `RSP - f`) with window-only stores
before (`s → S1`) and after (`s2 → s'`) is the caller's `MPost` (window `W`) -/
theorem mpost_up {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat}
    {s S1 s2 s' : State} {f W1 : Nat} (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s)
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hk : f + W1 ≤ W) (hg : S1.regs 14 = s.regs 14)
    (hfs : S1.fsBase = s.fsBase) (hdf : S1.df = s.df)
    (hF : MemFrame s.mem S1.mem (win s W 88))
    (hQ : MPost R b H L W1 zp zc st xp xl xc yp yl yc S1 s2)
    (F3 : MemFrame s2.mem s'.mem (win s W 88)) (hfs' : s'.fsBase = s2.fsBase) (hdf' : s'.df = s2.df)
    (r0 : s'.regs 0 = s2.regs 0) (r1 : s'.regs 3 = s2.regs 3) (r2 : s'.regs 1 = s2.regs 1) :
    MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hce, -, -, -, -, ⟨⟨-, -, -, -, -, hxw⟩, ⟨-, -, -, -, -, hyw⟩, ⟨-, -, hzw, -, -, -⟩, -⟩, hstk, -, -, -⟩ := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, hstw, -⟩ := hstk
  have hsubA := win_sub (ab := 88) hsp hk (by omega) (by omega) (stk1 := W1) (above1 := 88)
  obtain ⟨eW, eL, eC⟩ := hdr_frame hF hstw
  obtain ⟨eW3, eL3, eC3⟩ := hdr_frame F3 hstw
  have hxS : natVal S1.mem xp xl = natVal s.mem xp xl := by
    rcases Nat.eq_zero_or_pos xl with h0 | h0
    · subst h0; simp
    · exact natVal_frame hF (hxw h0).1
  have hyS : natVal S1.mem yp yl = natVal s.mem yp yl := by
    rcases Nat.eq_zero_or_pos yl with h0 | h0
    · subst h0; simp
    · exact natVal_frame hF (hyw h0).1
  obtain ⟨efs, edf, p', l', c', q0, q1, q2, hv, hn, hlc, hll, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex,
    hsb, hMF, hLF⟩ := hQ
  have hpo : 0 < c' → Outside p' (8 * c') (win s W 88) := by
    intro hc
    rcases hkind with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · exact hzw
    · have := NatAdd.outside_of_inRanges hout hin
      simp only [win, outside_cons, outside_nil, and_true]; omega
  have hwS : stkWs S1.mem st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  rw [hwS] at hMF hLF
  rw [hxS, hyS] at hv hex
  rw [stkR_congr eC, ← stkR_congr eC3] at hbud
  have hLs' : LiveSep L (win s W 88) := hLs
  have hFL : MemFrame s.mem s'.mem (R.rt ++ win s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
    frame3 hF hMF F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨⟨h.1.1.1, hsubA _ _ h.1.1.2⟩, h.1.2⟩, h.2⟩
  have hLL : ∀ ws : List (Nat × Nat), LiveFrame S1.mem s2.mem L ws → LiveFrame s.mem s'.mem L ws := fun ws h =>
    LiveFrame.trans (LiveFrame.trans (lf_win' _ hF hLs') h fun _ _ h => h) (lf_win' _ F3 hLs') fun _ _ h => h
  refine ⟨by rw [hfs', efs, hfs], by rw [hdf', edf, hdf], p', l', c', by rw [r0, q0], by rw [r1, q1], by rw [r2, q2],
    ?_, ?_, hlc, hll, hc40, L', b', hext, hbud,
    inv_frame_win F3 hout (by omega) (by decide) (by rw [← hg]; exact hinv), ?_, hkind, ?_, ?_, ?_, hFL, hLL _ hLF⟩
  · rcases Nat.eq_zero_or_pos l' with h0 | h0
    · subst h0; rw [natVal_zero, ← hv, natVal_zero]
    · rw [natVal_frame F3 ((hpo (by omega)).of_sub (Nat.le_refl _) (by omega)), hv]
  · rcases hn with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos l' with h0 | h0
      · exact Or.inl h0
      right; rw [F3.readLE _ _ ((hpo (by omega)).of_sub (by omega) (by omega))]; exact h
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hlive hc; exact ⟨a1, a2, by rw [F3.accessible]; exact a3, a4⟩
  · intro hne hc0 hcap0; rw [eC3] at hcap0; rw [eW3, eC3]; exact hfa hne hc0 hcap0
  · intro h1 h2 h3
    obtain ⟨e1, e2, hvz, hF', hLF'⟩ := hex h1 h2 h3
    rw [hwS] at hF' hLF'
    have hzN : Outside zp (8 * (xl + yl)) (win s W 88) := hzw.of_sub (Nat.le_refl _) (by omega)
    refine ⟨e1, e2, ?_, frame3 hF hF' F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨⟨h.1.1.1, hsubA _ _ h.1.1.2⟩, h.1.2⟩, h.2⟩, hLL _ hLF'⟩
    rw [natVal_frame F3 hzN]
    rcases hvz with h | ⟨h0, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, by rw [h, natVal_frame hF hzN]⟩
  · obtain ⟨⟨sbok, sblen, sbor⟩, sbm⟩ := hsb
    refine ⟨⟨stkOK_frame sbok F3 hstw, by rw [eL3, sblen, eL], ?_⟩, ?_⟩
    · rw [eW3, eC3]
      rcases sbor with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by rw [h1, eW], by rw [h2, eC]⟩
      · exact Or.inr h
    · unfold ArrIn; rw [eW3, eC3]; intro hn'; apply sbm; rw [eW, eC]; exact hn'

set_option maxRecDepth 20000 in
/-- a callee called at `RSP - f` with a frame `R.rt ++ win S1 W1 88 ++ [z] ++ stkWs` (an inner `nat.mul`) keeps the
caller's frame above the callee's window: `[S1.rsp + 88, RSP + 88)` -/
theorem mul_keeps {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat}
    {s S1 : State} {m2 : Memory} {f W1 zp' zc' : Nat} (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s)
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hk : f + W1 ≤ W)
    (hF : MemFrame s.mem S1.mem (win s W 88)) (hz' : Outside zp' (8 * zc') (win s W 88))
    (hMF : MemFrame S1.mem m2 (R.rt ++ win S1 W1 88 ++ [(zp', zp' + 8 * zc')] ++ stkWs S1.mem st)) :
    ∀ a n, (S1.regs 4).toNat + 88 ≤ a → a + n ≤ (s.regs 4).toNat + 88 → m2.readLE a n = S1.mem.readLE a n := by
  obtain ⟨hce, -, -, -, -, -, hstk, -, -, -⟩ := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -⟩ := hce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, hstw, -, -, -, hfw, -⟩ := hstk
  obtain ⟨eW, eL, eC⟩ := hdr_frame hF hstw
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw hz'
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  intro a n h1 h2
  refine hMF.readLE _ _ ?_
  simp only [stkWs, win, outside_append, outside_cons, outside_nil, and_true]
  rw [eW, eL, eC]
  exact ⟨⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩, by omega, by omega⟩

end FvModexp.Amd64.Q.NatMul
