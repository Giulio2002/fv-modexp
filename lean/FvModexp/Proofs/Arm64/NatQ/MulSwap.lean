import FvModexp.Proofs.Arm64.NatQ.MulLift
import FvModexp.Proofs.Common.BitLemmas

/-!
# [Q-form copy of Arm64/Nat/MulSwap.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64): `m < n` → `return z.mul(stk, y, x)` (natmul.go:23), and `n = 0` → `return z[:0]` (:25)

`swap`: the entry → the self-call at `0x1bb15c` (operands swapped, via the induction hypothesis at the smaller
measure) → the return; `mpre_swap` / `mpost_comm` swap the operands of `MPre` / `MPost`. `zero`: `len y = 0`
(`m ≥ n = 0`) returns `z[:0]`, writes nothing (`post_nil`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}


open FvModexp.Arm64.Q.NatSqr (stackBack_keep)

theorem mpre_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    (h : MPre R b H L W zp zc st xp xl xc yp yl yc s) (hw : mulW yl xl ≤ W) :
    MPre R b H L W zp zc st yp yl yc xp xl xc s := by
  obtain ⟨hce, -, hsv, hglb, hty, hops, hstk, hcost, hinv⟩ := h
  exact ⟨hce, hw, hsv, hglb, hty, hops.swap, hstk, by rw [mulCQ_comm, Nat.add_comm yl xl]; exact hcost, hinv⟩

theorem mpost_comm {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s s' : State}
    (h : MPost R b H L W zp zc st yp yl yc xp xl xc s s') : MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨p', l', c', q0, q1, q2, hv, hn, hlc, hll, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex, hsb,
    hMF, hLF⟩ := h
  have em : natVal s.mem yp yl * natVal s.mem xp xl = natVal s.mem xp xl * natVal s.mem yp yl := Nat.mul_comm _ _
  refine ⟨p', l', c', q0, q1, q2, by rw [hv, em], hn, hlc, by omega, hc40, L', b', hext,
    by rw [mulCQ_comm]; exact hbud, hinv, hlive, ?_, hfa, ?_, hsb, hMF, hLF⟩
  · rcases hkind with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, h2, h3⟩
  · intro h1 h2 h3
    obtain ⟨e1, e2, hvz, hF, hLF'⟩ := hex (by omega) h3 h2
    rw [Nat.add_comm yl xl] at hvz hF hLF'
    rw [em] at hvz
    exact ⟨e1, e2, hvz, hF, hLF'⟩

private theorem kpA {x : Nat} (h : 264 ≤ x) : x - 256 - 8 ≤ x - 256 ∧ x - 256 + 8 ≤ x - 256 + 8 := by omega
private theorem kpB {x : Nat} (h : 264 ≤ x) : x - 256 - 8 ≤ x - 264 ∧ x - 264 + 8 ≤ x - 256 + 8 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- the self-call at `0x1bb15c` (`y`, `x` in `X4..X9`) and the return -/
theorem swap2 (impl : List Segment) (R : RtInv) (n : Nat) (ih : ∀ j, IH impl R H n j) {b : Nat}
    {L : List (Nat × Nat)} {W : Nat} {zp zl zc st xp xl xc yp yl yc : BitVec 64} {s : State}
    (hpreS : MPre R b H L W zp.toNat zc.toNat st.toNat yp.toNat yl.toNat yc.toNat xp.toNat xl.toNat xc.toNat s)
    (hμ : μl yl.toNat xl.toNat + 3 < n) (hw1 : mulW yl.toNat xl.toNat + 256 ≤ W)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb15c) (hsp : S.sp = s.sp - 256#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 264#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = zp) (r1 : S.regs 1 = zl) (r2 : S.regs 2 = zc) (r3 : S.regs 3 = st) (r4 : S.regs 4 = yp)
    (r5 : S.regs 5 = yl) (r6 : S.regs 6 = yc) (r7 : S.regs 7 = xp) (r8 : S.regs 8 = xl) (r9 : S.regs 9 = xc)
    (hF : MemFrame s.mem S.mem (winA s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (mlr : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (Q : State → Prop)
    (hfin : ∀ (S1 s2 s' : State), MemFrame s.mem S1.mem (winA s W 88) → S1.sp = S.sp → S1.regs 28 = S.regs 28 →
      MPost R b H L (W - 256) zp.toNat zc.toNat st.toNat yp.toNat yl.toNat yc.toNat xp.toNat
      xl.toNat xc.toNat S1 s2 → MemFrame s2.mem s'.mem (winA s W 88) → s'.regs 0 = s2.regs 0 →
      s'.regs 1 = s2.regs 1 → s'.regs 2 = s2.regs 2 → Q s') :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ Q s' := by
  have hpre' := hpreS
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩, hmw, -⟩ := hpre'
  have hW : 4608 ≤ W := by have := mulW_ge yl.toNat xl.toNat; omega
  have hsp' : S.sp.toNat = s.sp.toNat - 256 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hBS : Summary (LibMul.program.link impl) 0x1bae70 _ _ := Summary.mono
    (ih (.mul, ⟨b, L, W - 256, zp, zl, zc, st, yp, yl, yc, xp, xl, xc⟩))
    (pre' := fun s1 => (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48 ∧
      s1.regs 0 = zp ∧ s1.regs 1 = zl ∧ s1.regs 2 = zc ∧ s1.regs 3 = st ∧ s1.regs 4 = yp ∧ s1.regs 5 = yl ∧
      s1.regs 6 = yc ∧ s1.regs 7 = xp ∧ s1.regs 8 = xl ∧ s1.regs 9 = xc ∧ s1.sp = S.sp ∧
      s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (post' := fun s1 s2 => Kept s1 s2 ∧ s2.mem.accessible (s.sp.toNat - 264) 264 true = true ∧
      s2.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat ∧ s2.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat ∧
      IntAS.Box (∃ S1 : State, S1.mem = S.mem ∧ S1.sp = S.sp ∧ S1.regs 28 = S.regs 28 ∧
        MPost R b H L (W - 256) zp.toNat zc.toNat st.toNat yp.toNat
      yl.toNat yc.toNat xp.toNat xl.toNat xc.toNat S1 s2))
    (fun s1 ⟨hr4, hr48, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, hs, hg, hm⟩ => by
      refine ⟨⟨⟨hr4, hr48, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩, ?_⟩, hμ⟩
      show MPre R b H L (W - 256) zp.toNat zc.toNat st.toNat yp.toNat yl.toNat yc.toNat xp.toNat xl.toNat xc.toNat s1
      exact mpre_down hpreS (by rw [hs]; exact hsp') (by rw [hg, h28]) (by rw [hm]; exact hF) (by rw [hm]; exact hreg)
        (by omega) (by omega) (by omega) (by omega))
    (fun s1 s2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, hg, hm⟩ ⟨hk, hq⟩ => by
      have hMF : MemFrame s1.mem s2.mem (R.rt ++ winA s1 (W - 256) 88 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)] ++
          stkWs s1.mem st.toNat) := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, -⟩ := hq; exact h
      have hsp1 : s1.sp.toNat = s.sp.toNat - 256 := by rw [hs]; exact hsp'
      have hz' : Outside zp.toNat (8 * zc.toNat) (win s W 88) := hpreS.2.2.2.2.2.1.2.2.1.2.2.1
      have hF1 : MemFrame s.mem s1.mem (winA s W 88) := by rw [hm]; exact hF
      have h264 : 264 ≤ s.sp.toNat := Nat.le_trans (by decide) (Nat.le_trans hW hb0)
      have hkp := mul_keeps (W1 := W - 256) (f := 256) (S1 := s1) (m2 := s2.mem) hpreS hsp1 (by omega) (by omega)
        (by omega) hF1 hz' hMF
      have e1 : s2.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat := by
        rw [hkp (s.sp.toNat - 256) 8 (Or.inl (by rw [hsp1]; exact kpA h264)), hm]; exact mlr
      have e2 : s2.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat := by
        rw [hkp (s.sp.toNat - 264) 8 (Or.inl (by rw [hsp1]; exact kpB h264)), hm]; exact mfp
      have e3 : s2.mem.accessible (s.sp.toNat - 264) 264 true = true := by
        rw [hMF.accessible, hm, hF.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
      exact ⟨hk, e3, e1, e2, ⟨⟨s1, hm, hs, hg, hq⟩⟩⟩)
  janus_run until [0x1bb160] calls [hBS]
  rename_i e3 e1 e2 hbox
  obtain ⟨⟨S1, hm1, hs1, hg1, hq⟩⟩ := hbox
  clear hBS hpreS hμ hw1 ih
  janus_run [e1, e2]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin S1 _ _ (by rw [hm1]; exact hF) (by rw [hs1, hsp]) (by rw [hg1, h28]) hq ?qF ?_ ?_ ?_⟩
  case qF => simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem swap (impl : List Segment) (R : RtInv) (n : Nat) (ih : ∀ j, IH impl R H n j) (b : Nat)
    (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 0x1bae70) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hμ : μl xl.toNat yl.toNat + 3 = n) (hlt : xl.toNat < yl.toNat) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s fun s' =>
      Kept s s' ∧ MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩, hmw, -, -, -,
    ⟨⟨-, -, hxl12, -⟩, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hpre'
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hsw := mulW_swap hlt
  have hpreS := mpre_swap hpre (by omega)
  janus_run [toInt_small xl (by omega), toInt_small yl (by omega)] until [0x1bb15c]
  refine swap2 impl R n ih (zl := zl) hpreS (by rw [← hμ]; exact μ_swap hlt) (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?qF ?qreg ?qlr ?qfp hl4 hl48 _ fun S1 s2 s' hF1 hs1 hg1 hq F3 q0 q1 q2 =>
      mpost_comm (mpost_up hpreS (f := 256) (by rw [hs1]; janus_simp) (by omega) (by omega) (by rw [hg1]; janus_simp)
        hF1 hq F3 q0 q1 q2)
  case qF => simp only [winA]; janus_frame
  case qreg => janus_simp
  case qlr => janus_simp
  case qfp => janus_simp
  all_goals janus_simp

end FvModexp.Arm64.Q.NatMul
