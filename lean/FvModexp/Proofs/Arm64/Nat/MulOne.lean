import FvModexp.Proofs.Arm64.Nat.MulOneP
import FvModexp.Proofs.Arm64.Nat.MulOnePre
import FvModexp.Proofs.Arm64.Nat.Callees
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.mul` (arm64), `n = 1`: `return z.mulAddWW(x, y[0], 0)` (natmul.go:25-26)

`one`: the entry (`m ≥ n = 1`) → the call at `0x1bb108` (`R3..R5 = x`, `R6 = y[0]`, `R7 = 0`); `one2`: the call
(`MulAddWW.ensX`, pre by `pre_one`) → `0x1bb10c` (result stores) → the return; post by `mpost_one`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatMul

/-- `MulAddWW.ensX` with its side conditions in the precondition -/
theorem ensXR (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Ensures ((Extracted.program.onlySegments MulAddWW.names).link impl) (segAddr Extracted.program MulAddWW.fn)
      [zp, zl, zc, xp, xl, xc, y, r]
      (fun s => xl.toNat ≠ 0 ∧ xl.toNat < 2 ^ 39 ∧ r.toNat = 0 ∧ MulAddWW.Pre R b L zp zc xp xl y r s)
      (fun s s' => MulAddWW.Post R b L zp zc xp xl y r s s' ∧ MulAddWW.XQ R L zp zc xp xl y r s s') := by
  intro ret hret s hs ⟨h1, h2, h3, hpre⟩
  exact MulAddWW.ensX impl hap R hmk b L zp zl zc xp xl xc y r h1 h2 h3 ret hret s hs hpre

theorem toSummaryRegs8 {p0 P : Program} {entry : Nat}
    {pre : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State → Prop}
    {post : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State →
      State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7]
      (pre a0 a1 a2 a3 a4 a5 a6 a7) (post a0 a1 a2 a3 a4 a5 a6 a7))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs 30).toNat ∧
        pre (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7) s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧
        post (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7) s s') := by
  intro s hpc ⟨hret, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6)
    (s.regs 7)) hx hc s hpc ⟨hret, by simp [ArgsFrom], hpre⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- the call `z.mulAddWW(x, y[0], 0)` at `0x1bb108` and the return -/
theorem one2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W : Nat} {zp zl zc xp xl xc : BitVec 64} {st yp yc : Nat} {s : State}
    (hpre : MPre R b L W zp.toNat zc.toNat st xp.toNat xl.toNat xc.toNat yp 1 yc s) (hx1 : xl.toNat ≠ 0)
    (y0 : BitVec 64) (hy0 : y0.toNat = s.mem.readLE yp 8)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bb108) (hsp : S.sp = s.sp - 256#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 264#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = zp) (r1 : S.regs 1 = zl) (r2 : S.regs 2 = zc) (r3 : S.regs 3 = xp) (r4 : S.regs 4 = xl)
    (r5 : S.regs 5 = xc) (r6 : S.regs 6 = y0) (r7 : S.regs 7 = 0#64)
    (hF : MemFrame s.mem S.mem (winA s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (mlr : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b L W zp.toNat zc.toNat st xp.toNat xl.toNat xc.toNat yp 1 yc s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩, hmw,
    -, -, -, ⟨⟨-, -, hxl12, -⟩, -, ⟨-, -, hzw, -⟩, -⟩, -⟩ := hpre'
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  have hsp' : S.sp.toNat = s.sp.toNat - 256 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hc : CodeIn ((Extracted.program.onlySegments MulAddWW.names).link impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hM := toSummaryRegs8 (fun a0 a1 a2 a3 a4 a5 a6 a7 => ensXR impl hap R hmk b L a0 a1 a2 a3 a4 a5 a6 a7)
    (noExit_restrict hap MulAddWW.names) hc
  clear hc
  have hBS := Summary.mono hM
    (pre' := fun s1 => RetAddr ((Extracted.program.onlySegments MulAddWW.names).link impl) (s1.regs 30).toNat ∧
      s1.regs 0 = zp ∧ s1.regs 1 = zl ∧ s1.regs 2 = zc ∧ s1.regs 3 = xp ∧ s1.regs 4 = xl ∧ s1.regs 5 = xc ∧
      s1.regs 6 = y0 ∧ s1.regs 7 = 0#64 ∧ s1.sp = S.sp ∧ s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (post' := fun s1 s2 => Kept s1 s2 ∧ s2.mem.accessible (s.sp.toNat - 264) 264 true = true ∧
      s2.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat ∧ s2.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat ∧
      IntAS.Box (∃ S1 : State, S1.mem = S.mem ∧ S1.sp = S.sp ∧ S1.regs 28 = S.regs 28 ∧
        (MulAddWW.Post R b L zp zc xp xl y0 0#64 S1 s2 ∧ MulAddWW.XQ R L zp zc xp xl y0 0#64 S1 s2)))
    (fun s1 ⟨hra, q0, q1, q2, q3, q4, q5, q6, q7, hs, hg, hm⟩ => by
      refine ⟨hra, ?_⟩
      simp only [q0, q2, q3, q4, q6, q7]
      refine ⟨hx1, by omega, by simp, ?_⟩
      exact pre_one hpre hx1 (by rw [hs]; exact hsp') (by rw [hg, h28]) (by rw [hm]; exact hF)
        (by rw [hm]; exact hreg))
    (fun s1 s2 ⟨_, q0, q1, q2, q3, q4, q5, q6, q7, hs, hg, hm⟩ ⟨hk, hq⟩ => by
      simp only [q0, q2, q3, q4, q6, q7] at hq
      have hMF : MemFrame s1.mem s2.mem (R.rt ++ winA s1 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) := by
        obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, -⟩, -⟩ := hq; exact h
      have hsp1 : s1.sp.toNat = s.sp.toNat - 256 := by rw [hs]; exact hsp'
      have hkp : ∀ a n, s.sp.toNat - 264 ≤ a → a + n ≤ s.sp.toNat - 248 → s2.mem.readLE a n = s1.mem.readLE a n :=
        fun a n h1 h2 => hMF.readLE a n (by
          simp only [outside_append, winA, outside_cons, outside_nil, and_true]
          rw [hsp1]
          exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
      have e1 : s2.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat := by
        rw [hkp _ _ (by omega) (by omega), hm]; exact mlr
      have e2 : s2.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat := by
        rw [hkp _ _ (by omega) (by omega), hm]; exact mfp
      have e3 : s2.mem.accessible (s.sp.toNat - 264) 264 true = true := by
        rw [hMF.accessible, hm, hF.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
      exact ⟨hk, e3, e1, e2, ⟨⟨s1, hm, hs, hg, hq⟩⟩⟩)
  clear hM
  janus_run until [0x1bb10c] calls [hBS]
  rename_i e3 e1 e2 hbox
  obtain ⟨⟨S1, hm1, hs1, hg1, hq⟩⟩ := hbox
  janus_run [e1, e2]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_one hpre hx1
    (by rw [hs1]; first | exact hsp' | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))
    (by rw [hg1]; try rw [h28]) (by rw [hm1]; first | exact hF | skip) hy0 hq
    ?qF ?_ ?_ ?_⟩
  case qF => simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.mul`, `m ≥ n = 1`** -/
theorem one (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy : yl.toNat = 1) (hyx : yl.toNat ≤ xl.toNat) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s fun s' =>
      Kept s s' ∧ MPost R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩, hmw, -, -, -,
    ⟨⟨-, -, hxl12, -⟩, ⟨-, -, -, hyacc, -, hyw⟩, -⟩, -⟩ := hpre'
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hyw' := (hyw (by omega)).1
  simp only [win, outside_cons, outside_nil, and_true] at hyw'
  have hyl1 : yl = 1#64 := BitVec.eq_of_toNat_eq (by simp [hy])
  subst hyl1
  simp only [show (1#64 : BitVec 64).toNat = 1 from rfl] at hpre hyx ⊢
  have hx0' : (xl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hyx; simp at hyx
  have hy8 : s.mem.accessible yp.toNat 8 false = true := by simpa using hyacc
  janus_run [toInt_small xl (by omega), hx0'] until [0x1bb108]
  refine one2 impl hap R hmk (zl := zl) hpre (by omega) _ ?hy0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_
    (by simp only [winA]; janus_frame) ?qreg ?qlr ?qfp hl4 hl48
  case hy0 => janus_simp
  case qreg => janus_simp
  case qlr => janus_simp
  case qfp => janus_simp
  all_goals janus_simp

end FvModexp.Arm64.NatMul
