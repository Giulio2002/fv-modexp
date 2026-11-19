import FvModexp.Proofs.Amd64.NatQ.MulOneP
import FvModexp.Proofs.Amd64.NatQ.MulBM
import FvModexp.Proofs.Amd64.Nat.MulAddWWX

set_option autoImplicit false

/-!
# [amd64 port (divmc s44) of the Q-form Arm64/NatQ/MulOne.lean — TIGHT COSTS] `nat.mul` (amd64), `n = 1`: `return z.mulAddWW(x, y[0], 0)` (natmul.go:25-26)

`one`: the entry `0x5f0840` (`m ≥ n = 1`: `CMPQ R8, R10; JL` not taken, `CMPQ R10, $1; JE 0x5f0bd9`) → `DX = y[0]`,
`DI, SI, R8 = x`, `R9 = y[0]`, `R10 = 0`, `CALL mulAddWW` (`0x5f0bf3`, return `0x5f0bf8` pushed at `RSP - 264`) →
the callee's entry; `waCall`: the call (`MulAddWW.ensX`, pre by `pre_one`); then the result stores at
`0x98(SP') …`, `ADDQ $0xf8, SP; POPQ BP; RET`; post by `mpost_one`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

/-- `MulAddWW.ensX` with its side conditions in the precondition -/
theorem ensXR (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Ensures ((Extracted.program.onlySegments MulAddWW.names).link impl) (segAddr Extracted.program MulAddWW.fn)
      [zp, zl, zc, xp, xl, xc, y, r]
      (fun s => xl.toNat ≠ 0 ∧ xl.toNat < 2 ^ 39 ∧ r.toNat = 0 ∧ MulAddWW.Pre R b L zp zc xp xl y r s)
      (fun s s' => MulAddWW.Post R b L zp zc xp xl y r s s' ∧ MulAddWW.XQ R L zp zc xp xl y r s s') := by
  janus64_ensures_old [FvModexp.Amd64.MulAddWW.Pre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.MulAddWW.wordT, FvModexp.NatLive, FvModexp.Amd64.win, FvModexp.Amd64.TlsOK]
  intro ret hret s hs ⟨h1, h2, h3, hpre⟩
  exact (MulAddWW.ensX impl hap R hmk b L zp zl zc xp xl xc y r h1 h2 h3).toOld ret hret s hs hpre

/-- adapted from asm's `FvModexp.Amd64.DivW.Ensures.toSummaryRegs8` (Proofs/Amd64/Nat/DivWDefs.lean) -/
theorem toSummaryRegs8 {p0 P : Amd64.Program} {entry : Nat}
    {pre : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State → Prop}
    {post : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State →
      State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7]
      (pre a0 a1 a2 a3 a4 a5 a6 a7) (post a0 a1 a2 a3 a4 a5 a6 a7))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧ s.df = false ∧
        pre (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        post (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) s s') := by
  intro s hpc ⟨hret, hz, hdf, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9)
    (s.regs 10)) hx (by simp [numIntRegs]) hc s hpc ⟨hret, hz, by simp [ArgsFrom64, argReg, intArgRegs], hdf, hpre⟩

set_option maxRecDepth 20000 in
/-- a call of `mulAddWW` (`ensXR`) at its entry returning to `0x5f0bf8` -/
theorem waCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} {S : State} {ret : W64}
    {Q : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program MulAddWW.fn))
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = 0x5f0bf8)
    (h0 : S.regs 0 = a0) (h3 : S.regs 3 = a1) (h1 : S.regs 1 = a2) (h7 : S.regs 7 = a3) (h6 : S.regs 6 = a4)
    (h8 : S.regs 8 = a5) (h9 : S.regs 9 = a6) (h10 : S.regs 10 = a7)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false) (ha4 : a4.toNat ≠ 0) (ha4' : a4.toNat < 2 ^ 39) (ha7 : a7.toNat = 0)
    (hpre : MulAddWW.Pre R b L a0 a2 a3 a4 a6 a7 S)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 0x5f0bf8 → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      (MulAddWW.Post R b L a0 a2 a3 a4 a6 a7 S s' ∧ MulAddWW.XQ R L a0 a2 a3 a4 a6 a7 S s') →
      s'.mem.regions = S.mem.regions → ReachesRet (LibMul.program.link impl) ret s' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hc : CodeIn64 ((Extracted.program.onlySegments MulAddWW.names).link impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hM := toSummaryRegs8 (fun a0 a1 a2 a3 a4 a5 a6 a7 => ensXR impl hap R hmk b L a0 a1 a2 a3 a4 a5 a6 a7)
    (A64.noExit_restrict64 hap MulAddWW.names) hc
  refine ReachesRet.call_regions hM hpc ⟨?_, hx15, hdf, ?_⟩ fun s' hr ⟨⟨e4, e5, e14, e15⟩, hq⟩ hrg => ?_
  · simp only [regSP]; rw [hrd]
    exact ra_mul (i := 0x3b8) hap (by decide) (by decide)
  · rw [h0, h1, h7, h6, h9, h10]; exact ⟨ha4, ha4', ha7, hpre⟩
  · rw [h0, h1, h7, h6, h9, h10] at hq
    refine K s' ?_ e4 e5 e14 e15 hq hrg
    rw [hr, retAddrOf, hrd]

/-- the caller's saved `RBP` / return-address slots survive the `mulAddWW` call (small context) -/
theorem one_kp {R : RtInv} {s S1 : State} {m2 : Memory} {W zp zc : Nat}
    (hMF : MemFrame S1.mem m2 (R.rt ++ win S1 4208 72 ++ [(zp, zp + 8 * zc)]))
    (hsp1 : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hout0 : Outside ((s.regs 4).toNat - W) (W + 88) R.rt)
    (hW : 4608 ≤ W) (hb0 : W ≤ (s.regs 4).toNat)
    (hzw : zp + 8 * zc ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 88 ≤ zp) :
    ∀ a n, (s.regs 4).toNat - 192 ≤ a → a + n ≤ (s.regs 4).toNat + 88 → m2.readLE a n = S1.mem.readLE a n := by
  intro a n h1 h2
  refine hMF.readLE a n ?_
  simp only [outside_append, win, outside_cons, outside_nil, and_true]
  rw [hsp1]
  exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega⟩, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- after `mulAddWW` returns (`0x5f0bf8`): the result stores at `RSP - 104 …`, `ADDQ $0xf8, SP; POPQ BP; RET` -/
theorem one_ret (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W : Nat}
    {zp zc xp xl : BitVec 64} {st xc yp yc : Nat} {y0 : BitVec 64} {s S1 s2 : State}
    (hpre : MPre R b H L W zp.toNat zc.toNat st xp.toNat xl.toNat xc yp 1 yc s) (hx1 : xl.toNat ≠ 0)
    (hy0 : y0.toNat = s.mem.readLE yp 8)
    (hsp1 : S1.regs 4 = s.regs 4 - 264#64) (hg1 : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64)
    (hx15 : S1.xmm 15 = s.xmm 15) (hfs1 : S1.fsBase = s.fsBase) (hdf1 : S1.df = s.df)
    (hF1 : MemFrame s.mem S1.mem (win s W 88))
    (mra : S1.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : S1.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hrip : s2.rip = BitVec.ofNat 64 0x5f0bf8) (e4 : s2.regs 4 = S1.regs 4 + 8) (e5 : s2.regs 5 = S1.regs 5)
    (e14 : s2.regs 14 = S1.regs 14) (e15 : s2.xmm 15 = S1.xmm 15)
    (hq : MulAddWW.Post R b L zp zc xp xl y0 0#64 S1 s2 ∧ MulAddWW.XQ R L zp zc xp xl y0 0#64 S1 s2)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s2 fun s' =>
      Kept s s' ∧ MPost R b H L W zp.toNat zc.toNat st xp.toNat xl.toNat xc yp 1 yc s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb0, ha0, hw0⟩, hal0, -, hout0, -⟩, hmw, -, -, -, ⟨-, -, ⟨-, -, hzw, -⟩, -⟩, -⟩ := hpre'
  simp only [regSP] at hb0 ha0 hw0
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  have hsp1' : (S1.regs 4).toNat = (s.regs 4).toNat - 264 := by
    rw [hsp1, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hMF : MemFrame S1.mem s2.mem (R.rt ++ win S1 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) := by
    obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, -⟩, -⟩ := hq; exact h
  have hkp := one_kp hMF hsp1' hout0 hW hb0 hzw
  have q0 : s2.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    (hkp _ _ (by omega) (by omega)).trans mra
  have q8 : s2.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat :=
    (hkp _ _ (by omega) (by omega)).trans mbp
  have hacc : s2.mem.accessible ((s.regs 4).toNat - 256) 264 true = true := by
    rw [hMF.accessible, hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp2 : s2.regs 4 = s.regs 4 - 256#64 := by
    have h8 : (S1.regs 4 + 8).toNat = (s.regs 4).toNat - 256 := by
      have e8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [BitVec.toNat_add, hsp1', e8]; omega
    apply BitVec.eq_of_toNat_eq; rw [e4, h8, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have qfs : s2.fsBase = S1.fsBase := hq.1.1
  have qdf : s2.df = S1.df := hq.1.2.1
  janus64_run [hsp2, q0, q8, BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_one hpre hx1 hsp1' hg1 hF1 hy0 hq ?F3 ?_ ?_ ?_ ?_ ?_⟩
  case F3 => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact qfs.trans hfs1 | exact qdf.trans hdf1 | exact e15.trans hx15 | exact e14.trans hg1 | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- **`nat.mul`, `m ≥ n = 1`** -/
theorem one (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0840)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hy1 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat) (hy2 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat)
    (hy3 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy : yl.toNat = 1) (hyx : yl.toNat ≤ xl.toNat) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s fun s' =>
      Kept s s' ∧ MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hmw, -, -, -, ⟨⟨-, -, hxl12, -⟩, ⟨-, -, -, hyacc, -, hyw⟩, ⟨-, -, hzw, -⟩, -⟩, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hyw' := (hyw (by omega)).1
  simp only [win, outside_cons, outside_nil, and_true] at hyw' hzw
  have hyl1 : yl = 1#64 := BitVec.eq_of_toNat_eq (by simp [hy])
  subst hyl1
  simp only [show (1#64 : BitVec 64).toNat = 1 from rfl] at hpre hyx hy2 ⊢
  have hx0' : (xl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hyx; simp at hyx
  have hy8 : s.mem.accessible yp.toNat 8 false = true := by simpa using hyacc (by omega)
  have hwa : MulAddWW.fn = MulAddWW.fn := rfl
  have he : segAddr Extracted.program MulAddWW.fn = 0x5f1940 := by decide
  janus64_run [BitVec.msb_eq_decide, toInt_small xl (by omega), hx0'] until [0x5f1940]
  have e264 : (s.regs 4 - 264#64).toNat = (s.regs 4).toNat - 264 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine waCall hap hmk (b := b) (L := L) (a0 := zp) (a1 := zl) (a2 := zc) (a3 := xp) (a4 := xl) (a5 := xc)
    (a6 := BitVec.ofNat 64 (s.mem.readLE yp.toNat 8)) (a7 := 0#64) (by rw [he])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e264, Arm64.Memory.readLE_writeLE_self])
    ?r0 ?r3 ?r1 ?r7 ?r6 ?r8 ?r9 ?r10 ?x15 rfl (by omega) (by omega) rfl ?pre (fun s2 hr e4 e5 e14 e15 hq hrg => ?k)
  case pre =>
    exact pre_one hpre (by omega) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e264)
      (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) rfl (by simp only [win]; janus_frame)
      (by simp only [Arm64.Memory.regions_writeLE])
  case x15 => janus64_simp
  case k =>
    exact one_ret impl hpre (by omega) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp) (by simp only [win]; janus_frame) (by janus64_simp)
      (by janus64_simp) hr e4 e5 e14 e15 hq hra
  all_goals try (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | exact h0 | exact h3 | exact h1 | exact h6 | exact h8 | exact h9)
  all_goals try janus64_simp

end FvModexp.Amd64.Q.NatMul
