import FvModexp.Proofs.Amd64.NatQ.MulMakeA1
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulMakeA2.lean — TIGHT COSTS] `nat.mul` (amd64): `makeslice(Word, m + n, m + n + 4)` → the join `0x5f09d5`

From the `makeslice` entry (`AA`): the live contract's call (`hmk.pos`; the type descriptor is rodata, `apart_of_data`),
the reloads (`MOVQ 0x108(SP), DX` … `MOVQ 0x58(SP), CX`), the spills `0x58/0x90(SP')` and the join, then
`Core.wfr (core_alloc …)` and `JoinAt` (twin of Amd64/NatQ/SqrMakeA2).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (apart_of_held inv_frame_win)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem alloc_call (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibMul.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp _zl zc st xp xl xc yp yl yc : BitVec 64) (s S : State) (hA : AA s S W st xp xl xc yp yl yc)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hyl2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S Q := by
  have hpre' := hpre
  obtain ⟨hce, hmw, hsv, -, hty, ⟨⟨hxlc, -, hxl12, -, hxh, -⟩, ⟨hylc, -, hyl12, -, hyh, -⟩, -, -⟩, -, ⟨-, hcost⟩, -,
    hinv⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hga hgr
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hxh' := (hxh (by omega)).1
  have hyh' := (hyh (by omega)).1
  obtain ⟨hpc, r0, r3, r1, hsp, hg, h5, hfs, hdf, hx15, mret, mra, mbp, m144, m168, mst, mxp, mxl, mxc, my1, my2, my3,
    hF0, hreg⟩ := hA
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, xl.toNat + yl.toNat, xl.toNat + yl.toNat + 4] :=
    hsv.1 _ _ _ (by omega)
  have hmc : makeB (xl.toNat + yl.toNat) = allocCost (8 * (xl.toNat + yl.toNat + 4)) := rfl
  have hmc2 : makeB (xl.toNat + yl.toNat) ≤ mulCQ xl.toNat yl.toNat := by
    unfold mulCQ; rw [Nat.max_eq_left hyx, Nat.min_eq_right hyx]; exact MCQ_basic hyl2
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + yl.toNat + 4)) true
  have hbs : blockSize (8 * (xl.toNat + yl.toNat + 4)) true ≤ b := by omega
  have hwt : Apart NatAdd.wordT 16 ((s.regs 4).toNat - W) (W + 88) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  obtain ⟨_hwa, _hws, _hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt r0
  simp only [LiveSep, win] at hLs
  have hinvS : R.inv b L (s.regs 14).toNat (view R.rt L S.mem) := inv_frame_win hF0 hout (by omega) (by decide) hinv
  clear hxh hyh hmw hinv
  janus64_run [BitVec.msb_eq_decide, mod64_of_lt (xl.toNat + yl.toNat) (by omega),
    mod64_of_lt (xl.toNat + yl.toNat + 4) (by omega), _hws, _hwp] until [0x5f09d5] calls [hmk.pos L b]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv'
  refine hK ptr.toNat (xl.toNat + yl.toNat + 4) _ _ _ (Core.wfr (core_alloc (c := xl.toNat + yl.toNat + 4) hpre hF0
      ?qcs hLF hMF hAp hIn hle ?qacc (h8 (Or.inr (by omega))) hinv' ?q1 ?q2 ?q3 ?q4 ?q5 hz) ?hF2)
    ⟨?jpc, ?j0, ?j3, ?j1, ?j7, ?j6, ?j8, ?j9, ?j2, ?j10, ?j11, ?jsp, ?jg, ?jbp, ?jfs, ?jdf, ?jx15, ?jra, ?jmbp, ?j112,
      ?j144, ?j168, ?j64, ?j72, ?j80, ?jy1, ?jy2, ?jy3, ?jreg,
      apart_of_held (hxh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs1)
        (ApartAll.sub' hAp (Nat.le_refl _) ?qs2),
      apart_of_held (hyh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs3)
        (ApartAll.sub' hAp (Nat.le_refl _) ?qs4), ?qnx, ?qny⟩
  case qnx =>
    have := apart_of_held hxh' (hIn.sub (Nat.le_refl _) (n := 8 * (xl.toNat + yl.toNat + 4)) (by omega))
      (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
    unfold Apart at this; omega
  case qny =>
    have := apart_of_held hyh' (hIn.sub (Nat.le_refl _) (n := 8 * (xl.toNat + yl.toNat + 4)) (by omega))
      (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
    unfold Apart at this; omega
  case qs1 => omega
  case qs2 => omega
  case qs3 => omega
  case qs4 => omega
  case hF2 => simp only [win]; janus_frame
  case qcs => intro a n h; simp only [win, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  case qacc => rw [hMF.accessible, hF0.accessible]; exact hacc
  case q1 => omega
  case q2 => rw [hmc]; exact blockSize_le_allocCost _ true
  case q3 => omega
  case q4 => omega
  case q5 => omega
  all_goals try janus64_simp
  all_goals first
    | rfl
    | exact hrg1.trans hreg
    | omega
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.Q.NatMul
