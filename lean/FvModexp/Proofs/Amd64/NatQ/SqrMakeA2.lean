import FvModexp.Proofs.Amd64.NatQ.SqrMakeA1
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/SqrMakeA2.lean — TIGHT COSTS, divmc s38] `nat.sqr` (amd64), `make_alloc` call: `makeslice(Word, 2n, 2n + 4)` from `AA` (`0x5f1101` → `0x5f1106`) → the join

The run through the call (`hmk.pos`; the type descriptor's facts from `wordT_data`, its `Outside … calleeStack` from the
rodata `Apart`), the reloads (`MOVQ 0x58(SP), BX` … `MOVQ 0x50(SP), CX`), the spills `0x50/0x68(SP)` and the join
`0x5f1140`, then `Core.wfr (core_alloc …)` and `JoinAt`. Twin of arm64 SqrMakeA2 (divmc s32).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem alloc_call (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp _zl zc st xp xl xc : BitVec 64) (s S : State) (hA : AA s S W st xp xl xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) S Q := by
  have hpre' := hpre
  obtain ⟨hce, hsw, hsv, -, hty, hxlc, -, hxl12, -, hxh, -, -, -, -, -, -, -, -, -, ⟨-, hcost⟩, -, hinv⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hga hgr
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxh' := (hxh (by omega)).1
  obtain ⟨hpc, r0, r3, r1, hsp, hg, h5, hfs, hdf, hx15, mret, mra, mbp, m80, m88, mst, mxp, mxl, mxc, hF0, hreg⟩ := hA
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, 2 * xl.toNat, 2 * xl.toNat + 4] := hsv.1 _ _ _ (by omega)
  have hmc : makeB (2 * xl.toNat) = allocCost (8 * (2 * xl.toNat + 4)) := rfl
  have hmc2 : makeB (2 * xl.toNat) ≤ sqrCQ xl.toNat := by unfold sqrCQ; omega
  have hbl := blockSize_le_allocCost (8 * (2 * xl.toNat + 4)) true
  have hbs : blockSize (8 * (2 * xl.toNat + 4)) true ≤ b := by omega
  have hwt : Apart NatAdd.wordT 16 ((s.regs 4).toNat - W) (W + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  obtain ⟨_hwa, _hws, _hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt r0
  simp only [LiveSep, win] at hLs
  have hinvS : R.inv b L (s.regs 14).toNat (view R.rt L S.mem) := inv_frame_win hF0 hout (by omega) (by decide) hinv
  clear hxh hsw hinv
  janus64_run [BitVec.msb_eq_decide, mod64_of_lt (2 * xl.toNat) (by omega), mod64_of_lt (2 * xl.toNat + 4) (by omega),
    _hws, _hwp] until [0x5f1140] calls [hmk.pos L b]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv'
  refine hK ptr.toNat (2 * xl.toNat + 4) _ _ _ (Core.wfr (core_alloc (c := 2 * xl.toNat + 4) hpre hF0
      ?qcs hLF hMF hAp hIn hle ?qacc (h8 (Or.inr (by omega))) hinv' ?q1 ?q2 ?q3 ?q4 ?q5 hz) ?hF2)
    ⟨?jpc, ?j0, ?j3, ?j1, ?j7, ?j6, ?j8, ?j9, ?jsp, ?jg, ?jbp, ?jfs, ?jdf, ?jx15, ?jra, ?jmbp, ?j64, ?j80, ?j88,
      ?jreg, apart_of_held (hxh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs1)
        (ApartAll.sub' hAp (Nat.le_refl _) ?qs2), ?qna⟩
  case qna =>
    have := apart_of_held hxh' (hIn.sub (Nat.le_refl _) (n := 8 * (2 * xl.toNat + 4)) (by omega))
      (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
    unfold Apart at this; omega
  case qs1 => omega
  case qs2 => omega
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
    | fail "SHOW"

end FvModexp.Amd64.Q.NatSqr
