import FvModexp.Proofs.Amd64.Nat.SqrOne
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-!
# `nat.sqr` (amd64), `n = 1`, `cap z < 2`: `z = makeslice(Word, 2, 6)`; `z[1], z[0] = mulWW(x[0], x[0])` (natmul.go:78-82)

`one_alloc`: the entry → `makeslice` (CALL `0x5f1060`, return `0x5f1065`; `janus64_run … calls [hmk.pos L b]`) → `MULQ`,
the stores → `hnorm1`, then `one_tail` with `core_alloc`. Twin of arm64 `SqrOne.one_alloc` (divmc s32).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem one_alloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0fe0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : xl.toNat = 1)
    (hz : zc.toNat < 2) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) s fun s' =>
      Kept s s' ∧ SPost R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hsw, hsv, -, hty, -, -, -, hxacc, -, hxw, hzc40, -, -, -, -, -, -, -, hcost, -, hinv⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hga hgr
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxw := hxw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hxl1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl1
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, 2, 6] := hsv.1 _ _ _ (by decide)
  have hmc : sqrC (stLen s.mem st.toNat) (1#64).toNat = allocCost (8 * 6) := by
    unfold sqrC makeB; simp
  have hbl := blockSize_le_allocCost (8 * 6) true
  have hbs : blockSize (8 * 6) true ≤ b := by omega
  have hwt : Apart NatAdd.wordT 16 ((s.regs 4).toNat - W) (W + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  obtain ⟨_hwa, _hws, _hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  janus64_run [BitVec.msb_eq_decide, toInt_small zc (by omega), _hws, _hwp] until [hnorm1] calls [hmk.pos L b]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv'
  have hpw : Apart ((s.regs 4).toNat - W) (W + 64) ptr.toNat 48 := by
    have := NatAdd.outside_of_inRanges hout hIn
    first | exact this | (unfold Apart at this ⊢; omega) | (unfold Apart; omega)
  unfold Apart at hpw
  have hmb : makeB (2 * (1#64).toNat) = allocCost (8 * 6) := by unfold makeB; simp
  refine one_tail impl (core_alloc (c := 6) hpre ?hF (fun a n h => by
      simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega) hLF hMF hAp hIn (by omega)
      (by rw [hMF.accessible]; exact hacc) h8 hinv'
      (by decide) (by rw [hmb]; unfold allocCost; omega) (by simp) (by decide) (by decide) (Or.inl (by simp; omega)))
    (by simp) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [win, List.cons_append, List.nil_append]; janus_frame) ?qV
    ?qR1 ?qR2 hra
  case hF => simp only [win]; janus_frame
  case qV =>
    rw [natVal_two]
    janus64_simp
    show _ = s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8
    generalize s.mem.readLE xp.toNat 8 * s.mem.readLE xp.toNat 8 = q
    have := Nat.mod_add_div q 18446744073709551616; omega
  case qR1 =>
    janus64_simp
  case qR2 =>
    janus64_simp
  all_goals try janus64_simp
  all_goals first
    | exact IntAS.bv_ofNat_toNat _
    | fail "SHOW"

end FvModexp.Amd64.NatSqr
