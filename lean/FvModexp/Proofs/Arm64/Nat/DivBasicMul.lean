import FvModexp.Proofs.Arm64.Nat.DivBasicQh
import FvModexp.Proofs.Arm64.Nat.DivBasicMemF

/-!
# `divBasic` (arm64): `qhatv[n] = mulAddVWW(qhatv[0:n], v, qhat, 0)` (natdiv.go:703), `+0x160 → +0x194`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

/-- the frame facts at a point `pc` of the loop body (`j` stored at `SP-80`) -/
structure Bd (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (pc j : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 pc
  sp : S.sp = s.sp - 240#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 248#64
  r18 : S.regs 18 = s.regs 18
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S.mem
  jj : S.mem.readLE (s.sp.toNat - 80) 8 = j

/-- a store into the stack window keeps the runtime's view -/
theorem view_win {R : RtInv} {lo n0 : Nat} (hout : Outside lo n0 R.rt) (L : List (Nat × Nat)) (m : Memory)
    (a n v : Nat) (h1 : lo ≤ a) (h2 : a + n ≤ lo + n0) : view R.rt L (m.writeLE a n v) = view R.rt L m :=
  view_writeLE_out (hout.of_sub h1 h2)

abbrev callVww : Nat := segAddr Extracted.program fn + 0x190
abbrev afterVww : Nat := segAddr Extracted.program fn + 0x194

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem mul1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S mulPt j)
    (hr2 : S.regs 2 = BitVec.ofNat 64 qhat) (hq : qhat < 2 ^ 64) (Q : State → Prop)
    (k : ∀ S', Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' afterVww j →
      S'.mem.readLE (s.sp.toNat - 96) 8 = qhat →
      natVal S'.mem t vl = natVal s.mem vp vl * qhat % 2 ^ (64 * vl) →
      S'.mem.readLE (s.sp.toNat - 168) 8 = natVal s.mem vp vl * qhat / 2 ^ (64 * vl) →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hpc, hsp, h28, h29, h18, hM, hj⟩ := hB
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvb := hl.vb; have hv48 := hl.v48
  have ht48 := hl.t48
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hE.pre.ce
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have htacc : S.mem.accessible t (8 * vl) true = true := by
    rw [hMacc]; exact Memory.accessible_mono _ hE.scr.acc (by omega) (by omega)
  have hvacc : S.mem.accessible vp (8 * vl) false = true := by rw [hMacc]; exact hE.pre.vacc
  have hty : t = vp ∨ Apart t (8 * vl) vp (8 * vl) := by right; unfold Apart; have := hl.tv; omega
  have htr : Apart t (8 * vl) (s.sp.toNat - 240 + 72) 8 := by unfold Apart; have := hl.tw; omega
  have htH : Held R L1 t (8 * vl) := hl.theld.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 240 + 72) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg : Apart t (8 * vl) ((s.regs 28).toNat + 16) 8 := by unfold Apart; have := hl.tg; omega
  have hrg : Apart (s.sp.toNat - 240 + 72) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have hinv := hM.inv
  have m8 := hM.hc; have s8 := hM.s8; have tp := hM.tp; have s7 := hM.s7; have s9 := hM.s9
  have hvw := view_win hout L1
  janus_run [hr2, m8, s8, tp, s7, s9, hvw] until [afterVww] calls [vww impl hap R b1 L1]
  rename_i w hval hcar hFw hinvw hgd
  generalize hMc : ((((((((S.mem.writeLE (s.sp.toNat - 96) 8 qhat).writeLE (s.sp.toNat - 232) 8 t).writeLE
    (s.sp.toNat - 224) 8 vl).writeLE (s.sp.toNat - 216) 8 (vl + 1)).writeLE (s.sp.toNat - 208) 8 vp).writeLE
    (s.sp.toNat - 200) 8 vl).writeLE (s.sp.toNat - 192) 8 vc).writeLE (s.sp.toNat - 184) 8 qhat).writeLE
    (s.sp.toNat - 176) 8 0 = Mc at hval hcar hFw
  have hst : MemFrame S.mem Mc [(s.sp.toNat - 232, s.sp.toNat - 168), (s.sp.toNat - 96, s.sp.toNat - 88)] := by
    rw [← hMc]; janus_frame
  have hvw' := hl.vw
  have hvM : natVal Mc vp vl = natVal s.mem vp vl := by
    simp only [natVal]
    rw [hst.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hM.vs _ _ (by omega) (by omega)
  rw [hvM] at hval hcar
  have e72 : s.sp.toNat - 240 + 72 = s.sp.toNat - 168 := by omega
  rw [e72] at hcar hFw
  have hF : MemFrame S.mem w (scr s ++ wsL qp ql up ul vl t) := by
    refine (mfTrans hst hFw).mono fun a n ho => ?_
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have hM' := Mem.frame hE hM hF
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, hM', ?jj⟩ ?q1 hval hcar
  case jj =>
    show w.readLE _ _ = _
    have := hl.tw
    rw [hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hst.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hj
  case q1 =>
    show w.readLE _ _ = _
    have := hl.tw
    rw [hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hMc]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hq
  all_goals janus_simp

end FvModexp.Arm64.DivBasic
