import FvModexp.Proofs.Arm64.Nat.DivBasicRel

set_option autoImplicit false
/-!
# `divBasic` (arm64): after `stk.nat` — `vn1 := v[n-1]`, `rec := reciprocalWord(vn1)`, `j := m`, `ujn := 0`, to the
loop head (natdiv.go:654-662)

`pro3a`: from the return of `stk.nat` (`AfterNat`) to the return of `reciprocalWord`; `pro3b`: to the loop head, where
`Env` and `Mem` hold (handed to a continuation).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

theorem LiveFrame.trans' {m1 m2 m3 : Memory} {L ws : List (Nat × Nat)} (h1 : LiveFrame m1 m2 L ws)
    (h2 : LiveFrame m2 m3 L ws) : LiveFrame m1 m3 L ws :=
  ⟨fun a n hin ho => (h2.readLE a n hin ho).trans (h1.readLE a n hin ho)⟩

/-- `Env` from `stk.nat`'s post (pure) -/
theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (hpre : Pre R b L qp ql st up ul uc vp vl s) {S2 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hext : LiveExt R L L1) (hbud : b - ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen s.mem st + (vl + 1 + 3) / 4 * 4)
    (hsame : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st → stW S2 st = stW s.mem st ∧ stCap S2 st = stCap s.mem st)
    (hgrow : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = s.mem.accessible a n v)
    (hmem : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 → (stW S2 st, stW S2 st + 8 * stCap S2 st) ∈ L1) :
    Env R b L qp ql st up ul uc vp vl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have hscr := Scr.of_post (m0 := s.mem) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_, ?_⟩
  · rw [← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hacc2]; exact a3, a4⟩
  · exact (ArrIn.of_nat (L1 := L1) (m0 := s.mem) (m := S2) hlc hlen hsame hmem :)




set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- after `stk.nat` returned (`S2`): `vn1 := v[n-1]`, `rec := reciprocalWord(vn1)`, `j := m`, `ujn := 0` → the head -/
theorem pro3 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkSN abSN : Nat)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : BitVec 64) (s : State)
    (hpre : Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s)
    (P : State) (hP : AtNat R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s P)
    (S2 : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (hA : AfterNat R b L st.toNat vl.toNat s P S2 stkSN abSN L1 b1) (Q : State → Prop)
    (k : ∀ S t w1 c1, Hd R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s
      t L1 b1 w1 c1 S (ul.toNat + 2 ^ 64 - vl.toNat) 0 →
      (∀ a n, (qp.toNat ≤ a ∧ a + n ≤ qp.toNat + 8 * ql.toNat) ∨ (up.toNat ≤ a ∧ a + n ≤ up.toNat + 8 * ul.toNat) →
        S.mem.readLE a n = s.mem.readLE a n) → ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S2 Q := by
  obtain ⟨-, -, -, -, -, -, -, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ := hP
  obtain ⟨hpc2, hsp2, h28, h29, h18, hr0, hr1, hr2, hext, hbud, hinv2, hok, hlen2, hsame, hgrow, hF2, hLF2, hmem⟩ := hA
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hpre.ce
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hfw := hpre.stfw; simp only [win, outside_cons, outside_nil, and_true, freeP, freeN] at hfw
  have hlc := hpre.stok.2.2.2.2.2.1
  have hPs : ∀ a n, (a + n ≤ s.sp.toNat - 248 ∨ s.sp.toNat + 88 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
  have hE := env_of (S2 := S2.mem) hpre hext hbud hok hlen2 hsame hgrow
    (fun a n v => by rw [hF2.accessible, hF.accessible]) hmem
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvb := hl.vb; have hv48 := hl.v48
  -- reads of `S2.mem` in the frame
  have k2 : ∀ a n, (s.sp.toNat - 248 ≤ a ∧ a + n ≤ s.sp.toNat - 232) ∨ (s.sp.toNat - 144 ≤ a ∧ a + n ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 88) → S2.mem.readLE a n = P.mem.readLE a n := by
    intro a n ha
    refine hF2.readLE _ _ ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega⟩
  -- `v` in `S2.mem`
  have hvS : ∀ a n, vp.toNat ≤ a → a + n ≤ vp.toNat + 8 * vl.toNat → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have hvw := hl.vw
    have hfr := hpre.free.2.2; have hsv := hpre.stv
    simp only [freeP, freeN] at hfr
    unfold Apart at hfr hsv
    rw [Held.readLE2 (hpre.vh.sub h1 h2) hF2 hLF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega), hPs a n (by omega)]
  have q8 := (k2 _ 8 (by omega)).trans p16
  have qn1 := (k2 _ 8 (by omega)).trans p5
  have q7 := (k2 _ 8 (by omega)).trans p15
  have qmm := (k2 _ 8 (by omega)).trans p4
  have hvn1 := hvS (vp.toNat + 8 * (vl.toNat - 1)) 8 (by omega) (by omega)
  have hquS : ∀ a n, (qp.toNat ≤ a ∧ a + n ≤ qp.toNat + 8 * ql.toNat) ∨ (up.toNat ≤ a ∧ a + n ≤ up.toNat + 8 * ul.toNat) →
      S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h
    have hqw := hl.qw; have huw := hl.uw
    have hfq := hpre.free.1; have hfu := hpre.free.2.1; have hsq := hpre.stq; have hsu := hpre.stu
    simp only [freeP, freeN] at hfq hfu
    unfold Apart at hfq hfu hsq hsu
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Held.readLE2 (hpre.qh.sub h1 h2) hF2 hLF2
        (by simp only [outside_cons, outside_nil, and_true]; omega)
        (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega), hPs a n (by omega)]
    · rw [Held.readLE2 (hpre.uh.sub h1 h2) hF2 hLF2
        (by simp only [outside_cons, outside_nil, and_true]; omega)
        (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega), hPs a n (by omega)]
  have hvtop := hpre.vtop
  have hvn1' : S2.mem.readLE (vp.toNat + 8 * (vl.toNat - 1)) 8 ≠ 0 := by rw [hvn1]; omega
  have hgS : S2.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    have hstg := hpre.stg; have hstgf := hpre.stgf
    simp only [freeP, freeN] at hstgf
    unfold Apart at hstg hstgf hga
    have ho : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 240 - stkSN, s.sp.toNat - 248),
        (s.sp.toNat - 232, s.sp.toNat - 240 + abSN)] ++ stkWs s.mem st.toNat) := by
      simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hgr, by omega, by omega⟩, by omega, by omega⟩
    rw [hF2.readLE _ _ ho, hPs _ _ (by omega)]
  have hS2acc : ∀ a n v, S2.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF2.accessible, hF.accessible]
  have hvacc := hpre.vacc
  have hvacc2 : S2.mem.accessible vp.toNat (8 * vl.toNat) false = true := by rw [hS2acc]; exact hvacc
  have hgacc : S2.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hS2acc]; exact hg2
  have hwacc : S2.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hS2acc]; exact hw
  have e240 : (s.sp - 240#64).toNat = s.sp.toNat - 240 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold Apart at hga
  have hvw := hl.vw
  have hvn1'' : S2.mem.readLE (vp.toNat + (vl.toNat - 1) * 8) 8 = s.mem.readLE (vp.toNat + 8 * (vl.toNat - 1)) 8 := by
    rw [← hvn1, Nat.mul_comm]
  janus_run [hr0, hr1, hr2, q8, qn1, q7, hvn1''] until [callRec + 4] calls [recip impl hap]
  rename_i hpc3 hsp3 hr03 h183 h283 h293 hFw
  generalize hMq : (((S2.mem.writeLE (s.sp.toNat - 104) 8 (vl.toNat + 1)).writeLE (s.sp.toNat - 112) 8
    (vl.toNat + 1)).writeLE (s.sp.toNat - 56) 8 (stW S2.mem st.toNat + 8 * stLen s.mem st.toNat)).writeLE
    (s.sp.toNat - 136) 8 (s.mem.readLE (vp.toNat + 8 * (vl.toNat - 1)) 8) = Mq at hFw
  have kq : ∀ a n, (a + n ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 128 ≤ a) → (a + n ≤ s.sp.toNat - 112 ∨ s.sp.toNat - 96 ≤ a) →
      (a + n ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 48 ≤ a) → Mq.readLE a n = S2.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have kw : ∀ a n, (a + n ≤ s.sp.toNat - 328 ∨ s.sp.toNat - 280 ≤ a) → s'.mem.readLE a n = Mq.readLE a n := by
    intro a n h
    exact hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hm88 : s'.mem.readLE (s.sp.toNat - 88) 8 = (ul.toNat + 2 ^ 64 - vl.toNat) % 2 ^ 64 := by
    rw [kw _ _ (by omega), kq _ _ (by omega) (by omega) (by omega), qmm]
  have hrl := FvModexp.AsmDivVW.recipWord_lt (s.mem.readLE (vp.toNat + 8 * (vl.toNat - 1)) 8) (by omega)
    (Memory.readLE_lt _ _ _)
  have hS'acc : ∀ a n v, s'.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hFw.accessible, ← hMq]; simp only [Memory.accessible_writeLE]; exact hS2acc a n v
  have hwacc' : s'.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hS'acc]; exact hw
  janus_run [hm88] until [head]
  generalize hrec : AsmDiv.recipWord (s.mem.readLE (vp.toNat + 8 * (vl.toNat - 1)) 8) = rc at *
  have kM : ∀ a n, (a + n ≤ s.sp.toNat - 128 ∨ s.sp.toNat - 120 ≤ a) →
      (s'.mem.writeLE (s.sp.toNat - 128) 8 rc).readLE a n = s'.mem.readLE a n :=
    fun a n h => Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have ks : ∀ a n, ((s.sp.toNat - 248 ≤ a ∧ a + n ≤ s.sp.toNat - 232) ∨ (s.sp.toNat - 144 ≤ a ∧ a + n ≤ s.sp.toNat - 136) ∨
      (s.sp.toNat - 96 ≤ a ∧ a + n ≤ s.sp.toNat - 56) ∨ (s.sp.toNat - 48 ≤ a ∧ a + n ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 88)) →
      (s'.mem.writeLE (s.sp.toNat - 128) 8 rc).readLE a n = P.mem.readLE a n := by
    intro a n h
    rw [kM a n (by omega), kw a n (by omega), kq a n (by omega) (by omega) (by omega), k2 a n (by omega)]
  -- the frame
  have hst : MemFrame S2.mem (s'.mem.writeLE (s.sp.toNat - 128) 8 rc)
      [(s.sp.toNat - 328, s.sp.toNat - 280), (s.sp.toNat - 136, s.sp.toNat - 96), (s.sp.toNat - 56, s.sp.toNat - 48)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      rw [kM a n (by omega), kw a n (by omega), kq a n (by omega) (by omega) (by omega)],
     fun a n v => by simp only [Memory.accessible_writeLE]; rw [hFw.accessible, ← hMq]; simp only [Memory.accessible_writeLE]⟩
  have hwst := hl.sw
  refine k _ _ _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE, ?mem⟩ ?qu
  case qu =>
    intro a n h
    have hqw := hl.qw; have huw := hl.uw
    have h' : a + n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 88 ≤ a := by omega
    rw [kM a n (by omega), kw a n (by omega), kq a n (by omega) (by omega) (by omega)]
    exact hquS a n h
  case mem =>
    refine ⟨(ks _ _ (by omega)).trans p1, (ks _ _ (by omega)).trans p2, (ks _ _ (by omega)).trans p3, ?vn, ?rw, ?hl,
      ?hc, (ks _ _ (by omega)).trans p4, ?tp, (ks _ _ (by omega)).trans p6, (ks _ _ (by omega)).trans p7,
      (ks _ _ (by omega)).trans p8, (ks _ _ (by omega)).trans p9, (ks _ _ (by omega)).trans p10,
      (ks _ _ (by omega)).trans p11, (ks _ _ (by omega)).trans p12, (ks _ _ (by omega)).trans p13,
      (ks _ _ (by omega)).trans p14, (ks _ _ (by omega)).trans p15, (ks _ _ (by omega)).trans p16,
      (ks _ _ (by omega)).trans p17, ?hw, ?hlen, ?hcap, ?vs, ?fr, ?lf, ?inv⟩
    case vn =>
      rw [kM _ _ (by omega), kw _ _ (by omega), ← hMq, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
    case rw => rw [Memory.readLE_writeLE_self, ← hrec, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    case hl =>
      rw [kM _ _ (by omega), kw _ _ (by omega), ← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    case hc =>
      rw [kM _ _ (by omega), kw _ _ (by omega), ← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    case tp =>
      rw [kM _ _ (by omega), kw _ _ (by omega), ← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := hl.t48; omega)
    case hw => rw [kM _ _ (by omega), kw _ _ (by omega), kq _ _ (by omega) (by omega) (by omega)]
    case hlen =>
      rw [kM _ _ (by omega), kw _ _ (by omega), kq _ _ (by omega) (by omega) (by omega)]; exact hlen2
    case hcap => rw [kM _ _ (by omega), kw _ _ (by omega), kq _ _ (by omega) (by omega) (by omega)]
    case vs =>
      intro a n h1 h2
      rw [kM a n (by omega), kw a n (by omega), kq a n (by omega) (by omega) (by omega)]
      exact hvS a n h1 h2
    case fr =>
      refine (mfTrans hF (mfTrans hF2 hst)).mono fun a n ho => ?_
      simp only [winA, stkWs, wsL, proWs, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
      obtain ⟨hrt, h1, h2, h3, h4, h5, h6, h7⟩ := ho
      refine ⟨?_, ?_, hrt, ?_, ?_, h6, h7, ?_, ?_, ?_⟩
      all_goals clear h3 h4 h5 h6 h7
      all_goals omega
    case lf =>
      refine ⟨fun a n hin hws => ?_⟩
      simp only [stkWs, wsL, outside_append, outside_cons, outside_nil, and_true] at hws
      obtain ⟨⟨h4, h5, h6⟩, h7, h8⟩ := hws
      have hw0 : a + n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 88 ≤ a := by
        obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; clear h4 h5 h6 h7 h8; omega
      rw [kM a n (by clear h4 h5 h6 h7 h8; omega), kw a n (by clear h4 h5 h6 h7 h8; omega),
        kq a n (by clear h4 h5 h6 h7 h8; omega) (by clear h4 h5 h6 h7 h8; omega) (by clear h4 h5 h6 h7 h8; omega),
        hLF2.readLE a n hin (by simp only [stkWs, outside_cons, outside_nil, and_true]; exact ⟨h7, h8⟩),
        hPs a n (by clear h4 h5 h6 h7 h8; omega)]
    case inv =>
      refine inv_store_out (RtInv.inv_frame' (ws := [(s.sp.toNat - 328, s.sp.toNat - 280)]) hFw ?_ ?_)
        (hout.of_sub (by omega) (by omega))
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; left; exact hout.of_sub (by omega) (by omega)
      · rw [← hMq]
        refine inv_store_out (inv_store_out (inv_store_out (inv_store_out hinv2 ?_) ?_) ?_) ?_ <;>
          exact hout.of_sub (by omega) (by omega)
  all_goals janus_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; try omega)

end FvModexp.Arm64.DivBasic
