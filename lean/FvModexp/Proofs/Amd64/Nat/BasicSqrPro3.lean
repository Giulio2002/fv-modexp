import FvModexp.Proofs.Amd64.Nat.BasicSqrEnv
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Common.DivmcMem

set_option autoImplicit false

/-!
# `basicSqr` (amd64): after `t := stk.nat(2n)` returned — the spills of `t`, up to `clear(t)` (natmul.go:121-122;
the amd64 twin of `Arm64/Nat/BasicSqrPro.lean`'s `pro3`)

At the return address `+0xbe` (`RSP' = RSP - 192`): `MOVQ BX, 0x68(SP)` (`RSP - 88`, len), `MOVQ AX, 0x90(SP)`
(`RSP - 48`, ptr), `MOVQ CX, 0x70(SP)` (`RSP - 80`, cap), `TESTQ BX, BX; JE` (`2n ≠ 0`), `BX = 8·BX`, then the
`CALL runtime.memclrNoHeapPointers` (`clr`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.BasicSqr

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0xb9

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s P : State) : Prop where
  pc : P.rip = BitVec.ofNat 64 callNat
  sp : P.regs 4 = s.regs 4 - 192#64
  r5 : P.regs 5 = s.regs 4 - 8#64
  r14 : P.regs 14 = s.regs 14
  fs : P.fsBase = s.fsBase
  x15 : P.xmm 15 = 0#128
  df : P.df = false
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r3 : P.regs 3 = BitVec.ofNat 64 (2 * xl)
  fr : MemFrame s.mem P.mem [((s.regs 4).toNat - 89, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 40, (s.regs 4).toNat),
    ((s.regs 4).toNat + 16, (s.regs 4).toNat + 64)]
  reg : P.mem.regions = s.mem.regions
  bp : P.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dfn : P.mem.readLE ((s.regs 4).toNat - 40) 8 = segAddr LibBasicSqr.program (fn ++ ".deferwrap1")
  dst : P.mem.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : P.mem.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  s1 : P.mem.readLE ((s.regs 4).toNat + 16) 8 = zp
  s2 : P.mem.readLE ((s.regs 4).toNat + 24) 8 = zl
  s3 : P.mem.readLE ((s.regs 4).toNat + 32) 8 = zc
  s4 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = xp
  s5 : P.mem.readLE ((s.regs 4).toNat + 48) 8 = xl
  s6 : P.mem.readLE ((s.regs 4).toNat + 56) 8 = xc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- after `(*stack).nat` returned (state `S2`): the three result spills, up to `clear(t)` -/
theorem pro3 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hclr : ClrK impl R b L st zp zl zc xp xl xc s)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15s : s.xmm 15 = 0#128) (hdfs : s.df = false)
    (P : State) (hP : AtNat R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s P)
    (S2 : State) (hpc2 : S2.rip = BitVec.ofNat 64 (callNat + 5)) (hsp2 : S2.regs 4 = s.regs 4 - 192#64)
    (h5 : S2.regs 5 = s.regs 4 - 8#64) (h14 : S2.regs 14 = s.regs 14) (hfs2 : S2.fsBase = s.fsBase)
    (hx152 : S2.xmm 15 = 0#128) (hdf2 : S2.df = false)
    (hr0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st.toNat + 8 * stLen s.mem st.toNat))
    (hr3 : S2.regs 3 = BitVec.ofNat 64 (2 * xl.toNat)) (hr1 : S2.regs 1 = BitVec.ofNat 64 (2 * xl.toNat))
    (L1 : List (Nat × Nat)) (b1 : Nat) (hext : LiveExt R L L1)
    (hbud : b - stackNatCost (stLen s.mem st.toNat) (2 * xl.toNat) ≤ b1)
    (hinv2 : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S2.mem)) (hok : StkOK S2.mem R L1 st.toNat)
    (hlen2 : stLen S2.mem st.toNat = stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4)
    (hsame : stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4 ≤ stCap s.mem st.toNat →
      stW S2.mem st.toNat = stW s.mem st.toNat ∧ stCap S2.mem st.toNat = stCap s.mem st.toNat)
    (hgrow : stCap s.mem st.toNat < stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4 →
      InRanges (stW S2.mem st.toNat) (8 * stCap S2.mem st.toNat) R.rt ∧
        ApartAll (stW S2.mem st.toNat) (8 * stCap S2.mem st.toNat) L)
    (hmem : stCap s.mem st.toNat < stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4 →
      (stW S2.mem st.toNat, stW S2.mem st.toNat + 8 * stCap S2.mem st.toNat) ∈ L1)
    (hF2 : MemFrame (P.mem.writeLE ((s.regs 4).toNat - 200) 8 6231390) S2.mem
      (R.rt ++ [((s.regs 4).toNat - 200 - 4192, (s.regs 4).toNat - 200 + 24)] ++ stkWs s.mem st.toNat))
    (hLF2 : LiveFrame (P.mem.writeLE ((s.regs 4).toNat - 200) 8 6231390) S2.mem L (stkWs s.mem st.toNat)) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) S2 fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hF, -, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := hP
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, hga, -, hLs, -, ⟨-, -, htg⟩, htrt, htw⟩ := hpre.ce
  simp only [regSP, regG] at hb' ha hw htg
  unfold Apart at htw
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hfw := hpre.stfw; simp only [win, outside_cons, outside_nil, and_true, freeP, freeN] at hfw
  have hlc := hpre.stok.2.2.2.2.2.1
  have hst48 := hpre.stok.2.2.2.1
  have hPs : ∀ a n, (a + n ≤ (s.regs 4).toNat - 89 ∨ (s.regs 4).toNat + 64 ≤ a) →
      P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hE := env_of (P := P.mem) (S2 := S2.mem) hpre hbig (fun k hk => hPs _ _ (by omega))
    (fun a n v => hF.accessible a n v) hext
    (by simp only [stLen] at hbud ⊢; rw [hPs _ _ (by omega)]; exact hbud) hok
    (by simp only [stLen] at hlen2 ⊢; rw [hlen2, hPs _ _ (by omega)])
    (by simp only [stLen, stW, stCap] at hsame ⊢
        rw [hPs (st.toNat + 8) _ (by omega), hPs (st.toNat + 16) _ (by omega), hPs st.toNat _ (by omega)]; exact hsame)
    (by simp only [stLen, stW, stCap] at hgrow ⊢
        rw [hPs (st.toNat + 8) _ (by omega), hPs (st.toNat + 16) _ (by omega)]; exact hgrow)
    (fun a n v => by rw [hF2.accessible, Janus.Arm64.Memory.accessible_writeLE])
    (by simp only [stLen, stW, stCap] at hmem ⊢
        rw [hPs (st.toNat + 8) _ (by omega), hPs (st.toNat + 16) _ (by omega)]; exact hmem) hx15s hdfs hra
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hx0 := hl.x0
  -- reads of `S2.mem` in the frame record
  have k2 : ∀ a, (s.regs 4).toNat - 176 ≤ a → a + 8 ≤ (s.regs 4).toNat + 64 →
      S2.mem.readLE a 8 = P.mem.readLE a 8 := by
    intro a h1 h2
    rw [hF2.readLE _ _ ?_, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega, by omega⟩
  have hr3' : (S2.regs 3).toNat = 2 * xl.toNat := by
    rw [hr3]; simp only [BitVec.toNat_ofNat]; have := hpre.stlen; omega
  have hnz : S2.regs 3 ≠ 0#64 := by intro h; rw [h] at hr3'; simp at hr3'; omega
  have ht48 := hE.scr.b48
  have hsh : BitVec.ofNat 64 (2 * xl.toNat) <<< 3 = BitVec.ofNat 64 (16 * xl.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
    have := hpre.stlen; omega
  have hPo : ∀ a n, Outside a n [((s.regs 4).toNat - 89, (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 40, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 64)] →
      P.mem.readLE a n = s.mem.readLE a n := fun a n h => hF.readLE _ _ h
  janus64_run [hr0, hr1, hr3] until [callClr]
  generalize hMq : ((S2.mem.writeLE ((s.regs 4).toNat - 88) 8 (2 * xl.toNat)).writeLE ((s.regs 4).toNat - 48) 8
      (stW S2.mem st.toNat + 8 * stLen s.mem st.toNat)).writeLE ((s.regs 4).toNat - 80) 8 (2 * xl.toNat) = Mq
  have kq : ∀ a n, (a + n ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat - 72 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 40 ≤ a) → Mq.readLE a n = S2.mem.readLE a n := by
    intro a n h1 h2
    rw [← hMq, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hst : MemFrame S2.mem Mq [((s.regs 4).toNat - 88, (s.regs 4).toNat - 72),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)] :=
    ⟨fun a n h => by simp only [outside_cons, outside_nil, and_true] at h; exact kq a n h.1 h.2,
     fun a n v => by rw [← hMq]; simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
  have hW : MemFrame P.mem (P.mem.writeLE ((s.regs 4).toNat - 200) 8 6231390)
      [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
     fun a n v => by simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
  have ks : ∀ a, ((s.regs 4).toNat - 72 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 48 ∨
      (s.regs 4).toNat - 40 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → Mq.readLE a 8 = P.mem.readLE a 8 :=
    fun a ha => by rw [kq a 8 (by omega) (by omega), k2 a (by omega) (by omega)]
  have kst : ∀ k, k + 8 ≤ 24 → Mq.readLE (st.toNat + k) 8 = S2.mem.readLE (st.toNat + k) 8 :=
    fun k hk => kq _ _ (by omega) (by omega)
  have hstt := hpre.stt; have hstft := hpre.stft
  simp only [freeP, freeN, stW, stLen, stCap] at hstft
  unfold Apart at hstt hstft
  have hfs8 := hl.fs
  simp only [stLen, stCap] at hlc
  refine hclr _ L1 b1 _ _ hE _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?r0 ?r3
    ⟨?ra, (ks _ (by omega)).trans p1, ?tl, ?tc, ?tp, (ks _ (by omega)).trans p2, (ks _ (by omega)).trans p3,
      (ks _ (by omega)).trans p4, (ks _ (by omega)).trans p5, (ks _ (by omega)).trans p6, (ks _ (by omega)).trans p7,
      (ks _ (by omega)).trans p8, (ks _ (by omega)).trans p9, (ks _ (by omega)).trans p10,
      (ks _ (by omega)).trans p11, kst 0 (by omega), (kst 8 (by omega)).trans hlen2, kst 16 (by omega), ?tls, ?xs, ?fr,
      ?lf, ?inv⟩
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hr0]
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsh]
  case ra =>
    rw [ks _ (by omega), hPo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  case tl =>
    rw [← hMq, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case tc => rw [← hMq, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  case tp =>
    rw [← hMq, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case tls =>
    rw [kq _ _ (by omega) (by omega), hF2.readLE _ _ ?_, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hPo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), htg]
    simp only [stkWs, stW, stLen, stCap, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨htrt, by omega⟩, by omega, by omega⟩
  case xs =>
    intro a n h1 h2
    have hxw := hl.xw
    have hfr := hpre.free.2; have hsx := hpre.stx
    simp only [freeP, freeN] at hfr
    unfold Apart at hfr hsx
    rw [kq a n (by omega) (by omega), Held.readLE2 (hpre.xh.sub h1 h2) hF2 hLF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hPo a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
  case fr =>
    refine (mfTrans hF (mfTrans hW (mfTrans hF2 hst))).mono fun a n ho => ?_
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨⟨hrt, hw1⟩, hz, ht⟩, h6, h7⟩ := ho
    refine ⟨⟨by omega, by omega, by omega⟩, by omega, ⟨⟨hrt, by omega⟩, h6, h7⟩, by omega, by omega⟩
  case lf =>
    refine ⟨fun a n hin hws => ?_⟩
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at hws
    obtain ⟨⟨h4, h5⟩, h6, h7⟩ := hws
    have hw0 : a + n ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 64 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; clear h4 h5 h6 h7; omega
    rw [kq a n (by clear h4 h5 h6 h7; omega) (by clear h4 h5 h6 h7; omega),
      hLF2.readLE a n hin (by simp only [stkWs, outside_cons, outside_nil, and_true]; exact ⟨h6, h7⟩),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by clear h4 h5 h6 h7; omega),
      hPo a n (by simp only [outside_cons, outside_nil, and_true]; clear h4 h5 h6 h7; omega)]
  case inv =>
    rw [← hMq]
    refine inv_store_out (inv_store_out (inv_store_out hinv2 ?_) ?_) ?_ <;> exact hout.of_sub (by omega) (by omega)
  all_goals first | rfl | exact hfs2 | exact hx152 | janus64_simp

end FvModexp.Amd64.BasicSqr
