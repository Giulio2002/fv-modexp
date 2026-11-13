import FvModexp.Proofs.Amd64.NatQ.RemNatC

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): `_, r = q.div(stk, z, u, v)` — from `stk.nat`'s return to `div`'s return
(twin of Arm64/NatQ/RemDivC.lean; divmc s58)

`T` at `0x5edd9e` (`RSP = r - 200`): the stack arguments `u`, `v` are copied to `r-200 … r-160`, `DI = stk`,
`SI, R8, R9 = z`, `AX, BX, CX = q` (`stk.nat`'s result), `CALL nat.div` (premise `ExpHyp.DivHypLQ` as a `LibRem` summary).
The callee's precondition is a premise `hX` (proved by `dv_pre`, RemDvPre).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

variable {H : Nat}

/-- the entry of `nat.div` -/
abbrev divR : Nat := 0x5edf20

theorem div_entryR : segAddr Extracted.program ExpHyp.fnDiv = divR := by decide

/-- `nat.div` (premise `DivHypLQ`) as a summary in `LibRem.program` -/
theorem remDivSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {cd : Nat → Nat → Nat} (hD : ExpHyp.DivHypLQ impl R LibDiv.names 41512 112 cd)
    (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) :
    Summary (LibRem.program.link impl) divR
      (fun s => RetAddr ((Extracted.program.onlySegments LibDiv.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [z, zl, zc, st, z2, z2l, z2c] ∧ s.df = false ∧
        ExpHyp.DivPreQ R b H (cd ul vl + stkR H s.mem st.toNat) L 41512 112 z.toNat zl.toNat zc.toNat st.toNat
          z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        ExpHyp.DivPostLQ R b (cd ul vl + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L 41512 112
          z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s') := by
  have hS := Ensures.toSummaryIn (hD H b L z zl zc st z2 z2l z2c u ul uc v vl vc) (A64.noExit_restrict64 hap LibDiv.names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap (IntAS.sub_of_all (ms := LibRem.names) (by decide)))
  rw [← LibRem.eq_only, div_entryR] at hS
  exact hS

/-- the callee-entry facts at `CALL nat.div` (`X` = `T` after the stack-argument stores and the push) -/
structure AtDiv (s T X : State) (up ul uc vp vl vc : Nat) : Prop where
  sp : X.regs 4 = s.regs 4 - 208#64
  r14 : X.regs 14 = T.regs 14
  fs : X.fsBase = T.fsBase
  reg : X.mem.regions = T.mem.regions
  mf : MemFrame T.mem X.mem [((s.regs 4).toNat - 208, (s.regs 4).toNat - 208 + 48 + 8)]
  ra : X.mem.readLE ((s.regs 4).toNat - 208) 8 = callDiv + 5
  a1 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = up
  a2 : X.mem.readLE ((s.regs 4).toNat - 192) 8 = ul
  a3 : X.mem.readLE ((s.regs 4).toNat - 184) 8 = uc
  a4 : X.mem.readLE ((s.regs 4).toNat - 176) 8 = vp
  a5 : X.mem.readLE ((s.regs 4).toNat - 168) 8 = vl
  a6 : X.mem.readLE ((s.regs 4).toNat - 160) 8 = vc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`CALL nat.div`** from `stk.nat`'s return `T` (`RSP = r - 200`); the callee's precondition is the premise `hX`,
the continuation gets `div`'s return state `U` at `0x5ede0a` -/
theorem divc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {cd : Nat → Nat → Nat} (hD : ExpHyp.DivHypLQ impl R LibDiv.names 41512 112 cd) (H b : Nat) (L : List (Nat × Nat))
    (s T : State) (zp zl zc st up ul uc vp vl vc q k : Nat)
    (hbd : q < 2 ^ 64 ∧ k < 2 ^ 64 ∧ st < 2 ^ 64 ∧ zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64)
    (hpc : T.rip = BitVec.ofNat 64 (callNat + 5)) (hsp : T.regs 4 = s.regs 4 - 200#64)
    (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (q0 : T.regs 0 = BitVec.ofNat 64 q) (q1 : T.regs 3 = BitVec.ofNat 64 k) (q2 : T.regs 1 = BitVec.ofNat 64 k)
    (hsl : Sl s zp zl zc st up ul uc T.mem)
    (hv1 : T.mem.readLE ((s.regs 4).toNat + 8) 8 = vp) (hv2 : T.mem.readLE ((s.regs 4).toNat + 16) 8 = vl)
    (hv3 : T.mem.readLE ((s.regs 4).toNat + 24) 8 = vc)
    (hb : 41720 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (hw : T.mem.accessible ((s.regs 4).toNat - 41720) (41720 + 112) true = true)
    {ret : W64} {Q : State → Prop}
    (hX : ∀ X : State, AtDiv s T X up ul uc vp vl vc →
      ExpHyp.DivPreQ R b H (cd ul vl + stkR H X.mem st) L 41512 112 q k k st zp zl zc up ul uc vp vl vc X)
    (kk : ∀ U X : State, AtDiv s T X up ul uc vp vl vc →
      U.rip = BitVec.ofNat 64 (callDiv + 5) → U.regs 4 = s.regs 4 - 200#64 → U.regs 5 = T.regs 5 →
      U.regs 14 = T.regs 14 → U.xmm 15 = T.xmm 15 → U.mem.regions = T.mem.regions →
      ExpHyp.DivPostLQ R b (cd ul vl + stkR H X.mem st) (stkR H U.mem st) L 41512 112 q k st zp zc up ul vp vl X U →
        ReachesRet (LibRem.program.link impl) ret U Q) :
    ReachesRet (LibRem.program.link impl) ret T Q := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hbd
  have m1 := hsl.s1; have m2 := hsl.s2; have m3 := hsl.s3; have m4 := hsl.s4
  have m5 := hsl.zp'; have m6 := hsl.zl'; have m7 := hsl.zc'
  have hspN : (T.regs 4).toNat = (s.regs 4).toNat - 200 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hspX : (s.regs 4 - 208#64).toNat = (s.regs 4).toNat - 208 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have bu : up < 2 ^ 64 := m2 ▸ readLE_lt_8 _ _
  have bul : ul < 2 ^ 64 := m3 ▸ readLE_lt_8 _ _
  have buc : uc < 2 ^ 64 := m4 ▸ readLE_lt_8 _ _
  have bvp : vp < 2 ^ 64 := hv1 ▸ readLE_lt_8 _ _
  have bvl : vl < 2 ^ 64 := hv2 ▸ readLE_lt_8 _ _
  have bvc : vc < 2 ^ 64 := hv3 ▸ readLE_lt_8 _ _
  clear hsl
  janus64_run [m1, m2, m3, m4, m5, m6, m7, hv1, hv2, hv3] until [divR]
  have hM : ∀ X : State, X.mem = ((((((Janus.Arm64.Memory.writeLE T.mem ((s.regs 4).toNat - 200) 8 up).writeLE
        ((s.regs 4).toNat - 192) 8 ul).writeLE ((s.regs 4).toNat - 184) 8 uc).writeLE ((s.regs 4).toNat - 176) 8 vp).writeLE
        ((s.regs 4).toNat - 168) 8 vl).writeLE ((s.regs 4).toNat - 160) 8 vc).writeLE ((s.regs 4).toNat - 208) 8 6217226 →
      X.regs 4 = s.regs 4 - 208#64 → X.regs 14 = T.regs 14 → X.regs 5 = T.regs 5 → X.fsBase = T.fsBase →
      X.df = false → X.xmm 15 = 0 → X.rip = BitVec.ofNat 64 divR →
      ArgsFrom64 X 0 [BitVec.ofNat 64 q, BitVec.ofNat 64 k, BitVec.ofNat 64 k, BitVec.ofNat 64 st, BitVec.ofNat 64 zp,
        BitVec.ofNat 64 zl, BitVec.ofNat 64 zc] →
      ReachesRet (LibRem.program.link impl) ret X Q := by
    intro X eM e4 e14 e5 efs edf ex15 erip hargs
    have hAt : AtDiv s T X up ul uc vp vl vc := by
      refine ⟨e4, e14, efs, by rw [eM]; simp only [Janus.Arm64.Memory.regions_writeLE], by rw [eM]; janus_frame,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [eM]; janus64_simp) <;> omega
    refine ReachesRet.call_regions (remDivSum impl hap R hD H b L (BitVec.ofNat 64 q) (BitVec.ofNat 64 k)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 st) (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
      up ul uc vp vl vc) erip ⟨?ra, ?x15, hargs, edf, ?pre⟩ fun U hr hq hUreg => ?_
    case ra =>
      simp only [regSP]; rw [e4, hspX, hAt.ra]; exact rem_ra hap (by decide) 0x16a (by decide)
    case x15 => exact ex15
    case pre =>
      rw [tN64 b0, tN64 b1, tN64 b2, tN64 b3, tN64 b4, tN64 b5]
      exact hX X hAt
    obtain ⟨⟨k4, k5, k14, k15⟩, hpost⟩ := hq
    simp only [tN64 b0, tN64 b1, tN64 b2, tN64 b3, tN64 b5] at hpost
    refine kk U X hAt ?_ ?_ (by rw [k5, e5]) (by rw [k14, e14]) (by rw [k15, ex15, hx15]) (by rw [hUreg, hAt.reg]) hpost
    · rw [hr, retAddrOf_eq, e4, hspX, hAt.ra]
    · rw [k4, e4]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hspX, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]; rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega
  exact hM _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl (by first | rfl | exact hdf) (by exact hx15) rfl
    (by simp [ArgsFrom64, argReg, intArgRegs, setRegF, q0, q1, q2])

end FvModexp.Amd64.Q.NatRem
