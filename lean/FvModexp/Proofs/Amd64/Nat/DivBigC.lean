import FvModexp.Proofs.Amd64.Nat.DivBigP
import FvModexp.Proofs.Amd64.Nat.DivBigF
import FvModexp.Proofs.Amd64.Nat.DivOneF

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u ≥ v`: the `divLarge` call (premise `DivLarge.Hyp`), the results stored, return

After the call (`retL = fn + 0x41d`): `q` (`RAX, RBX, RCX`) stored at `RSP - 56 … - 40`, `r` (`RDI, RSI, R8`) at
`RSP - 80 … - 64`; the defer bit `[RSP - 122]` (= 0) tested; reloads; `ADDQ $0xe0, SP; POPQ BP; RET`.
Port of `Arm64/Nat/DivBigC.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- after `divLarge` returned: results stored, the (unset) defer bit tested, return -/
theorem big3 (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s)
    {X : State} (hsp : X.regs 4 = s.regs 4 - 240#64) (h14 : X.regs 14 = s.regs 14)
    (hF : MemFrame s.mem X.mem (win s 41512 112))
    {q ql qc r rl rc : Nat} {L' : List (Nat × Nat)} {b'' : Nat} {T : State}
    (hq : ExpHyp.NatOF R L L' T.mem zp zc 1 q ql qc (natVal X.mem u ul / natVal X.mem v vl))
    (hr : ExpHyp.NatOF R L L' T.mem z2 z2c 1 r rl rc (natVal X.mem u ul % natVal X.mem v vl))
    (hrt : EvenHyp.RtPost R b (DivLarge.cost dc (stLen X.mem st) ul vl) L L' b'' X T)
    (hsb : StackBackL R L L' st X.mem T.mem)
    (hfr : ¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap T.mem st →
      Apart r (8 * rc) (stW T.mem st) (8 * stCap T.mem st))
    (hmf : MemFrame X.mem T.mem (R.rt ++ win X 41272 112 ++ (ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (hlf : LiveFrame X.mem T.mem L ((ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (hpcT : T.rip = BitVec.ofNat 64 retL) (hspT : T.regs 4 = s.regs 4 - 232#64) (h5T : T.regs 5 = s.regs 4 - 8#64)
    (h14T : T.regs 14 = s.regs 14) (hfsT : T.fsBase = s.fsBase) (hx15T : T.xmm 15 = 0#128) (hdfT : T.df = false)
    (e0 : T.regs 0 = BitVec.ofNat 64 q) (e1 : T.regs 3 = BitVec.ofNat 64 ql) (e2 : T.regs 1 = BitVec.ofNat 64 qc)
    (e3 : T.regs 7 = BitVec.ofNat 64 r) (e4 : T.regs 6 = BitVec.ofNat 64 rl) (e5 : T.regs 8 = BitVec.ofNat 64 rc)
    (m0 : T.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (m1 : T.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m3 : T.mem.readLE ((s.regs 4).toNat - 122) 1 = 0)
    (hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) T (RQ R b dc L zp zc st z2 z2c u ul v vl s) := by
  have hp := hpre.f
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hB : Box (Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) := ⟨hpre⟩
  have hB2 := Box.mk (And.intro hq (And.intro hr (And.intro hrt (And.intro hsb (And.intro hfr (And.intro hmf hlf))))))
  clear hpre hp hmf hlf hq hr hrt hsb hfr
  janus64_run [m0, m1, m3, e0, e1, e2, e3, e4, e5]
  obtain ⟨hpre⟩ := hB
  obtain ⟨hq, hr, hrt, hsb, hfr, hmf, hlf⟩ := hB2.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, bigFin hpre hsp h14 hF hq hr hrt hsb hfr hmf hlf _ ?_ ?_ (by janus_frame) ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hx15T.trans hx0.symm
    | exact hfsT
    | exact hdfT.trans hdf0.symm
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)
   

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `divLarge`'s entry: the call (summary `lsum`), then `big3` -/
theorem big2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl)
    (X : State) (hX : AtL zp zl zc st z2 z2l z2c u ul uc v vl vc s X)
    (hzp : zp < 2 ^ 64) (hz2 : z2 < 2 ^ 64)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) X (RQ R b dc L zp zc st z2 z2c u ul v vl s) := by
  have hp := hpre.f
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hspn := sp240 hX.sp (by omega)
  have hF := hX.mf
  have hz40 := hp.zo.1; have hz240 := hp.z2o.1; have hul := hp.ul9; have hvl := hp.vl9
  have hu48 := hp.uo.2.2.1; have hv48 := hp.vo.2.2.1
  have hst48 := hp.sok.2.2.2.1
  have hsum := lsum impl hap R dc hL b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 z2) (BitVec.ofNat 64 z2l) (BitVec.ofNat 64 z2c) u ul v vl
  have ezp := tN64 hzp; have ezc := tN64 (n := zc) (by omega); have est := tN64 (n := st) (by omega)
  have ez2 := tN64 hz2; have ez2c := tN64 (n := z2c) (by omega)
  have hra' : RetAddr ((Extracted.program.onlySegments DivLarge.names).link impl)
      (X.mem.readLE (X.regs 4).toNat 8) := by
    rw [hspn, hX.rc]
    have := raD hap (ns := DivLarge.names) (by decide) 0x41d (by decide)
    rw [segA] at this; exact this
  refine ReachesRet.call_regions hsum (by rw [divLE_eq]; exact hX.pc)
    ⟨hra', hX.x15, ?args, hX.df, ?pre⟩ (fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_)
  case args =>
    show X.regs 0 = _ ∧ X.regs 3 = _ ∧ X.regs 1 = _ ∧ X.regs 7 = _ ∧ X.regs 6 = _ ∧ X.regs 8 = _ ∧
      X.regs 9 = _ ∧ True
    exact ⟨hX.a0, hX.a3, hX.a1, hX.a7, hX.a6, hX.a8, hX.a9, trivial⟩
  case pre =>
    rw [ezp, ezc, est, ez2, ez2c]
    exact l_pre hpre hge hv2 X hX
  rw [ezp, ezc, est, ez2, ez2c] at hq
  obtain ⟨hfs, hdf, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b'', hq', hr', hrt, hsb, hfr, hmf, hlf⟩ := hq
  have hk := slots_keep hpre hX.sp hF hmf
  have m0 : T.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hk _ _ ⟨by omega, by omega⟩]; exact hX.ra
  have m1 : T.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hk _ _ ⟨by omega, by omega⟩]; exact hX.bp
  have m3 : T.mem.readLE ((s.regs 4).toNat - 122) 1 = 0 := by
    rw [hk _ _ ⟨by omega, by omega⟩]; exact hX.by0
  have hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hmf.accessible, hF.accessible]; exact hw
  exact big3 impl hpre hX.sp hX.r14 hF hq' hr' hrt hsb hfr hmf hlf
    (by rw [hT, retAddrOf, hspn, hX.rc]) (by rw [f4, hX.sp]; bv_omega) (by rw [f5, hX.r5]) (by rw [f14, hX.r14])
    (by rw [hfs, hX.fs]) (by rw [f15, hX.x15]) (by rw [hdf, hX.df]) e0 e1 e2 e3 e4 e5 m0 m1 m3 hTacc hra hx0 hdf0

end FvModexp.Amd64.NatDiv
