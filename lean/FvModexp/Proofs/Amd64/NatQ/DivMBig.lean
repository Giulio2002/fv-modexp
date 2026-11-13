import FvModexp.Proofs.Amd64.NatQ.DivMBigPost
import FvModexp.Proofs.Amd64.NatQ.DivMLPre
import FvModexp.Proofs.Amd64.NatQ.DivBigC

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, `z = nil`, `z2 = u`, `u ≥ v`: the `divLarge` call, the deferred `stk.free()`, return (top s42)

Twin of Arm64/NatQ/DivMBig.lean. `bigCallM`: from `divLarge`'s entry `X` (after `getStack()` and the defer record,
`joinM`): the call (premise `DivLarge.HypG`, summary `lsumG`, precondition `l_preM`), the result stores and the closure
call (`epiCM`), the closure `nat.div.deferwrap1` (`dsumM`, pre `freePreM`), the reloads and the return (`epiRM`); the
postcondition `RQM` (`postBigM`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 100000 in
theorem st3 {t st : Nat} (hb : 41512 ≤ t) (h : t - 41512 + (41512 + 112) ≤ st ∨ st + 24 ≤ t - 41512) :
    Outside st 24 [(t - 240, t - 232), (t - 80, t - 32), (t - 121, t - 120)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem sp232 (x : BitVec 64) (h : 240 ≤ x.toNat) : x - 240#64 + 8#64 = x - 232#64 := by bv_omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bigCallM (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    {b : Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl vc s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl) (hu64 : u < 2 ^ 64)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {L1 : List (Nat × Nat)} {b1 st : Nat} (X : State) (hN : NewStk R L L1 b b1 (s.regs 14).toNat X.mem st)
    (hF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112)) (hLF : LiveFrame s.mem X.mem L [])
    (hreg : X.mem.regions = s.mem.regions)
    (hpc : X.rip = BitVec.ofNat 64 divLE) (hsp : X.regs 4 = s.regs 4 - 240#64) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hx15 : X.xmm 15 = 0#128) (hdfX : X.df = false)
    (ha0 : X.regs 0 = BitVec.ofNat 64 0) (ha3 : X.regs 3 = BitVec.ofNat 64 0) (ha1 : X.regs 1 = BitVec.ofNat 64 0)
    (ha7 : X.regs 7 = BitVec.ofNat 64 st) (ha6 : X.regs 6 = BitVec.ofNat 64 u)
    (ha8 : X.regs 8 = BitVec.ofNat 64 ul) (ha9 : X.regs 9 = BitVec.ofNat 64 uc)
    (mrc : X.mem.readLE ((s.regs 4).toNat - 240) 8 = retL)
    (mra : X.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : X.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (mfl : X.mem.readLE ((s.regs 4).toNat - 122) 1 = 1) (mdw : X.mem.readLE ((s.regs 4).toNat - 32) 8 = dwM)
    (mst : X.mem.readLE ((s.regs 4).toNat - 24) 8 = st)
    (mdp : X.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32)
    (i0 : X.mem.readLE ((s.regs 4).toNat - 232) 8 = u) (i1 : X.mem.readLE ((s.regs 4).toNat - 224) 8 = ul)
    (i3 : X.mem.readLE ((s.regs 4).toNat - 208) 8 = v) (i4 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = vl) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) X (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal hga
  have hwO : Outside ((s.regs 4).toNat - 41512) (41512 + 112) R.rt := hout
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hul := hp.ul9; have hvl := hp.vl9
  have hu40 := hp.uo.1
  have hst48 := hN.2.2.2.2.1
  have hsum := lsumG impl hap R dc hL (16 * ul + 64) b1 L1 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 st) (BitVec.ofNat 64 u) (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) u ul v vl
  have e00 := tN64 (n := 0) (by decide); have est := tN64 (n := st) (by omega); have eu := tN64 hu64
  have euc := tN64 (n := uc) (by omega)
  have hra' : RetAddr ((Extracted.program.onlySegments DivLarge.names).link impl)
      (X.mem.readLE (X.regs 4).toNat 8) := by
    rw [hspn, mrc]
    have := raD hap (ns := DivLarge.names) (by decide) 0x41d (by decide)
    rw [segA] at this; exact this
  refine ReachesRet.call_regions hsum (by rw [divLE_eq]; exact hpc)
    ⟨hra', hx15, ?args, hdfX, ?pre⟩ (fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_)
  case args =>
    show X.regs 0 = _ ∧ X.regs 3 = _ ∧ X.regs 1 = _ ∧ X.regs 7 = _ ∧ X.regs 6 = _ ∧ X.regs 8 = _ ∧
      X.regs 9 = _ ∧ True
    exact ⟨ha0, ha3, ha1, ha7, ha6, ha8, ha9, trivial⟩
  case pre =>
    rw [e00, est, eu, euc]
    exact l_preM hp X hN hF hLF hreg hge hv2 hsp h14 hfs i0 i1 i3 i4
  rw [e00, est, eu, euc] at hq
  clear e00 est eu euc hsum hra'
  obtain ⟨hfsT, hdfT, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L2, b'', -, hr', ⟨hx, hbb, hinvT⟩, hsb, hfr,
    hmf, hlf, -, -⟩ := hq
  have hbbB : Box (b1 - (DivLarge.costQ dc ul vl + stkR (16 * ul + 64) X.mem st) + stkR (16 * ul + 64) T.mem st ≤ b'') :=
    ⟨hbb⟩
  clear hbb
  -- the stack facts used below
  have hl0 : stLen X.mem st = 0 := hN.2.2.2.2.2.2.1
  have hmH : (st, st + 24) ∈ L1 := by rw [hN.1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hmA : 0 < stCap X.mem st → (stW X.mem st, stW X.mem st + 8 * stCap X.mem st) ∈ L1 := fun hc => by
    rw [hN.1]; refine List.mem_append_right _ ?_
    simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, true_or, or_true]
  have hok1 : StkOK T.mem R L2 st := hsb.1.1
  have hl1 : stLen T.mem st = 0 := hsb.1.2.1.trans hl0
  have hc01 : stCap T.mem st = 0 → stW T.mem st = 0 := hsb.2.cap0 hN.2.2.2.2.2.2.2.2.1
  have hdis1 : 0 < stCap T.mem st → Apart st 24 (stW T.mem st) (8 * stCap T.mem st) := fun hc => by
    rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨-, hap'⟩
    · rw [ew, ec]; exact hN.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have := hap' _ hmH; simp only [Nat.add_sub_cancel_left] at this; exact this.symm
  have hrs1 : ∀ x ∈ stkRs T.mem st, x ∈ L2 := stkRs_forall (hx.mem_old hmH) fun hc => by
    by_cases hk' : stW T.mem st = stW X.mem st ∧ stCap T.mem st = stCap X.mem st
    · rw [hk'.1, hk'.2]; exact hx.mem_old (hmA (by rw [← hk'.2]; exact hc))
    · exact hsb.2.mem hk'
  have hB : Box (ExpHyp.NatOF R L1 L2 T.mem u uc 1 r rl rc (natVal X.mem u ul % natVal X.mem v vl) ∧
      StackBackL R L1 L2 st X.mem T.mem) := ⟨⟨hr', hsb⟩⟩
  clear hr' hsb
  have hKb : Box (T.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
      T.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ T.mem.readLE ((s.regs 4).toNat - 122) 1 = 1 ∧
      T.mem.readLE ((s.regs 4).toNat - 32) 8 = dwM ∧ T.mem.readLE ((s.regs 4).toNat - 24) 8 = st ∧
      T.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32) :=
    ⟨slots6 (u := u) (uc := uc) hN hb' hwO (fun hc => (hp.uo.2.2 hc).1) hsp hmf mra mbp mfl mdw mst mdp⟩
  clear mra mbp mfl mdw mst mdp
  have hpcT : T.rip = BitVec.ofNat 64 retL := by rw [hT, retAddrOf, hspn, mrc]
  clear hspn
  have hspT : T.regs 4 = s.regs 4 - 232#64 := by rw [f4, hsp]; exact sp232 _ (by omega)
  have hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hmf.accessible, hF.accessible]; exact hw
  have hg14 : T.regs 14 = s.regs 14 := f14.trans h14
  rw [h14] at hinvT
  refine epiCM impl (retAddrOf s) _ hb' ha T hpcT hspT hTacc hKb.h.2.2.1 hKb.h.2.2.2.2.2 hKb.h.2.2.2.1 ?_
  intro S2 p2 sp2 r2 r5 r14 rx rfs rdf hF2 hrg2 hra2 w0 w1 w2 w3 w4 w5
  have hWb : Box (S2.mem.readLE ((s.regs 4).toNat - 80) 8 = (T.regs 7).toNat ∧
      S2.mem.readLE ((s.regs 4).toNat - 72) 8 = (T.regs 6).toNat ∧
      S2.mem.readLE ((s.regs 4).toNat - 64) 8 = (T.regs 8).toNat) := ⟨⟨w3, w4, w5⟩⟩
  clear w0 w1 w2 w3 w4 w5
  -- the stack at `S2`
  have hhdO := out_inR2 hwO hN.hdr.1
  have hst2 : Outside st 24 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120)] :=
    st3 hb' hhdO
  obtain ⟨hok2, ew2, el2, ec2⟩ := stkOK_frame hok1 hF2 hst2
  have hrsE : stkRs S2.mem st = stkRs T.mem st := stkRs_congr ew2 ec2
  -- the guard word and the window at `S2`
  have hgS : S2.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    guardS hN hb' hga hgr (fun hc => (hp.uo.2.2 hc).2.1) hsp hF hmf hF2
  have hacS : ∀ a k w, S2.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF2.accessible, hmf.accessible, hF.accessible]
  have h24' : S2.mem.readLE ((s.regs 4).toNat - 24) 8 = st := by
    rw [hF2.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hKb.h.2.2.2.2.1
  have e14 : (S2.regs 14).toNat = (s.regs 14).toNat := by rw [r14, hg14]
  have hinv2 : R.inv b'' L2 (s.regs 14).toNat (view R.rt L2 S2.mem) := RtInv.inv_frame' hF2 (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals left; exact hwO.of_sub (by simp only; omega) (by simp only; omega)) hinvT
  have esp2 : (S2.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [sp2, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hpre := freePreM (b' := b'') (L2 := L2) (sp := (s.regs 4).toNat) hN esp2
    (by rw [r2, BitVec.toNat_ofNat]; omega) hra2 e14 hg1
    (by rw [hacS]; exact hg2) (by rw [hgS]; omega) hga hgr hal hb' ha (by rw [hacS]; exact hw) hwO hLs h24'
    hok2 (by rw [el2]; exact hl1) (by rw [ec2, ew2]; exact hc01) (by rw [ec2, ew2]; exact hdis1)
    (by rw [hrsE]; exact hrs1) hx (hp.srv.2.2.2.2.2.2.2.2 [Free.poolA]) hinv2
  refine epiRM impl (dsumM impl hap R hput b'' L2 (stkRs S2.mem st)) _ hb' ha S2 p2 sp2 hra2 hpre hra ?_
  intro s3 hpost3 hrg3
  obtain ⟨⟨t4, t5, t14, t15, tfs, tdf⟩, hMF3, hLF3, hinv3⟩ := hpost3
  have hso : Free.stkOf S2 = st := by
    show S2.mem.readLE ((S2.regs 2).toNat + 8) 8 = st
    rw [r2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (s.regs 4).toNat - 32 + 8 = (s.regs 4).toNat - 24 by omega]
    exact h24'
  rw [hso, esp2] at hMF3
  rw [hso] at hLF3
  rw [e14] at hinv3
  have hrd3 : ∀ a, (s.regs 4).toNat - 240 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 →
      s3.mem.readLE a 8 = S2.mem.readLE a 8 := by
    intro a i1 i2
    refine hMF3.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwO.of_sub (by omega) (by omega), by omega, by omega⟩
  have hrdT : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 121 ∨ (s.regs 4).toNat - 120 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 80 ∨ (s.regs 4).toNat - 32 ≤ a) → (s.regs 4).toNat - 232 ≤ a →
      S2.mem.readLE a 8 = T.mem.readLE a 8 := fun a i1 i2 i3 =>
    hF2.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨t4, by rw [hMF3.accessible, hacS]; exact hw, ?_, ?_⟩
  · rw [hrd3 _ (by omega) (by omega), hrdT _ (by omega) (by omega) (by omega)]; exact hKb.h.1
  intro s4 hs4 v0 v3 v1 v7 v6 v8 v5 v14 vx vfs vdf hm4
  have q7 : s4.regs 7 = BitVec.ofNat 64 r := by
    rw [v7, hrd3 _ (by omega) (by omega), hWb.h.1, e3, Expmc.bv_ofNat_toNat]
  have q6 : s4.regs 6 = BitVec.ofNat 64 rl := by
    rw [v6, hrd3 _ (by omega) (by omega), hWb.h.2.1, e4, Expmc.bv_ofNat_toNat]
  have q8 : s4.regs 8 = BitVec.ofNat 64 rc := by
    rw [v8, hrd3 _ (by omega) (by omega), hWb.h.2.2, e5, Expmc.bv_ofNat_toNat]
  have q5 : s4.regs 5 = s.regs 5 := by
    rw [v5, hrd3 _ (by omega) (by omega), hrdT _ (by omega) (by omega) (by omega), hKb.h.2.1,
      Expmc.bv_ofNat_toNat]
  have q14 : s4.regs 14 = s.regs 14 := v14.trans (t14.trans (r14.trans hg14))
  have qx : s4.xmm 15 = s.xmm 15 := by
    rw [vx, t15, rx, f15, hx15, hx0]
  have qfs : s4.fsBase = s.fsBase := vfs.trans (tfs.trans (rfs.trans (hfsT.trans hfs)))
  have qdf : s4.df = s.df := by rw [vdf, tdf, rdf, hdfT, hdfX, hdf0]
  refine ⟨⟨hs4, q5, q14, qx⟩, ?_⟩
  obtain ⟨hr', hsb⟩ := hB.h
  exact postBigM hp hN hF hLF hsp hr' hx hbbB.h hsb hfr hmf hlf hF2 hMF3 hLF3
    (by rw [hrsE] at hinv3 ⊢; exact hinv3) s4 hm4 qfs qdf v0 v3 v1 q7 q6 q8

end FvModexp.Amd64.Q.NatDiv
