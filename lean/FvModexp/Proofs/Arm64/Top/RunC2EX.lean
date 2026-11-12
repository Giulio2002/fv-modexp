import FvModexp.Proofs.Arm64.Top.RunC2RA
import FvModexp.Proofs.Arm64.Top.RunC2Lem3
import FvModexp.Proofs.Arm64.Top.RunC2One

set_option autoImplicit false

/-! # `Run` (arm64): from the `exp` call block (`fn + 0x864`) to `V`: `v = base.exp(base, exp, mod, false).Bytes()`

(`base.Exp(base, exp, mod)` of `contracts.go:692` inlined: `mod ≠ 0`, `exp.neg = false`, so `Exp` calls `z.exp(x, y, m,
false)` — `int.go:568`.) Reached from `C2` on both `base.BitLen() ≠ 1` paths (`RunC2E`). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- The state at the `exp` call (`fn + 0x878`), as `janus_run` builds it from the block's entry state `T`. -/
abbrev expCallS (T s : State) (rg : Nat → W64) (pcc : W64) : State := { T with regs := rg, sp := s.sp - 624#64, pc := pcc }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c2eXB (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : RunIface.ExpSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (Q : Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 28).toNat + 16) 8 L)
    (hbB : okB s p len ≤ b)
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 L1 b1 T)
    (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x864)) (hv2 : 0 < opV s p len 2)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.pc = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q)
    (rg : Nat → W64) (pcc : W64) (s' : State) (e3 : rg 28 = s.regs 28)
    (hpc' : s'.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x87c))
    (hsp1 : s'.sp = (expCallS T s rg pcc).sp) (h281 : s'.regs 28 = (expCallS T s rg pcc).regs 28)
    (h291 : s'.regs 29 = (expCallS T s rg pcc).regs 29) (h181 : s'.regs 18 = (expCallS T s rg pcc).regs 18) (e29 : rg 29 = T.regs 29) (e18 : rg 18 = T.regs 18)
    (hr01 : s'.regs 0 = s.sp - 136#64)
    (hpost : RunIface.IntPost R b1 (RunIface.ExpBudget (max (max (RunIface.lenW T.mem (s.sp.toNat - 136))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) (RunIface.lenW T.mem (s.sp.toNat - 200)))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) L1 stkM aboveM (s.sp.toNat - 136)
        (RunIface.IntV T.mem (s.sp.toNat - 136) ^ RunIface.IntV T.mem (s.sp.toNat - 168) %
          RunIface.IntV T.mem (s.sp.toNat - 200)) (expCallS T s rg pcc) s')
    (hrg1 : s'.mem.regions = (expCallS T s rg pcc).mem.regions) :
    Reaches ((LibRun.program.link impl).withExit ret) s' Q := by
  have henvW0 := henvW
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henvW
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  simp only [stk] at hLsS hMF
  have hspn : T.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  obtain ⟨-, hval0, -, h1280, -, hlive0⟩ := hop 0 (by omega)
  simp only [opAt, show s.sp.toNat - 136 - 32 * 0 = s.sp.toNat - 136 by omega] at hval0 h1280 hlive0
  obtain ⟨-, hval1, -, h1281, -, -⟩ := hop 1 (by omega)
  simp only [opAt, show s.sp.toNat - 136 - 32 * 1 = s.sp.toNat - 168 by omega] at hval1 h1281
  obtain ⟨-, hval2, -, h1282, -, -⟩ := hop 2 (by omega)
  simp only [opAt, show s.sp.toNat - 136 - 32 * 2 = s.sp.toNat - 200 by omega] at hval2 h1282
  -- the exp call: IntPre outside the run
  have hxs : ∀ a ∈ [s.sp.toNat - 136, s.sp.toNat - 168, s.sp.toNat - 200], ∃ j, j < 3 ∧ a = opAt s j := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, by omega, by simp only [opAt]; omega⟩
    · exact ⟨1, by omega, by simp only [opAt]; omega⟩
    · exact ⟨2, by omega, by simp only [opAt]; omega⟩
  have hpw : [s.sp.toNat - 136, s.sp.toNat - 168, s.sp.toNat - 200].Pairwise
      fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j := by
    refine List.Pairwise.cons (fun a' ha' => ?_) (List.Pairwise.cons (fun a' ha' => ?_) (List.pairwise_singleton _ _))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · exact ⟨0, 1, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
      · exact ⟨0, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
    · simp only [List.mem_singleton] at ha'; subst ha'
      exact ⟨1, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
  have l0 : RunIface.lenW T.mem (s.sp.toNat - 136) ≤ wMax s p len :=
    Nat.le_trans (lenW_op0 (hop 0 (by omega))) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have l1 : RunIface.lenW T.mem (s.sp.toNat - 168) ≤ wMax s p len :=
    Nat.le_trans (lenW_op1 (hop 1 (by omega))) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have l1' : RunIface.lenW T.mem (s.sp.toNat - 168) ≤ opW s p len 1 := lenW_op1 (hop 1 (by omega))
  have l2 : RunIface.lenW T.mem (s.sp.toNat - 200) ≤ wMax s p len :=
    Nat.le_trans (lenW_op2 (hop 2 (by omega))) (Nat.le_max_right _ _)
  have hbB' := hbB
  simp only [okB, callB] at hbB'
  have hBm : RunIface.ExpBudget (max (max (RunIface.lenW T.mem (s.sp.toNat - 136)) (RunIface.lenW T.mem (s.sp.toNat - 168)))
      (RunIface.lenW T.mem (s.sp.toNat - 200))) (RunIface.lenW T.mem (s.sp.toNat - 168)) ≤ b1 := by
    have := budget_c2e0 (lb := 0) l0 l1 l2 l1' (Nat.zero_le _) hbud hbB'
    omega
  have hy0 : 0 < RunIface.IntV T.mem (s.sp.toNat - 200) := by rw [intV_eq]; rw [hval2]; exact hv2
  have hzl : RunIface.IntLenLe T.mem (s.sp.toNat - 136) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW; exact h1280
  have hyl : RunIface.IntLenLe T.mem (s.sp.toNat - 168) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW; exact h1281
  have hml : RunIface.IntLenLe T.mem (s.sp.toNat - 200) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW; exact h1282
  have hIP : ∀ t : State, t.sp = T.sp → t.mem = T.mem → t.regs 28 = s.regs 28 →
      RunIface.IntPre R b1 (RunIface.ExpBudget (max (max (RunIface.lenW T.mem (s.sp.toNat - 136))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) (RunIface.lenW T.mem (s.sp.toNat - 200)))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) L1 stkM aboveM
        [s.sp.toNat - 136, s.sp.toNat - 168, s.sp.toNat - 200] t :=
    fun t h1 h2 h3 => intPre_ops _ (by rw [h1]; exact hspn) h2 h3 henvW0 hW hW1 hab hglob hgL hsv hBm hdS hext hinv hMF
      hop hopA hxs hpw
  have h281' : s'.regs 28 = s.regs 28 := h281.trans e3
  replace h291 : s'.regs 29 = T.regs 29 := h291.trans e29
  replace h181 : s'.regs 18 = T.regs 18 := h181.trans e18
  replace hsp1 : s'.sp = T.sp := hsp1.trans hsp.symm
  have hgz : Apart RunIface.gA 32 (s.sp.toNat - 136) 32 := by
    have := hglob.2.2.2.2.2.2.2.2.2
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this; unfold Apart; omega
  have hga : 0 < T.mem.readLE (s.sp.toNat - 136 + 24) 8 →
      Apart RunIface.gA 32 (T.mem.readLE (s.sp.toNat - 136 + 8) 8) (8 * T.mem.readLE (s.sp.toNat - 136 + 24) 8) :=
    fun hc => InRanges.apart (hlive0 hc).2.2.2.2.1 hglob.2.2.2.2.2.2.2.2.1
  have hlb : RunIface.lenW s'.mem (s.sp.toNat - 136) ≤ RunIface.maxW := by
    have hp' := hpost
    obtain ⟨hvz, L', b', -, -, -, hokz, -⟩ := hp'
    have hn := hokz.2.2.2.2.2.2.2.1
    have hlt : RunIface.IntV s'.mem (s.sp.toNat - 136) < RunIface.IntV T.mem (s.sp.toNat - 200) := by
      rw [hvz]; exact Nat.mod_lt _ hy0
    unfold RunIface.IntV at hlt
    have := len_le_of_lt_norm _ _ _ _ _ _ hn hlt
    unfold RunIface.IntLenLe RunIface.maxW at hml
    unfold RunIface.lenW RunIface.maxW; omega
  have hBB : RunIface.ExpBudget (max (max (RunIface.lenW T.mem (s.sp.toNat - 136))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) (RunIface.lenW T.mem (s.sp.toNat - 200)))
        (RunIface.lenW T.mem (s.sp.toNat - 168)) + RunIface.BytesBudget (RunIface.lenW s'.mem (s.sp.toNat - 136)) ≤ b1 :=
    budget_c2e0 l0 l1 l2 l1' hlb hbud hbB'
  obtain ⟨L2, b2, hext2, hb2, hv1, hinv2, hok2, hMF2, hLF2, hIPb⟩ :=
    afterInt hIP hpost hsp.symm rfl e3 hrg1 hgz hga hBB
  have hBy' := bytesW impl hap R stkM aboveM hBy b2 L2 (s.sp - 624#64) (s.regs 28) s'.mem (s.sp.toNat - 136)
    (fun t h1 h2 h3 => hIPb t h1 h2 (h3.trans e3.symm)) hlb
  have hz136 : (s.sp - 136#64).toNat = s.sp.toNat - 136 := by rw [BitVec.toNat_sub]; simp; omega
  have hsp624 : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [← hsp]; exact hspn
  have harrR : 0 < T.mem.readLE (s.sp.toNat - 136 + 24) 8 → InRanges (T.mem.readLE (s.sp.toNat - 136 + 8) 8)
      (8 * T.mem.readLE (s.sp.toNat - 136 + 24) 8) R.rt := fun hc => (hlive0 hc).2.2.2.2.1
  have harrL : 0 < T.mem.readLE (s.sp.toNat - 136 + 24) 8 → ApartAll (T.mem.readLE (s.sp.toNat - 136 + 8) 8)
      (8 * T.mem.readLE (s.sp.toNat - 136 + 24) 8) L := fun hc => (hlive0 hc).2.2.2.2.2
  have hIV0 : RunIface.IntV T.mem (s.sp.toNat - 136) = opV s p len 0 := by rw [intV_eq]; exact hval0
  have hIV1 : RunIface.IntV T.mem (s.sp.toNat - 168) = opV s p len 1 := by rw [intV_eq]; exact hval1
  have hIV2 : RunIface.IntV T.mem (s.sp.toNat - 200) = opV s p len 2 := by rw [intV_eq]; exact hval2
  have hspW : W ≤ s.sp.toNat := by omega
  have hTw : T.mem.accessible (s.sp.toNat - W) (W + 40) true = true := by rw [hMF.accessible]; exact hw
  have hz1 : s.sp.toNat - W ≤ s.sp.toNat - 136 := by omega
  have hz2 : s.sp.toNat - 136 + 32 ≤ s.sp.toNat + 40 := by omega
  have hwsW : ∀ r ∈ win s W 40, s.sp.toNat - W ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ s.sp.toNat - W + (W + 40) := by
    intro r hr; simp only [win, List.mem_singleton] at hr; subst hr; dsimp only; omega
  have hsl : ∀ (M2 : Memory) (t : State), t.sp = s.sp - 624#64 → MemFrame s'.mem M2 (R.rt ++ winA t stkM aboveM) →
      M2.readLE (s.sp.toNat - 624) 8 = ret ∧ M2.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
      M2.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 := by
    intro M2 t ht h3
    have o1 : Outside (s.sp.toNat - 624) 8 R.rt := hout.of_sub (by omega) (by omega)
    have o2 : Outside (s.sp.toNat - 632) 8 R.rt := hout.of_sub (by omega) (by omega)
    have o3 : Outside (s.sp.toNat - 464) 8 R.rt := hout.of_sub (by omega) (by omega)
    exact ⟨(slot_TV (h1 := hMF2) (h2 := h3) ht hsp624 o1 (by omega) (by omega) harrR).trans hm1,
      (slot_TV (h1 := hMF2) (h2 := h3) ht hsp624 o2 (by omega) (by omega) harrR).trans hm2,
      (slot_TV (h1 := hMF2) (h2 := h3) ht hsp624 o3 (by omega) (by omega) harrR).trans hs3⟩
  try clear hop
  try clear hopA
  try clear hxs
  try clear hpw
  try clear hExp
  try clear henvW0
  try clear hglob
  try clear hgL
  try clear hsv
  try clear hLsS
  try clear hinv
  try clear hBm
  try clear hy0
  try clear hzl
  try clear hyl
  try clear hml
  try clear hpost
  try clear hgz
  try clear hBB
  try clear hE
  try clear hBy
  try clear hg1
  try clear hg2
  try clear hg3
  try clear hgr
  try clear hIP
  try clear hval0
  try clear hval1
  try clear hval2
  try clear h1280
  try clear h1281
  try clear h1282
  try clear hlive0
  try clear hbB
  try clear hd
  try clear hb'
  try clear ha
  try clear hal
  janus_run [hsp1, h281', hr01, hz136] until [pcCV] calls [hQ := hBy']
  obtain ⟨⟨hsp2, h282, h292, h182⟩, vp, vn, vc, hvp, hvn, -, -, hbe, hmin, Lb, bb, hext3, hb3, hinv3, hfr3, hMF3,
    hLF3⟩ := hQ.1
  have hrg3 := hQ.2
  clear hQ hBy' hIPb
  have hval : beVal s'.mem vp vn = resV s p len := by
    rw [hbe, hv1, hIV0, hIV1, hIV2, resV_eq _ _ _ hv2]
  have hvlt : vn ≤ hdrV s p len 2 :=
    beLen_le _ _ _ _ hmin (by rw [hbe, hv1, hIV0, hIV1, hIV2]; exact lt_modLen s p len (Nat.mod_lt _ hv2))
  have hMFTV := frame_TV (sp := s.sp.toNat) hW hab hspW hsp624 hsp624 hz1 hz2 harrR hMF2 hMF3
  have hMFall : MemFrame s.mem s'.mem (R.rt ++ win s W 40) :=
    (memFrame_win hW1 hMF).trans hMFTV fun _ _ h => ⟨h, h⟩
  have hLFall : LiveFrame s.mem s'.mem L [] :=
    hLF.trans (liveFrame_TV hext hext2 hLs hz1 hz2 harrL hLF2 hLF3) fun _ _ h => h
  have hextB := (hext.trans hext2).trans hext3
  obtain ⟨e1, e2, e3⟩ := hsl _ _ rfl hMF3
  refine hk _ Lb bb ⟨by first | rfl | janus_simp [hsp2, hsp1, hsp], by janus_simp [h282, h281'], by janus_simp [h292, h291, h29], by janus_simp [h182, h181, h18],
    e1, e2, e3, hl2, dataLoaded_win hdS (hrg3.trans hrg1) hro hMFTV hTw hwsW, ?vn, ?vv, ?fr, hextB, ?bud, hinv3,
    liveSep_W hextB hLs hout hspW, hMFall, hLFall⟩ (by janus_simp)
  case vn => show (s'.regs 1).toNat ≤ _; rw [hvn]; exact hvlt
  case vv => show beVal s'.mem (s'.regs 0).toNat (s'.regs 1).toNat = _; rw [hvp, hvn]; exact hval
  case fr =>
    show 0 < (s'.regs 1).toNat → _
    rw [hvp, hvn]; intro h
    obtain ⟨a1, a2, -, a4, a5⟩ := hfr3 h
    exact ⟨a1, a2, a4, a5⟩
  case bud =>
    unfold callB
    exact budget_c2e l0 l1 l2 l1' hlb hbud hb2 hb3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c2eX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : RunIface.ExpSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (Q : Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 28).toNat + 16) 8 L)
    (hbB : okB s p len ≤ b) (hone : FvModexp.Spec.RunArm64.NatOne R s.mem (win s W 40))
    (hpool : FvModexp.Spec.RunArm64.StackPool R s.mem (win s W 40))
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 L1 b1 T)
    (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x864)) (hv2 : 0 < opV s p len 2)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.pc = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have henvW0 := henvW
  have hrel0 := hrel
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henvW
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  simp only [stk] at hLsS hMF
  have hspn : T.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  obtain ⟨-, hval0, -, h1280, -, hlive0⟩ := hop 0 (by omega)
  simp only [opAt, show s.sp.toNat - 136 - 32 * 0 = s.sp.toNat - 136 by omega] at hval0 h1280 hlive0
  obtain ⟨-, hval1, -, h1281, -, -⟩ := hop 1 (by omega)
  simp only [opAt, show s.sp.toNat - 136 - 32 * 1 = s.sp.toNat - 168 by omega] at hval1 h1281
  obtain ⟨-, hval2, -, h1282, -, -⟩ := hop 2 (by omega)
  simp only [opAt, show s.sp.toNat - 136 - 32 * 2 = s.sp.toNat - 200 by omega] at hval2 h1282
  -- the exp call: IntPre outside the run
  have hxs : ∀ a ∈ [s.sp.toNat - 136, s.sp.toNat - 168, s.sp.toNat - 200], ∃ j, j < 3 ∧ a = opAt s j := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, by omega, by simp only [opAt]; omega⟩
    · exact ⟨1, by omega, by simp only [opAt]; omega⟩
    · exact ⟨2, by omega, by simp only [opAt]; omega⟩
  have hpw : [s.sp.toNat - 136, s.sp.toNat - 168, s.sp.toNat - 200].Pairwise
      fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j := by
    refine List.Pairwise.cons (fun a' ha' => ?_) (List.Pairwise.cons (fun a' ha' => ?_) (List.pairwise_singleton _ _))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · exact ⟨0, 1, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
      · exact ⟨0, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
    · simp only [List.mem_singleton] at ha'; subst ha'
      exact ⟨1, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
  have l0 : RunIface.lenW T.mem (s.sp.toNat - 136) ≤ wMax s p len :=
    Nat.le_trans (lenW_op0 (hop 0 (by omega))) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have l1 : RunIface.lenW T.mem (s.sp.toNat - 168) ≤ wMax s p len :=
    Nat.le_trans (lenW_op1 (hop 1 (by omega))) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have l1' : RunIface.lenW T.mem (s.sp.toNat - 168) ≤ opW s p len 1 := lenW_op1 (hop 1 (by omega))
  have l2 : RunIface.lenW T.mem (s.sp.toNat - 200) ≤ wMax s p len :=
    Nat.le_trans (lenW_op2 (hop 2 (by omega))) (Nat.le_max_right _ _)
  have hbB' := hbB
  simp only [okB, callB] at hbB'
  have hBm : RunIface.ExpBudget (max (max (RunIface.lenW T.mem (s.sp.toNat - 136)) (RunIface.lenW T.mem (s.sp.toNat - 168)))
      (RunIface.lenW T.mem (s.sp.toNat - 200))) (RunIface.lenW T.mem (s.sp.toNat - 168)) ≤ b1 := by
    have := budget_c2e0 (lb := 0) l0 l1 l2 l1' (Nat.zero_le _) hbud hbB'
    omega
  have hy0 : 0 < RunIface.IntV T.mem (s.sp.toNat - 200) := by rw [intV_eq]; rw [hval2]; exact hv2
  have hzl : RunIface.IntLenLe T.mem (s.sp.toNat - 136) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW; exact h1280
  have hyl : RunIface.IntLenLe T.mem (s.sp.toNat - 168) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW; exact h1281
  have hml : RunIface.IntLenLe T.mem (s.sp.toNat - 200) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW; exact h1282
  have hIP : ∀ t : State, t.sp = T.sp → t.mem = T.mem → t.regs 28 = s.regs 28 →
      RunIface.IntPre R b1 (RunIface.ExpBudget (max (max (RunIface.lenW T.mem (s.sp.toNat - 136))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) (RunIface.lenW T.mem (s.sp.toNat - 200)))
        (RunIface.lenW T.mem (s.sp.toNat - 168))) L1 stkM aboveM
        [s.sp.toNat - 136, s.sp.toNat - 168, s.sp.toNat - 200] t :=
    fun t h1 h2 h3 => intPre_ops _ (by rw [h1]; exact hspn) h2 h3 henvW0 hW hW1 hab hglob hgL hsv hBm hdS hext hinv hMF
      hop hopA hxs hpw
  have hExp := expW impl hap R stkM aboveM hE b1 L1 T.sp (s.regs 28) T.mem (s.sp.toNat - 136) (s.sp.toNat - 168)
    (s.sp.toNat - 200) hIP hy0 hzl hyl hml
    (fun t h1 => oneG_ops _ (by rw [h1]; exact hspn) hW hab hb' hone hMF hW1 hop hxs)
    (fun t h1 => poolG_ops (by rw [h1]; exact hspn) hW hab hb' hpool hMF hW1)
    (expX_ops hb' hW1 hglob.2.2.2.2.2.2.2.2.2.2.2.2).1 (expX_ops hb' hW1 hglob.2.2.2.2.2.2.2.2.2.2.2.2).2
    (by unfold RunIface.ModX; intro hc; exact (InRanges.apart (hlive0 hc).2.2.2.2.1 hglob.2.2.2.2.2.2.2.2.1).symm)
  have hRA := raExp impl hap
  janus_run until [segAddr Extracted.program fn + 0x87c] calls [hP := hExp]
  obtain ⟨⟨⟨hsp1, h281, h291, h181⟩, hr01, hpost⟩, hrg1⟩ := hP
  exact c2eXB impl hap R stkM aboveM hE hBy hsv b L c p len cp ret hret s Q W henvW0 hW hW1 hab hglob hgL hbB L1 b1 T
    hrel0 hpc hv2 hk _ _ _ (by janus_simp [h28]) (by janus_simp) hsp1 h281 h291 h181
    (by janus_simp [h29]) (by janus_simp [h18]) (by rw [hr01]; try janus_simp [hsp]) hpost hrg1

end FvModexp.Arm64.Run
