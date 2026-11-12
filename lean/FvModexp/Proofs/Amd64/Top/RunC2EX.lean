import FvModexp.Proofs.Amd64.Top.RunC2B
import FvModexp.Proofs.Common.GenReg

/-! # `Run` (amd64): the `exp` path — `C2` with `base.BitLen() ≠ 1` to the exp block `fn + 0xb9b` (`c2e`), and the
exp block: `exp(&base, &base, &exp, &mod, false)` (call `fn + 0xbb8`, return `fn + 0xbbd`), `Bytes(z)` (call
`fn + 0xbc0`, return `V`) (`c2eX`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c2eX (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : RunIface.ExpSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (Q : Janus.Amd64.Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144)
    (ha8 : 8 ≤ aboveM)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 14).toNat + 16) 8 L)
    (hfL : ApartAll (s.fsBase.toNat - 8) 8 L)
    (hbB : okB s p len ≤ b)
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 3 (cstD 3) L1 b1 T)
    (hpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0xb9b)) (hv2 : 0 < opV s p len 2)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.rip = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have henvW0 := henvW
  have hrel0 := hrel
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henvW
  simp only [regSP, Janus.Amd64.GoABI.regG] at hb' ha hw hout hal hga hgr
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, -, -, -, -, -, -, hs3, -, -, -, hl0, hl1, hl2, hnz, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  simp only [stk] at hLsS hMF
  rw [hx0] at hx15
  rw [hdf0] at hdf
  have hspn : (T.regs 4).toNat = (s.regs 4).toNat - 608 := by
    rw [hsp, BitVec.toNat_sub]; simp; omega
  have hsp0 : (T.regs 4 - 8#64).toNat = (s.regs 4).toNat - 616 := by
    rw [BitVec.toNat_sub, hspn]; simp; omega
  obtain ⟨-, hval2, -, h1282, -, -⟩ := hop 2 (by omega)
  simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at hval2 h1282
  have e1 : (s.regs 4).toNat - 136 - 32 * 1 = (s.regs 4).toNat - 168 := by omega
  have e2 : (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 := by omega
  have hxs : ∀ a ∈ [(s.regs 4).toNat - 136, (s.regs 4).toNat - 168, (s.regs 4).toNat - 200], ∃ j, j < 3 ∧ a = opAt s j := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, by omega, by simp only [opAt]; omega⟩
    · exact ⟨1, by omega, by simp only [opAt]; omega⟩
    · exact ⟨2, by omega, by simp only [opAt]; omega⟩
  have hpw : [(s.regs 4).toNat - 136, (s.regs 4).toNat - 168, (s.regs 4).toNat - 200].Pairwise
      fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j := by
    refine List.Pairwise.cons (fun a' ha' => ?_) (List.Pairwise.cons (fun a' ha' => ?_) (List.pairwise_singleton _ _))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · exact ⟨0, 1, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
      · exact ⟨0, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
    · simp only [List.mem_singleton] at ha'; subst ha'
      exact ⟨1, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
  have l0 : RunIface.lenW T.mem ((s.regs 4).toNat - 136) ≤ wMax s p len :=
    Nat.le_trans (lenW_op (hop 0 (by omega)) (by omega)) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have l1 : RunIface.lenW T.mem ((s.regs 4).toNat - 168) ≤ wMax s p len := by
    have := lenW_op (hop 1 (by omega)) (by omega); simp only [opAt, e1] at this
    exact Nat.le_trans this (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have l1' : RunIface.lenW T.mem ((s.regs 4).toNat - 168) ≤ opW s p len 1 := by
    have := lenW_op (hop 1 (by omega)) (by omega); simp only [opAt, e1] at this; exact this
  have l2 : RunIface.lenW T.mem ((s.regs 4).toNat - 200) ≤ wMax s p len := by
    have := lenW_op (hop 2 (by omega)) (by omega); simp only [opAt, e2] at this
    exact Nat.le_trans this (Nat.le_max_right _ _)
  -- the memory at `exp`'s entry: the return address pushed at `e - 616`
  generalize hMd : T.mem.writeLE ((s.regs 4).toNat - 616) 8 6639357 = M
  have hMr : ∀ j, j < 3 → ∀ o, o + 8 ≤ 32 → M.readLE (opAt s j + o) 8 = T.mem.readLE (opAt s j + o) 8 := by
    intro j hj o ho; rw [← hMd]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp only [opAt]; omega)
  have hlwj : ∀ j a, j < 3 → a = opAt s j → RunIface.lenW M a = RunIface.lenW T.mem a := by
    intro j a hj ha; subst ha; simp only [RunIface.lenW]; exact hMr j hj 16 (by omega)
  have hlw0 := hlwj 0 ((s.regs 4).toNat - 136) (by omega) (by simp only [opAt]; omega)
  have hlw1 := hlwj 1 ((s.regs 4).toNat - 168) (by omega) (by simp only [opAt, e1])
  have hlw2 := hlwj 2 ((s.regs 4).toNat - 200) (by omega) (by simp only [opAt, e2])
  have hBm : RunIface.ExpBudget (max (max (RunIface.lenW M ((s.regs 4).toNat - 136)) (RunIface.lenW M ((s.regs 4).toNat - 168)))
      (RunIface.lenW M ((s.regs 4).toNat - 200))) (RunIface.lenW M ((s.regs 4).toNat - 168)) ≤ b1 := by
    rw [hlw0, hlw1, hlw2]
    have hbB' := hbB
    simp only [okB, callB] at hbB'
    have := budget_c2e0 (lb := 0) l0 l1 l2 l1' (Nat.zero_le _) hbud hbB'
    omega
  have hIV : ∀ j, j < 3 → RunIface.IntV M (opAt s j) = RunIface.IntV T.mem (opAt s j) := by
    intro j hj
    obtain ⟨-, -, -, -, hlcj, hlivej⟩ := hop j hj
    unfold RunIface.IntV
    rw [hMr j hj 8 (by omega), hMr j hj 16 (by omega)]
    by_cases hz : T.mem.readLE (opAt s j + 16) 8 = 0
    · rw [hz]; rfl
    · obtain ⟨hin, -⟩ := hlivej (by omega)
      have ho := outside_of_inRanges hin hLsS
      simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true] at ho
      rw [← hMd]; simp only [natVal]
      exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hIVj : ∀ j a, j < 3 → a = opAt s j → RunIface.IntV M a = opV s p len j := by
    intro j a hj ha; subst ha; rw [hIV j hj, intV_eq]; exact (hop j hj).2.1
  have hy0 : 0 < RunIface.IntV M ((s.regs 4).toNat - 200) := by
    rw [hIVj 2 ((s.regs 4).toNat - 200) (by omega) (by simp only [opAt, e2])]; exact hv2
  have hlenj : ∀ j a, j < 3 → a = opAt s j → RunIface.IntLenLe M a RunIface.maxW := by
    intro j a hj ha; subst ha
    unfold RunIface.IntLenLe RunIface.maxW; rw [hMr j hj 16 (by omega)]; exact (hop j hj).2.2.2.1
  have hIP : ∀ t : State, t.regs 4 = T.regs 4 - 8#64 → t.mem = M → t.regs 14 = s.regs 14 → t.fsBase = s.fsBase →
      RunIface.IntPre R b1 (RunIface.ExpBudget (max (max (RunIface.lenW M ((s.regs 4).toNat - 136))
        (RunIface.lenW M ((s.regs 4).toNat - 168))) (RunIface.lenW M ((s.regs 4).toNat - 200)))
        (RunIface.lenW M ((s.regs 4).toNat - 168))) L1 stkM aboveM
        [(s.regs 4).toNat - 136, (s.regs 4).toNat - 168, (s.regs 4).toNat - 200] t := by
    intro t h4 hm h14' hfs'
    have h0 := intPre_ops (T := { t with mem := T.mem }) (M := T.mem) _ (by simp only; rw [h4]; exact hsp0) rfl
      (by simp only; exact h14') (by simp only; exact hfs') henvW0 hW hW1 hab ha8 hglob hgL hfL hsv hBm hdS hext hinv
      hMF hop hopA hxs hpw
    exact intPre_push h0 ha8 6639357 rfl rfl rfl (by simp only; rw [hm, ← hMd, h4, hsp0])
  have hRA : RetAddr ((Extracted.program.onlySegments RunIface.namesExp).link impl)
      (M.readLE (T.regs 4 - 8#64).toNat 8) := by
    rw [hsp0, ← hMd, Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by decide),
      show (6639357 : Nat) = 0x654340 + 0xbbd by decide]
    exact raExp impl hap
  have hExp := expW impl hap R stkM aboveM hE b1 L1 (T.regs 4 - 8#64) (s.regs 14) s.fsBase M
    ((s.regs 4).toNat - 136) ((s.regs 4).toNat - 168) ((s.regs 4).toNat - 200) hRA hIP hy0
    (hlenj 0 ((s.regs 4).toNat - 136) (by omega) (by simp only [opAt]; omega)) (hlenj 1 ((s.regs 4).toNat - 168) (by omega) (by simp only [opAt, e1]))
    (hlenj 2 ((s.regs 4).toNat - 200) (by omega) (by simp only [opAt, e2]))
  have hz136 : (s.regs 4 - 608#64 + 472#64).toNat = (s.regs 4).toNat - 136 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
  have hz168 : (s.regs 4 - 608#64 + 440#64).toNat = (s.regs 4).toNat - 168 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
  have hz200 : (s.regs 4 - 608#64 + 408#64).toNat = (s.regs 4).toNat - 200 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
  clear hRA
  have hBB : RunIface.ExpBudget (max (max (RunIface.lenW M ((s.regs 4).toNat - 136)) (RunIface.lenW M ((s.regs 4).toNat - 168)))
      (RunIface.lenW M ((s.regs 4).toNat - 200))) (RunIface.lenW M ((s.regs 4).toNat - 168)) +
      RunIface.BytesBudget RunIface.maxW ≤ b1 := by
    rw [hlw0, hlw1, hlw2]
    have hbB' := hbB
    simp only [okB, callB] at hbB'
    exact budget_c2e0 l0 l1 l2 l1' (Nat.le_refl _) hbud hbB'
  have hbfin : ∀ b2 b3 lb, lb ≤ RunIface.maxW → b1 - RunIface.ExpBudget (max (max (RunIface.lenW M ((s.regs 4).toNat - 136))
      (RunIface.lenW M ((s.regs 4).toNat - 168))) (RunIface.lenW M ((s.regs 4).toNat - 200)))
      (RunIface.lenW M ((s.regs 4).toNat - 168)) ≤ b2 → b2 - RunIface.BytesBudget lb ≤ b3 →
      b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ b3 := fun b2 b3 lb hl h2 h3 => by
    rw [hlw0, hlw1, hlw2] at h2
    unfold callB; exact budget_c2e l0 l1 l2 l1' hl hbud h2 h3
  have hv : RunIface.IntV M ((s.regs 4).toNat - 136) ^ RunIface.IntV M ((s.regs 4).toNat - 168) %
      RunIface.IntV M ((s.regs 4).toNat - 200) = resV s p len := by
    rw [hIVj 0 ((s.regs 4).toNat - 136) (by omega) (by simp only [opAt]; omega), hIVj 1 ((s.regs 4).toNat - 168) (by omega) (by simp only [opAt, e1]),
      hIVj 2 ((s.regs 4).toNat - 200) (by omega) (by simp only [opAt, e2]), resV_eq _ _ _ hv2]
  have hvlt : RunIface.IntV M ((s.regs 4).toNat - 136) ^ RunIface.IntV M ((s.regs 4).toNat - 168) %
      RunIface.IntV M ((s.regs 4).toNat - 200) < opV s p len 2 := by
    rw [hIVj 2 ((s.regs 4).toNat - 200) (by omega) (by simp only [opAt, e2])]; exact Nat.mod_lt _ hv2
  clear hBm hIV hIVj hMr hlwj hlw0 hlw1 hlw2 hxs hpw hy0 hlenj l0 l1 l1' l2
  subst hMd
  janus64_run [hsp, h14, hfs, hdf, hx15, hz136, hz168, hz200, hsp0] until [segAddr Extracted.program fn + 0xbbd]
    calls [hP := hExp]
  obtain ⟨⟨⟨h4m, h5m, h14m, hxm⟩, hfsm, hdfm, hr0m, hpost⟩, hrgm⟩ := hP
  exact c2B impl hap R stkM aboveM hBy hsv b L c p len cp ret hret s hx0 hdf0 Q W henvW0 hW hW1 hab ha8 hglob L1 b1 T
    hrel0 hk _ _ _ 6639357 6639365 _ _ (fun t h4 hm h14t hfst => hIP t h4 (hm.trans (by janus64_simp [hsp0])) h14t hfst)
    (by janus64_simp) (by janus64_simp [hsp0]) (by janus64_simp [h14]) (by janus64_simp [hfs]) hpost hrgm
    (by janus64_simp [h4m]) (by janus64_simp [h5m]) (by janus64_simp [h14m, h14]) (by janus64_simp [hxm, hx15])
    (by janus64_simp [hfsm, hfs]) (by janus64_simp [hdfm, hdf]) (by rw [hr0m]; janus64_simp [hsp, hz136])
    (Or.inr ⟨by janus64_simp, rfl⟩) hv hvlt hBB hbfin

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run

theorem le_or_left' {a b c : Nat} (h : a ≤ b) : a ≤ b ||| c := Nat.le_trans h Nat.left_le_or
theorem le_or_right' {a b c : Nat} (h : a ≤ c) : a ≤ b ||| c := Nat.le_trans h Nat.right_le_or
theorem smear_le_left {a : Nat} {b c : BitVec 64} (h : a ≤ b.toNat) : a ≤ (b ||| c).toNat := by
  rw [BitVec.toNat_or]; exact le_or_left' h
theorem smear_le_right_shr {a : Nat} {b c : BitVec 64} {k : Nat} (h : a ≤ c.toNat) : a ≤ (b >>> k ||| c).toNat := by
  rw [BitVec.toNat_or]; exact le_or_right' h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `C2` with `base ≠ 1`: `base.BitLen() ≠ 1` (len `0`: `JL` taken, bit length `0`; else the top limb's bit length
via `BSR` of its smear, `blr_one64`), to the exp block, then `c2eX`. -/
theorem c2e (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : RunIface.ExpSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (Q : Janus.Amd64.Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144)
    (ha8 : 8 ≤ aboveM)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 14).toNat + 16) 8 L)
    (hfL : ApartAll (s.fsBase.toNat - 8) 8 L)
    (hbB : okB s p len ≤ b)
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 3 (cstD 3) L1 b1 T)
    (hpc : T.rip = BitVec.ofNat 64 pcC2) (hv0 : opV s p len 0 ≠ 1) (hv2 : 0 < opV s p len 2)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.rip = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have hX := c2eX impl hap R stkM aboveM hE hBy hsv b L c p len cp ret hret s hx0 hdf0 Q W henvW hW hW1 hab ha8 hglob
    hgL hfL hbB L1 b1
  have hrel0 := hrel
  have hb' : W ≤ (s.regs 4).toNat := by have := henvW.2.1.1; simpa only [regSP] using this
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hMF, -, hop, -⟩ := hrel
  simp only [stk] at hMF
  obtain ⟨-, hval0, hnorm0, h1280, hlc0, hlive0⟩ := hop 0 (by omega)
  clear hop
  simp only [opAt, natAt, show (s.regs 4).toNat - 136 - 32 * 0 + 8 = (s.regs 4).toNat - 128 by omega,
    show (s.regs 4).toNat - 128 + 8 = (s.regs 4).toNat - 120 by omega,
    show (s.regs 4).toNat - 136 - 32 * 0 + 16 = (s.regs 4).toNat - 120 by omega,
    show (s.regs 4).toNat - 136 - 32 * 0 + 24 = (s.regs 4).toNat - 112 by omega] at hval0 hnorm0 h1280 hlc0 hlive0
  generalize hmpd : T.mem.readLE ((s.regs 4).toNat - 128) 8 = mp at hval0 hnorm0 hlive0
  generalize hmld : T.mem.readLE ((s.regs 4).toNat - 120) 8 = ml at hval0 hnorm0 h1280 hlc0
  have hcont : ∀ T' : State, T'.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0xb9b) → T'.mem = T.mem →
      T'.regs 4 = T.regs 4 → T'.regs 14 = T.regs 14 → T'.regs 5 = T.regs 5 → T'.xmm 15 = T.xmm 15 →
      T'.fsBase = T.fsBase → T'.df = T.df → Reaches ((LibRun.program.link impl).withExit ret) T' Q :=
    fun T' h1 h2 h3 h4 h5' h6 h7 h8 => hX T' (RelD.congr hrel0 h2 h3 h4 h5' h6 h7 h8) h1 hv2 hk
  rcases Nat.eq_zero_or_pos ml with h0 | hml1
  · -- `len(base.abs) = 0`: `bitLen` is `0`
    subst h0
    janus64_run [hsp, hmld, msb_allones, msb_m1'] until [segAddr Extracted.program fn + 0xb9b]
    exact hcont _ (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp)
  · have hq := msb_sub_one_le64 ml hml1 (by omega)
    obtain ⟨-, -, hpacc, hp48, -, -⟩ := hlive0 (by omega)
    have hA : T.mem.accessible mp (8 * ml) false = true := by
      rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_read_of_write _
        (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
    have ht : T.mem.readLE (mp + 8 * (ml - 1)) 8 ≠ 0 := hnorm0.resolve_left (by omega)
    have ht' : T.mem.readLE (mp + ml * 8 - 8) 8 ≠ 0 := by
      rwa [show mp + ml * 8 - 8 = mp + 8 * (ml - 1) by omega]
    janus64_run [hsp, hmpd, hmld, hq] until [segAddr Extracted.program fn + 0xb1c]
    gen_reg 2 as x with hXd
    have hx : x.toNat ≠ 0 := by
      rw [← hXd]
      first
        | exact top_ne64 ht'
        | exact top_ne64 ht
        | (simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)]; first | exact ht' | exact ht)
    janus64_run until [segAddr Extracted.program fn + 0xb5b]
    gen_reg 9 as y with hY
    have hy : (y.toNat = 0) = False := by
      rw [← hY]; simp only [eq_iff_iff, iff_false]
      repeat (first | apply bv_or_ne_right_shr | apply bv_or_ne_left)
      exact hx
    janus64_run [hy] until [segAddr Extracted.program fn + 0xb76]
    gen_reg 2 as bl with hBl
    have hxy : x.toNat ≤ y.toNat := by
      rw [← hY]
      repeat (first | apply smear_le_right_shr | apply smear_le_left)
      exact Nat.le_refl _
    have hx1y : x.toNat = 1 → y.toNat = 1 := fun h => by
      have := BitVec.eq_of_toNat_eq (y := 1#64) h; subst this; rw [← hY]; decide
    have hbl1 : bl.toNat ≠ 1 := by
      intro h1
      rw [← hBl] at h1
      obtain ⟨hm1, hx1⟩ := (blr_one64 x.toNat y.toNat ml (Nat.pos_of_ne_zero hx) hxy hx1y
        y.isLt hml1 (by omega)).1 h1
      subst hm1
      rw [← hXd] at hx1
      apply hv0
      rw [← hval0, natVal_succ, natVal_zero]
      first
        | (simp only [BitVec.toNat_ofNat] at hx1; rw [Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)] at hx1;
           simpa using hx1)
        | simpa using hx1
    have hb1 : (bl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro h; apply hbl1; rw [h]; rfl
    janus64_run [hb1] until [segAddr Extracted.program fn + 0xb9b]
    exact hcont _ (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp)

end FvModexp.Amd64.Run
