import FvModexp.Proofs.Amd64.Top.RunC2RA
import FvModexp.Proofs.Amd64.Top.RunC2Lem
import FvModexp.Proofs.Amd64.Top.RunC2B
import FvModexp.Proofs.Amd64.Top.RunC2One

set_option autoImplicit false

/-! # `Run` (amd64): `C2` to `V` when `base = 1` (`base.BitLen() == 1`): `v = base.Mod(base, mod).Bytes()`

`C2` = `fn + 0xafe`: `base.BitLen()` (len slot `e - 120`, pointer `e - 128`; `BSRQ` of the smeared top limb), `= 1` →
`Mod(&base, &base, &mod)` (call `fn + 0xb8f`, return `fn + 0xb94`), `Bytes(z)` (call `fn + 0xb94`, return `fn + 0xb99`),
`JMP V`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

open Janus.Arm64 in
theorem clz_one : clzNat 64 1 = 63 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c2m (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hM : RunIface.ModSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (Q : Janus.Amd64.Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144)
    (ha8 : 8 ≤ aboveM)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 14).toNat + 16) 8 L)
    (hfL : ApartAll (s.fsBase.toNat - 8) 8 L)
    (hbB : okB s p len ≤ b) (hpool : FvModexp.Spec.RunAmd64.StackPool R s.mem (win s W 40))
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 3 (cstD 3) L1 b1 T)
    (hpc : T.rip = BitVec.ofNat 64 pcC2)
    (hv0 : opV s p len 0 = 1) (hv2 : 0 < opV s p len 2)
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
  -- the base operand is the one-limb nat `1`
  obtain ⟨hneg0, hval0, hnorm0, h1280, hlc0, hlive0⟩ := hop 0 (by omega)
  simp only [opAt, natAt, show (s.regs 4).toNat - 136 - 32 * 0 + 8 = (s.regs 4).toNat - 128 by omega,
    show (s.regs 4).toNat - 128 + 8 = (s.regs 4).toNat - 120 by omega,
    show (s.regs 4).toNat - 136 - 32 * 0 + 16 = (s.regs 4).toNat - 120 by omega,
    show (s.regs 4).toNat - 136 - 32 * 0 + 24 = (s.regs 4).toNat - 112 by omega] at hneg0 hval0 hnorm0 h1280 hlc0 hlive0
  rw [hv0] at hval0
  obtain ⟨hn1, hx1⟩ := natVal_eq_one hnorm0 hval0
  obtain ⟨-, -, hb0acc, hb048, -, -⟩ := hlive0 (by omega)
  have hA : T.mem.accessible (T.mem.readLE ((s.regs 4).toNat - 128) 8) 8 false = true := by
    rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_read_of_write _
      (Janus.Arm64.Memory.accessible_mono _ hb0acc (Nat.le_refl _) (by omega))
  -- the Mod call: IntPre outside the run
  have hxs : ∀ a ∈ [(s.regs 4).toNat - 136, (s.regs 4).toNat - 200], ∃ j, j < 3 ∧ a = opAt s j := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, by omega, by simp only [opAt]; omega⟩
    · exact ⟨2, by omega, by simp only [opAt]; omega⟩
  have hpw : [(s.regs 4).toNat - 136, (s.regs 4).toNat - 200].Pairwise
      fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j := by
    refine List.Pairwise.cons (fun a' ha' => ?_) (List.pairwise_singleton _ _)
    simp only [List.mem_singleton] at ha'; subst ha'
    exact ⟨0, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
  have l0 : RunIface.lenW T.mem ((s.regs 4).toNat - 136) ≤ wMax s p len :=
    Nat.le_trans (lenW_op0 (hop 0 (by omega))) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have l2 : RunIface.lenW T.mem ((s.regs 4).toNat - 200) ≤ wMax s p len :=
    Nat.le_trans (lenW_op2 (hop 2 (by omega))) (Nat.le_max_right _ _)
  -- the memory at `Mod`'s entry: the return address pushed at `e - 616`
  generalize hMd : T.mem.writeLE ((s.regs 4).toNat - 616) 8 6639316 = M
  have hMr : ∀ j, j < 3 → ∀ o, o + 8 ≤ 32 → M.readLE (opAt s j + o) 8 = T.mem.readLE (opAt s j + o) 8 := by
    intro j hj o ho; rw [← hMd]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp only [opAt]; omega)
  have hlw0 : RunIface.lenW M ((s.regs 4).toNat - 136) = RunIface.lenW T.mem ((s.regs 4).toNat - 136) := by
    have := hMr 0 (by omega) 16 (by omega); simp only [opAt, Nat.mul_zero, Nat.sub_zero] at this
    simp only [RunIface.lenW]; exact this
  have hlw2 : RunIface.lenW M ((s.regs 4).toNat - 200) = RunIface.lenW T.mem ((s.regs 4).toNat - 200) := by
    have := hMr 2 (by omega) 16 (by omega)
    simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at this
    simp only [RunIface.lenW]; exact this
  have hBm : RunIface.ModBudget (max (RunIface.lenW M ((s.regs 4).toNat - 136))
      (RunIface.lenW M ((s.regs 4).toNat - 200))) ≤ b1 := by
    rw [hlw0, hlw2]
    have hbB' := hbB
    simp only [okB, callB] at hbB'
    have := budget_mod (w := wMax s p len) (lb := 0) l0 l2 (Nat.zero_le _) hbud hbB'
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
  have hy0 : 0 < RunIface.IntV M ((s.regs 4).toNat - 200) := by
    have := hIV 2 (by omega)
    simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at this
    rw [this, intV_eq]
    obtain ⟨-, hval2, -⟩ := hop 2 (by omega)
    simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at hval2
    rw [hval2]; exact hv2
  have hzl : RunIface.IntLenLe M ((s.regs 4).toNat - 136) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW
    have := hMr 0 (by omega) 16 (by omega); simp only [opAt, Nat.mul_zero, Nat.sub_zero] at this
    rw [this, show (s.regs 4).toNat - 136 + 16 = (s.regs 4).toNat - 120 by omega]; exact h1280
  have hyl : RunIface.IntLenLe M ((s.regs 4).toNat - 200) RunIface.maxW := by
    unfold RunIface.IntLenLe RunIface.maxW
    have := hMr 2 (by omega) 16 (by omega)
    simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at this
    rw [this]; exact (hop 2 (by omega)).2.2.2.1
  have hIP : ∀ t : State, t.regs 4 = T.regs 4 - 8#64 → t.mem = M → t.regs 14 = s.regs 14 → t.fsBase = s.fsBase →
      RunIface.IntPre R b1 (RunIface.ModBudget (max (RunIface.lenW M ((s.regs 4).toNat - 136))
        (RunIface.lenW M ((s.regs 4).toNat - 200)))) L1 stkM aboveM [(s.regs 4).toNat - 136, (s.regs 4).toNat - 200] t := by
    intro t h4 hm h14' hfs'
    have h0 := intPre_ops (T := { t with mem := T.mem }) (M := T.mem) _ (by simp only; rw [h4]; exact hsp0) rfl
      (by simp only; exact h14') (by simp only; exact hfs') henvW0 hW hW1 hab ha8 hglob hgL hfL hsv hBm hdS hext hinv
      hMF hop hopA hxs hpw
    exact intPre_push h0 ha8 6639316 rfl rfl rfl (by simp only; rw [hm, ← hMd, h4, hsp0])
  have hRA : RetAddr ((Extracted.program.onlySegments RunIface.namesMod).link impl)
      (M.readLE (T.regs 4 - 8#64).toNat 8) := by
    rw [hsp0, ← hMd, Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by decide),
      show (6639316 : Nat) = 0x654340 + 0xb94 by decide]
    exact raMod impl hap
  have hMod := modW impl hap R stkM aboveM hM b1 L1 (T.regs 4 - 8#64) (s.regs 14) s.fsBase M
    ((s.regs 4).toNat - 136) ((s.regs 4).toNat - 200) hRA hIP hy0 hzl hyl
    (fun t h4 => by
      have h0 := poolG_ops (T := t) (M := T.mem) (by rw [h4]; exact hsp0) hW hab hb' hpool hMF hW1
      simp only [win] at h0 ⊢
      rw [← hMd]
      exact poolG_push h0 ⟨by rw [h4, hsp0]; omega, by rw [h4, hsp0]; omega⟩)
  have hz136 : (s.regs 4 - 608#64 + 472#64).toNat = (s.regs 4).toNat - 136 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
  have hz200 : (s.regs 4 - 608#64 + 408#64).toNat = (s.regs 4).toNat - 200 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
  clear hRA
  have hBB : RunIface.ModBudget (max (RunIface.lenW M ((s.regs 4).toNat - 136))
      (RunIface.lenW M ((s.regs 4).toNat - 200))) + RunIface.BytesBudget RunIface.maxW ≤ b1 := by
    rw [hlw0, hlw2]
    have hbB' := hbB
    simp only [okB, callB] at hbB'
    exact budget_mod (w := wMax s p len) l0 l2 (Nat.le_refl _) hbud hbB'
  have hbfin : ∀ b2 b3 lb, lb ≤ RunIface.maxW → b1 - RunIface.ModBudget (max (RunIface.lenW M ((s.regs 4).toNat - 136))
      (RunIface.lenW M ((s.regs 4).toNat - 200))) ≤ b2 → b2 - RunIface.BytesBudget lb ≤ b3 →
      b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ b3 := fun b2 b3 lb hl h2 h3 => by
    rw [hlw0, hlw2] at h2
    unfold callB; exact budget_c2m l0 l2 hl hbud h2 h3
  have hIV0 : RunIface.IntV M ((s.regs 4).toNat - 136) = 1 := by
    have := hIV 0 (by omega); simp only [opAt, Nat.mul_zero, Nat.sub_zero] at this
    rw [this, intV_eq]; simp only [natAt, show (s.regs 4).toNat - 136 + 8 = (s.regs 4).toNat - 128 by omega,
      show (s.regs 4).toNat - 128 + 8 = (s.regs 4).toNat - 120 by omega]; exact hval0
  have hIV2 : RunIface.IntV M ((s.regs 4).toNat - 200) = opV s p len 2 := by
    have := hIV 2 (by omega)
    simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at this
    rw [this, intV_eq]
    obtain ⟨-, hval2, -⟩ := hop 2 (by omega)
    simp only [opAt, show (s.regs 4).toNat - 136 - 32 * 2 = (s.regs 4).toNat - 200 by omega] at hval2
    exact hval2
  have hv : RunIface.IntV M ((s.regs 4).toNat - 136) % RunIface.IntV M ((s.regs 4).toNat - 200) = resV s p len := by
    rw [hIV0, hIV2, resV_eq _ _ _ hv2, hv0, Nat.one_pow]
  have hvlt : RunIface.IntV M ((s.regs 4).toNat - 136) % RunIface.IntV M ((s.regs 4).toNat - 200) < opV s p len 2 := by
    rw [hIV2]; exact Nat.mod_lt _ hv2
  clear hBm hIV hMr hlw0 hlw2 hxs hpw hzl hyl hy0 l0 l2
  subst hMd
  janus64_run [hsp, h14, hfs, hdf, hx15, hn1, hx1, clz_one, hz136, hz200, hsp0] until
    [segAddr Extracted.program fn + 0xb94, segAddr Extracted.program fn + 0xb9b] calls [hP := hMod]
  all_goals try (
    obtain ⟨⟨⟨h4m, h5m, h14m, hxm⟩, hfsm, hdfm, hr0m, hpost, -⟩, hrgm⟩ := hP
    exact c2B impl hap R stkM aboveM hBy hsv b L c p len cp ret hret s hx0 hdf0 Q W henvW0 hW hW1 hab ha8 hglob L1 b1 T
      hrel0 hk _ _ _ 6639316 6639321 _ _ (fun t h4 hm h14t hfst => hIP t h4 (hm.trans (by janus64_simp [hsp0])) h14t hfst)
      (by janus64_simp) (by janus64_simp [hsp0]) (by janus64_simp [h14]) (by janus64_simp [hfs]) hpost hrgm
      (by janus64_simp [h4m]) (by janus64_simp [h5m]) (by janus64_simp [h14m, h14]) (by janus64_simp [hxm, hx15])
      (by janus64_simp [hfsm, hfs]) (by janus64_simp [hdfm, hdf]) (by rw [hr0m]; janus64_simp [hsp, hz136])
      (Or.inl ⟨by janus64_simp, rfl⟩) hv hvlt hBB hbfin)
  all_goals (exact absurd hbr (by decide))

end FvModexp.Amd64.Run
