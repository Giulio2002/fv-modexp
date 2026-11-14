import FvModexp.Proofs.Amd64.Nat.DivFreeS

set_option autoImplicit false

/-!
# `nat.expNN.deferwrap1` (amd64) with the `StkSh` pool shape (agent expmc s73; twin of Arm64/Exp/NFree.lean)

`sumS`: Amd64/Nat/Free.lean's `sum` for the `Put` contract with the shared pooled-stack shape `StkSh` (the shape the
Run rows' `Get`/`Put` hypotheses use): precondition `Free.PreS` (Amd64/Nat/DivFreeS.lean: `Pre … (2^40 - 1)` plus
`cap = 0 → ptr = 0` of the captured header); the closure's `len := 0` store then gives `StkSh` at the `Put`. Same proof
as top's `sumDS` (adapted from Amd64/Nat/DivFreeS.lean) on `LibFree.program`, return from `Put` at `0x5e7a0d`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool
  Janus.Contracts.PoolAmd64

namespace FvModexp.Amd64.Free

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sumS (impl : List Amd64.Segment) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R stkT FvModexp.StkSh)
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibFree.program.link impl) (segAddr Extracted.program fn) (PreS R b L rs) (Post R b L rs) := by
  intro s hpc ⟨⟨hg1, hg2, hg3, hal, ha, hw, hra, hc1, hc2, hca, hsh, hsw, hsg, hgw, hgr, hrs, hok, hinv, hLs, hout⟩, hc0⟩
  have hca' := hca; have hsw' := hsw; have hsg' := hsg; have hgw' := hgw
  unfold Apart at hca' hsw' hsg' hgw'
  have hsh' := hsh
  obtain ⟨hs0, hs8, hs48, hsacc, -, -, -, -, -, -, -, -⟩ := hsh'
  simp only [stkOf] at hsh hsw' hsg' hs0 hs8 hs48 hsacc
  have hacc8 : s.mem.accessible (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hsacc (by omega) (by omega)
  have hacc8' : s.mem.accessible ((s.regs 4).toNat - 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  janus64_run [hacc8, hacc8'] until [cA "sync.(*Pool).Put"]
  generalize hM1 : ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 0).writeLE ((s.regs 4).toNat - 40) 8 6191629 = M1
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF1 : MemFrame s.mem M1 [((s.regs 4).toNat - 8, (s.regs 4).toNat),
      (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8, s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16),
      ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] := by
    rw [← hM1]; janus_frame
  have hk1 : ∀ a n, (a + n ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) →
      (a + n ≤ s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8 ∨ s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 32 ≤ a) →
      M1.readLE a n = s.mem.readLE a n := fun a n h1 h2 h3 =>
    hF1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hlen0 : M1.readLE (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 = 0 := by
    rw [← hM1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have hret : M1.readLE ((s.regs 4).toNat - 40) 8 = 6191629 := by
    rw [← hM1, Janus.Arm64.Memory.readLE_writeLE_self]
  have hhdr : (s.mem.readLE ((s.regs 2).toNat + 8) 8, s.mem.readLE ((s.regs 2).toNat + 8) 8 + 24) ∈ L := by
    apply hrs; have h' := hsh; unfold SliceObj at h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e⟩ := h'
    rw [e]; exact List.mem_cons_self
  have hinv1 : R.inv b L (s.regs 14).toNat (view R.rt L M1) := by
    refine RtInv.inv_frame' hF1 (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · right; exact ⟨_, hhdr, by simp only; omega, by simp only; omega⟩
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  have hsh1 : FvModexp.StkSh M1 (s.mem.readLE ((s.regs 2).toNat + 8) 8) rs := by
    refine ⟨sliceObj_len0 hsh hF1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega) hlen0, hlen0, ?_⟩
    rw [hk1 _ _ (by omega) (by omega) (by omega), hk1 _ _ (by omega) (by omega) (by omega)]
    simp only [stkOf] at hc0; exact hc0
  refine ReachesRet.call (hput L b rs) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩,
    ?_, ?_, hrs, ?_, ?_, ?_, ?_, ?_⟩ ?_
  all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40]
  case refine_2 => omega
  case refine_3 => omega
  case refine_4 => omega
  case refine_5 =>
    rw [← hM1]; simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  case refine_6 => omega
  case refine_7 => rw [← hM1]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hg2
  case refine_8 => rw [hk1 _ _ (by omega) (by omega) (by omega)]; omega
  case refine_9 =>
    simp only [calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, outside_cons, outside_nil, and_true]
    omega
  case refine_11 => rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsh1
  case refine_12 => exact hok
  case refine_13 => exact hinv1
  case refine_14 => exact Nat.zero_le _
  case refine_15 =>
    intro r hr; have := hLs r hr
    simp only [liveWin64, calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, List.cons_append,
      List.nil_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  case refine_16 =>
    intro r hr
    simp only [liveWin64, calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  all_goals first | (janus64_simp; done) | decide | rfl | skip
  intro s2 hpc2 ⟨r, x2, y2, fl, m, zh, kr, hs2, hMF, hLF, hNew, hinv2⟩
  subst hs2
  simp only [calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40] at hMF
  have hkm : ∀ a, ((s.regs 4).toNat - 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 8) → m.readLE a 8 = M1.readLE a 8 :=
    fun a ha => hMF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)
  have r8 : m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hkm _ (by omega), ← hM1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  have r0 : m.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hkm _ (by omega), hk1 _ _ (by omega) (by omega) (by omega)]
  have hra2 : retAddrOf
      { regs := setRegF (setRegF (setRegF (setRegF (setRegF s.regs 0 12107072#64) 1
                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 2) + 8) 8))) 3 7434400#64)
            4 (s.regs 4 - 40#64)) 5 (s.regs 4 - 8#64),
        rip := 4789440#64, flags := (subFlags (s.regs 4 - 8#64) (24#64) false).snd, xmm := s.xmm, mem := M1,
        ymmHi := s.ymmHi, fsBase := s.fsBase, df := s.df, mxcsr := s.mxcsr, x87 := s.x87, fpucw := s.fpucw,
        zmmHi := s.zmmHi, kreg := s.kreg : State } = 6191629#64 := by
    simp only [retAddrOf, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, hret]
  rw [hra2]
  janus64_run [r8, r0, hsp40]
  refine ⟨⟨?_, ?_, ?_, ?_, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, MapAmd64.keepABI_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · simp only [MapAmd64.keepX15_apply, ↓reduceIte]
  · refine hF1.trans hMF fun a k ho => ?_
    simp only [stkOf, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1, h2⟩ := ho
    exact ⟨⟨by omega, h2, by omega⟩, hrt, by omega, by omega⟩
  · refine ⟨fun a k hin hws => ?_⟩
    simp only [stkOf, outside_cons, outside_nil, and_true] at hws
    obtain ⟨r0, hr0, i1, i2⟩ := hin
    have := hLs r0 hr0
    simp only [outside_cons, outside_nil, and_true] at this
    rw [hLF.readLE a k ⟨r0, hr0, i1, i2⟩ trivial,
      hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, hws, by omega⟩)]
  · exact hinv2

end FvModexp.Amd64.Free
