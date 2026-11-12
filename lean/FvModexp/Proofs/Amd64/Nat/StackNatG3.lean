import FvModexp.Proofs.Amd64.Nat.StackNatCall

/-!
# `(*stack).nat` (amd64): the `memclrNoHeapPointers` call of `slices.Grow` (after `growslice` returned the block
`(p, 8·gc)`) → the join `+0xdd` → `joinW`

Frame slots (offsets from the entry `RSP`; `RSP' = RSP - 0x58`): `-0x30` = len (`0x28(SP')`), `-0x28` = gc (`0x30`),
`-0x20` = nr (`0x38`), `-0x18` = num (`0x40`), `-0x10` = p (`0x48`), `+8` = st, `+16` = n, `-8` = the caller's `RBP`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNat

/-- the return site of the `memclr` call -/
abbrev pMR : Nat := segAddr Extracted.program fn + 0xad

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem g3 (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibStackNat.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15s : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (hpre : Pre R b L 4192 24 st.toNat n.toNat s)
    (hk : stCap s.mem st.toNat < stLen s.mem st.toNat + rnd n.toNat) (p : Nat)
    (hpin : InRanges p (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) R.rt)
    (hp48 : p + 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) ≤ 2 ^ 48)
    (hal8 : p % 8 = 0)
    (hapL : ApartAll p (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) L)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : S.regs 4 = s.regs 4 - 96#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hx15 : S.xmm 15 = s.xmm 15)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false)
    (sret : S.mem.readLE ((s.regs 4).toNat - 96) 8 = pMR)
    (h0 : (S.regs 0).toNat = p + 8 * stCap s.mem st.toNat)
    (h3 : (S.regs 3).toNat = 8 * (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat))
    (hF : MemFrame s.mem S.mem (R.rt ++ win s 4192 24))
    (hLF : LiveFrame s.mem S.mem L [])
    (hpacc : S.mem.accessible p (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) true = true)
    (hinv : R.inv (b - 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))
      (L ++ [(p, p + 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))]) (s.regs 14).toNat
      (view R.rt (L ++ [(p, p + 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))]) S.mem))
    (sra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (sbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (s30 : S.mem.readLE ((s.regs 4).toNat - 48) 8 = stLen s.mem st.toNat)
    (s28 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))
    (s20 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = rnd n.toNat)
    (s10 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = p)
    (sst : S.mem.readLE ((s.regs 4).toNat + 8) 8 = st.toNat) (sn : S.mem.readLE ((s.regs 4).toNat + 16) 8 = n.toNat) :
    ReachesRet (LibStackNat.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostL R b L 4192 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  have hgcl := le_growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)
  have hgcb := growCap_lt (stLen s.mem st.toNat) n.toNat (stCap s.mem st.toNat) hk (by omega)
  have hgcc := growRound_le_cost (stLen s.mem st.toNat) n.toNat (stCap s.mem st.toNat) hk
  generalize growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) = gc at *
  have hpw := hpin.apart hout
  unfold Apart at hpw
  have hsp96 : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hFw : MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)]) := hF
  refine ReachesRet.call (hmc _ _) hpc (mcall_pre hpre hk S hFw (by omega) h14 (by rw [hsp96, sret]; decide)
    (by rw [hx15, hx15s]) hdf rfl hgcl hpin hp48 hpacc hinv h0 h3) ?_
  intro S3 hpc3 ⟨junk, f3, x3, yh3, m3, zh3, kr3, hs3, hMF3, hLF3, hinv3, _⟩
  subst hs3
  simp only [calleeStack64, hsp96, h0, h3] at hMF3 hLF3
  have hrd : ∀ a, ((s.regs 4).toNat - 48 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 24) →
      m3.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    refine hMF3.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
    have := (hpin.sub (a := p + 8 * stCap s.mem st.toNat)
      (n := 8 * (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat)) (by omega) (by omega)).apart
      (hout.of_sub (a := a) (n := 8) (by omega) (by omega))
    unfold Apart at this; omega
  have r30 := (hrd _ (by omega)).trans s30
  have r28 := (hrd _ (by omega)).trans s28
  have r20 := (hrd _ (by omega)).trans s20
  have r10 := (hrd _ (by omega)).trans s10
  have rst := (hrd _ (by omega)).trans sst
  have rn := (hrd _ (by omega)).trans sn
  have rra := (hrd _ (by omega)).trans sra
  have rbp := (hrd _ (by omega)).trans sbp
  have hret : retAddrOf S = BitVec.ofNat 64 pMR := by
    simp only [retAddrOf, hsp96, sret]
  have hsp88 : (s.regs 4 - 96#64 + 8#64).toNat = (s.regs 4).toNat - 88 := by
    rw [← hsp, BitVec.toNat_add, hsp96]; simp only [BitVec.toNat_ofNat]; omega
  rw [hret] at hpc3
  janus64_run [r30, r28, r20, r10, rst, rn, hsp88, hsp, h5] until [pJ]
  have hLs1 : LiveSep (L ++ [(p, p + 8 * gc)]) (win s 4192 24) := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [win, outside_cons, outside_nil, and_true]; omega
  have hext : LiveExt R L (L ++ [(p, p + 8 * gc)]) :=
    ⟨[(p, p + 8 * gc)], rfl, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]; exact ⟨hpin, hapL⟩,
      List.pairwise_singleton _ _⟩
  have hJ : J R b L st.toNat n.toNat s (L ++ [(p, p + 8 * gc)]) (b - 8 * gc) p gc m3 := by
    refine ⟨hpre, hra, rra, rbp, ?_, ?_, hext, by omega, by rw [← h14]; exact hinv3, ?_, hgcl, hgcb, by omega,
      fun h => absurd h (by omega), fun _ => ⟨hpin, hapL⟩, hLs1, ?_, hdf0,
      fun _ => List.mem_append_right _ (List.mem_singleton_self _)⟩
    · refine hF.trans hMF3 fun a k ho => ⟨ho, ?_⟩
      simp only [wJ, win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hrt, h1⟩ := ho
      refine ⟨⟨hrt, by omega, by omega⟩, ?_⟩
      have := (hpin.sub (a := p + 8 * stCap s.mem st.toNat)
        (n := 8 * (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat)) (by omega) (by omega)).apart hrt
      unfold Apart at this; omega
    · refine ⟨fun a k hin _ => ?_⟩
      rw [hLF3.readLE a k (hext.inRanges_old hin) ?_, hLF.readLE a k hin trivial]
      simp only [outside_cons, outside_nil, and_true]
      have := hapL.apart_of_inRanges hin; omega
    · intro _
      exact ⟨hal8, Or.inl ⟨(p, p + 8 * gc), List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
        by simp only; omega⟩, by rw [← hF.accessible]; exact hpacc, hp48⟩
    · intro _; simp only [win, outside_cons, outside_nil, and_true]; omega
  refine joinW impl R hwb b L st n s _ _ p gc m3 hJ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, hsp, h5, h14, hx15, hfs]
  all_goals first
    | (janus64_simp; done)
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | skip

end FvModexp.Amd64.StackNat
