import FvModexp.Proofs.Amd64.NatQ.DrsPro1
import FvModexp.Proofs.Amd64.NatQ.DrsDefs
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the epilogues and the post of a frame-only path

The three short returns `ADDQ $0x180, SP; POPQ BP; RET` at `0x5ef9ff` (`len u < n`), `0x5efa1b` (after `divBasic`),
`0x5efa32` (after `clear(z)`); `post_frame`: a path that writes only its own frame (`fw s`) and leaves `z = U/V`,
`u = U mod V` already in place satisfies `DrsPostW` (no allocation, same stack, same live set).
Twin of Arm64/NatQ/DrsFin.lean.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- a range outside the window is outside the frame's own writes -/
theorem fw_out {s : State} {W a n : Nat} (hW : 400 ≤ W) (h : Outside a n (win s W 96)) : Outside a n (fw s) := by
  simp only [win, fw, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxHeartbeats 4000000 in
/-- **the post of a frame-only path** (pure) -/
theorem post_frame {R : RtInv} {b Hq : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s s' : State} (hpre : DrsPreW R b L Hq c W qp ql qc st up ul uc vp vl vc s) (hW : 400 ≤ W)
    (hF : MemFrame s.mem s'.mem (fw s)) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hq : natVal s.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl)
    (hu : natVal s.mem up ul = natVal s.mem up ul % natVal s.mem vp vl) :
    DrsPostW R b L Hq c W qp ql st up ul vp vl s s' := by
  have hce := hpre.ce
  have hqo := hpre.qa
  have huo := hpre.ua
  have hsti := hpre.sti
  have hcq := hpre.cost
  have hinv := hpre.inv
  obtain ⟨-, -, -, -, hout, -, -, hLs, -⟩ := hce
  have hst := hsti.2.1
  have e0 : stW s'.mem st = stW s.mem st := hF.readLE _ _ (fw_out hW (hst.of_sub (Nat.le_refl _) (by omega)))
  have e1 : stLen s'.mem st = stLen s.mem st := hF.readLE _ _ (fw_out hW (hst.of_sub (by omega) (by omega)))
  have e2 : stCap s'.mem st = stCap s.mem st := hF.readLE _ _ (fw_out hW (hst.of_sub (by omega) (by omega)))
  have hrt : ∀ r ∈ fw s, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L := by
    intro r hr
    simp only [fw, win, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  refine ⟨hfs, hdf, ?_, ?_, L, b, ⟨LiveExt.refl R L, by rw [stkR_congr e2]; omega, RtInv.inv_frame' hF hrt hinv⟩,
    ?_, ?_, ?_⟩
  · rw [natVal_frame hF (fw_out hW hqo.2.2.2.1)]; exact hq
  · rw [natVal_frame hF (fw_out hW huo.2.2.2.1)]; exact hu
  · obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, -⟩ := hsti
    refine ⟨⟨⟨h1, h2, by rw [hF.accessible]; exact h3, h4, ?_, by rw [e1, e2]; exact h6, by rw [e2]; exact h7⟩,
      e1, Or.inl ⟨e0, e2⟩⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩
    rw [e0, e2]; intro hc; obtain ⟨a1, a2, a3, a4⟩ := h5 hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · refine hF.mono fun a n ho => ?_
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho
    simp only [fw, win, outside_cons, outside_nil, and_true]
    omega
  · refine ⟨fun a n hin _ => hF.readLE a n ?_⟩
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, outside_cons, outside_nil, and_true] at this ⊢
    omega

/-- the facts at a return of `divRecursiveStep` (entry state `s`, final state `s'`, memory as at the epilogue) -/
@[reducible] def Ret (s : State) (M : Memory) (s' : State) : Prop :=
  Kept s s' ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.mem = M

/-- the three return points of the short paths -/
abbrev epC : Nat := 0x5ef9ff
abbrev epB : Nat := 0x5efa1b
abbrev epZ : Nat := 0x5efa32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `ADDQ $0x180, SP; POPQ BP; RET` at one of the three short-path returns (`Fr`'s register / slot facts, stated
separately so that a state after a runtime call, whose memory frame is wider than `fw s`, can use it) -/
theorem epi (impl : List Amd64.Segment) (s T : State) (e : Nat) (he : e = epC ∨ e = epB ∨ e = epZ)
    (hpc : T.rip = BitVec.ofNat 64 e) (hsp : T.regs 4 = s.regs 4 - 392#64) (h14 : T.regs 14 = s.regs 14)
    (hfs : T.fsBase = s.fsBase) (hdf : T.df = false)
    (hra' : T.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hbp : T.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) (hx : T.xmm 15 = s.xmm 15) (hdf0 : s.df = false)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (h0 : 400 ≤ (s.regs 4).toNat)
    (h48 : (s.regs 4).toNat + 96 ≤ 2 ^ 48)
    (hacc : T.mem.accessible ((s.regs 4).toNat - 8) 16 false = true) (Q : State → Prop)
    (k : ∀ s', Ret s T.mem s' → Q s') :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hspn : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hr1 : T.mem.readLE ((T.regs 4).toNat + 392) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hspn, show (s.regs 4).toNat - 392 + 392 = (s.regs 4).toNat by omega]; exact hra'
  have hr2 : T.mem.readLE ((T.regs 4).toNat + 384) 8 = (s.regs 5).toNat := by
    rw [hspn, show (s.regs 4).toNat - 392 + 384 = (s.regs 4).toNat - 8 by omega]; exact hbp
  have hacc' : T.mem.accessible ((T.regs 4).toNat + 384) 16 false = true := by
    rw [hspn, show (s.regs 4).toNat - 392 + 384 = (s.regs 4).toNat - 8 by omega]; exact hacc
  have hret : retAddrOf s = BitVec.ofNat 64 (s.mem.readLE (s.regs 4).toNat 8) := rfl
  rcases he with rfl | rfl | rfl
  all_goals
    rw [hret]
    janus64_run [hr1, hr2]
    refine k _ ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, rfl⟩
    all_goals try (janus64_simp; done)
    all_goals first | exact hfs | (rw [hdf, hdf0]) | exact hx | skip

/-- **the post of a path that clears `z` by a live runtime call** (pure): the frame `fw s` up to `M0`, then a call whose
written ranges are `R.rt`, its stack `cs` (inside the window) and `z`'s array -/
theorem post_clr {R : RtInv} {b Hq : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s s' : State} {M0 : Memory} {cs : List (Nat × Nat)} (hpre : DrsPreW R b L Hq c W qp ql qc st up ul uc vp vl vc s)
    (hW : 400 ≤ W) (hF : MemFrame s.mem M0 (fw s))
    (hMF : MemFrame M0 s'.mem (R.rt ++ cs ++ [(qp, qp + 8 * ql)])) (hLF : LiveFrame M0 s'.mem L [(qp, qp + 8 * ql)])
    (hcs : ∀ a n, Outside a n (win s W 96) → Outside a n cs) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s'.mem))
    (hq : natVal s'.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl)
    (hu : natVal s.mem up ul = natVal s.mem up ul % natVal s.mem vp vl) :
    DrsPostW R b L Hq c W qp ql st up ul vp vl s s' := by
  have hce := hpre.ce
  obtain ⟨-, -, huh, huo, -⟩ := hpre.ua
  have hqu := hpre.qu
  have hsti := hpre.sti
  obtain ⟨hqs, -⟩ := hpre.sq
  have hcq := hpre.cost
  obtain ⟨-, -, -, -, hout, -, -, hLs, -⟩ := hce
  have hst := hsti.2.1
  have hfw : ∀ a n, Outside a n (win s W 96) → Outside a n (fw s) := fun a n h => fw_out hW h
  have hrd : ∀ a n, Held R L a n → Outside a n (win s W 96) → Apart a n qp (8 * ql) →
      s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh ho hap
    rw [FvModexp.Expmc.held_readLE hh hMF hLF (hcs a n ho)
      (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hap; omega)]
    exact hF.readLE a n (hfw a n ho)
  have hSh := hsti.1.2.1
  have hsq : Apart st 24 qp (8 * ql) := by unfold Apart at hqs ⊢; omega
  have e0 : stW s'.mem st = stW s.mem st :=
    hrd _ _ (hSh.sub (Nat.le_refl _) (by omega)) (hst.of_sub (Nat.le_refl _) (by omega)) (by unfold Apart at hsq ⊢; omega)
  have e1 : stLen s'.mem st = stLen s.mem st :=
    hrd _ _ (hSh.sub (by omega) (by omega)) (hst.of_sub (by omega) (by omega)) (by unfold Apart at hsq ⊢; omega)
  have e2 : stCap s'.mem st = stCap s.mem st :=
    hrd _ _ (hSh.sub (by omega) (by omega)) (hst.of_sub (by omega) (by omega)) (by unfold Apart at hsq ⊢; omega)
  have hacc : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hMF.accessible, hF.accessible]
  refine ⟨hfs, hdf, hq, ?_, L, b, ⟨LiveExt.refl R L, by rw [stkR_congr e2]; omega, hinv⟩, ?_, ?_, ?_⟩
  · have : natVal s'.mem up ul = natVal s.mem up ul := by
      unfold natVal; exact hrd _ _ huh huo (by unfold Apart at hqu ⊢; omega)
    rw [this]; exact hu
  · obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, -⟩ := hsti
    refine ⟨⟨⟨h1, h2, by rw [hacc]; exact h3, h4, ?_, by rw [e1, e2]; exact h6, by rw [e2]; exact h7⟩,
      e1, Or.inl ⟨e0, e2⟩⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩
    rw [e0, e2]; intro hc; obtain ⟨a1, a2, a3, a4⟩ := h5 hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · refine hF.trans hMF fun a n ho => ⟨?_, ?_⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho
      simp only [fw, win, outside_cons, outside_nil, and_true]
      omega
    · simp only [outside_append] at ho ⊢
      refine ⟨⟨ho.1.1.1, hcs a n ho.1.1.2⟩, ?_⟩
      have := ho.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; exact this.1
  · refine ⟨fun a n hin ho => ?_⟩
    simp only [List.cons_append, outside_cons, List.nil_append] at ho
    rw [hLF.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; exact ho.1)]
    refine hF.readLE a n ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, outside_cons, outside_nil, and_true] at this ⊢
    omega

end FvModexp.Amd64.Q.DivRec
