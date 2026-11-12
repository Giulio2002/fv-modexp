import FvModexp.Proofs.Amd64.Nat.NatAdd0Defs

set_option autoImplicit false

/-! # `nat.add` (amd64), empty-tolerant: the self-call `z.add(y, x)` under `PreS0` (`preS0_swap`, `postS_swap0`,
`postR_swap0`; twin of `FvModexp.Arm64.NatAdd.preS0_swap`). Omega-heavy CallEnv part proved with the guarded
operand facts cleared (with them in context omega's preprocessing blew up on arm64). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatAdd

set_option maxRecDepth 20000 in
theorem preS0_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s S1 : State}
    (hpre : PreS0 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
    (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hF : MemFrame s.mem S1.mem (win s 4440 80)) (hreg : S1.mem.regions = s.mem.regions) :
    PreS0 4288 R b L zp zc yp yl yc xp xl xc S1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨htg, htr, htw⟩⟩, hty, hxc, hyc, hxc40,
    hyc40, hx40, hy40, hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, hyn, hxw, hyacc, hy48, hyh, hyw, hinv, hok, hmv⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have e152 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have htw' := htw
  unfold Apart at hga htw'
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw hzw'
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4440 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4440 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hnorm : ∀ p n, (0 < n → (p + 8 * n ≤ (s.regs 4).toNat - 4440 ∨ (s.regs 4).toNat + 80 ≤ p)) →
      NatNorm s.mem p n → NatNorm S1.mem p n := by
    intro p n ho hn
    rcases hn with h0 | h0
    · exact Or.inl h0
    · by_cases hn0 : n = 0
      · exact Or.inl hn0
      · right; rw [hF.readLE _ _ (hFo _ _ (by have := ho (by omega); omega))]; exact h0
  refine ⟨?ce, hty, hyc, hxc, hyc40, hxc40, hy40, hx40, hz40, ?nl, ?zo, ?za, ?ya, hy48, hyh, ?yn, ?xn, ?yw, ?xa, hx48,
    hxh, ?xw, ?inv, ?ok, ?mv⟩
  case ce =>
    clear hyacc hxacc hy48 hx48 hyh hxh hyw hxw hzw hzl hnorm hok hmv hinv hyn hxn
    refine ⟨⟨by simp only [regG, stackguard0Offset]; rw [h14]; omega,
          by simp only [regG, stackguard0Offset]; rw [h14, hF.accessible]; exact hg2,
          by simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [h14, e152,
            hF.readLE _ _ (hFo _ _ (by omega))]; omega⟩,
        ⟨by simp only [regSP]; rw [e152]; omega, by simp only [regSP]; rw [e152]; omega,
          by simp only [regSP]; rw [e152, hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)⟩,
        by rw [e152]; omega,
        dataLoaded_frame64 hd hreg hro (hF.widen R.rt) (fun r hr _ => by
          simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          exact Janus.Arm64.Memory.accessible_mono _ hw (by simp) (by simp; omega)),
        by rw [e152]; exact hout.of_sub (by omega) (by omega), by rw [e152, h14]; unfold Apart; omega,
        by rw [h14]; exact hgr, fun r hr => ?_, hro,
        ⟨⟨by rw [hfs]; exact htg.base, by rw [hfs, hF.accessible]; exact htg.readable,
          by simp only [regG]; rw [hfs, h14, hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g⟩,
         by rw [hfs]; exact htr, by rw [hfs, e152]; unfold Apart; omega⟩⟩
    · have := hLs r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [e152]; omega
  case nl =>
    intro hc
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  case zo => simp only [win, outside_cons, outside_nil, and_true]; rw [e152]; omega
  case za =>
    intro hc
    obtain ⟨hzg, hzf, hzx, hzy⟩ := hzw hc
    exact ⟨by rw [h14]; exact hzg, by rw [hfs]; exact hzf, hzy, hzx⟩
  case ya => intro h; rw [hF.accessible]; exact hyacc h
  case yn => exact hnorm _ _ (fun h => by have := hyw h; omega) hyn
  case xn => exact hnorm _ _ (fun h => by have := hxw h; omega) hxn
  case yw => intro h; have := hyw h; simp only [win, outside_cons, outside_nil, and_true]; rw [e152]; omega
  case xa => intro h; rw [hF.accessible]; exact hxacc h
  case xw => intro h; have := hxw h; simp only [win, outside_cons, outside_nil, and_true]; rw [e152]; omega
  case inv => rw [h14]; exact inv_win hF hout hb' hinv
  case ok => rw [need_comm]; exact hok
  case mv => rw [mx_comm]; exact hmv

/-- an operand's value survives the frame of the self-call (empty: `0` everywhere) -/
theorem natVal_swap0 {s : State} {M : Janus.Arm64.Memory} {p n : Nat} (hF : MemFrame s.mem M (win s 4440 80))
    (ho : 0 < n → (p + 8 * n ≤ (s.regs 4).toNat - 4440 ∨ (s.regs 4).toNat + 80 ≤ p)) :
    natVal M p n = natVal s.mem p n := by
  by_cases hn : n = 0
  · subst hn; rfl
  · refine natVal_frame hF ?_
    have := ho (by omega)
    simp only [win, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
theorem postS_swap0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS0 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
    (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase) (hdf : S1.df = s.df)
    (hF : MemFrame s.mem S1.mem (win s 4440 80))
    (hq : PostS 4288 R b L zp zc yp yl xp xl S1 s') :
    PostS 4440 R b L zp zc xp xl yp yl s s' := by
  have hsp0 : 4440 ≤ (s.regs 4).toNat := by
    have := hpre.1.2.1.1; simpa only [regSP] using this
  have hLs := hpre.1.2.2.2.2.2.2.2.1
  have hxw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have e152 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4440 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4440 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  obtain ⟨hfs', hdf', p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor, hmf, hlf⟩ := hq
  rw [h14] at hinv
  rw [need_comm] at hb
  refine ⟨hfs'.trans hfs, hdf'.trans hdf, p', n', c', h0, h1, h2, ?_, hn, hnc, by rw [mx_comm] at hnm; exact hnm, L', b', hext, hb, hinv,
    hl, hor, hF.trans hmf fun a n ho => ⟨?_, ?_⟩, ⟨fun a n hin hz => ?_⟩⟩
  · rw [hv, natVal_swap0 hF (fun h => by have := hyw h; omega), natVal_swap0 hF (fun h => by have := hxw h; omega),
      Nat.add_comm]
  · simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    exact ho.1.2
  · simp only [outside_append, win, outside_cons, outside_nil, and_true, e152] at ho ⊢
    obtain ⟨⟨hr, hw1⟩, hz⟩ := ho
    exact ⟨⟨hr, by omega⟩, hz⟩
  · rw [hlf.readLE a n hin hz]
    refine hF.readLE a n ?_
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
    simp only [win, outside_cons, outside_nil, and_true]; omega

theorem postR_swap0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS0 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
    (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase) (hdf : S1.df = s.df)
    (hF : MemFrame s.mem S1.mem (win s 4440 80))
    (hq : PostR 4288 R b L zp zc yp yl xp xl S1 s') :
    PostR 4440 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hq, hr, hc⟩ := hq
  refine ⟨postS_swap0 hpre hsp h14 hfs hdf hF hq, fun h => hr (by rw [need_comm]; exact h),
    fun h => hc (by rw [mx_comm]; exact h)⟩

end FvModexp.Amd64.NatAdd
