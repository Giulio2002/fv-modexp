import FvModexp.Proofs.Amd64.Nat.NatAddMid

/-!
# `nat.add` (amd64): the self-call `z.add(y, x)` for `len x < len y`, and the stack-size weakenings

`S1` = the callee state at the self-call: `RSP' = RSP - 152` (after `CALL`), the caller's frame push, spills and the
return address in its memory (inside `win s 4440 80`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatAdd

theorem need_comm (xl yl : BitVec 64) : need yl xl = need xl yl := by
  unfold need mx; rw [Nat.min_comm, Nat.max_comm]

theorem mx_comm (xl yl : BitVec 64) : mx yl xl = mx xl yl := by unfold mx; rw [Nat.max_comm]

set_option maxRecDepth 20000 in
theorem preS_mono {stk stk' : Nat} (hk : stk' ≤ stk) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl xc yp yl yc : BitVec 64} {s : State} (h : PreS stk R b L zp zc xp xl xc yp yl yc s) :
    PreS stk' R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨htg, htr, htw⟩⟩, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, hzo, hzw, h10, h11, h12, h13, h14, hxw, h15, h16, h17, hyw, h18⟩ := h
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  unfold Apart at hga htw
  refine ⟨⟨⟨hg1, hg2, by simp only [stackguard0, stackguard0Offset, regG, regSP]; omega⟩,
    ⟨by simp only [regSP]; omega, by simp only [regSP]; omega,
      by simp only [regSP]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)⟩, hal, hd,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgr, fun r hr => ?_, hro,
    ⟨htg, htr, by unfold Apart; omega⟩⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, hzw, h10, h11, h12, h13, h14, ?_,
    h15, h16, h17, ?_, h18⟩
  · have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  · simp only [win, outside_cons, outside_nil, and_true] at hzo ⊢; omega
  · simp only [win, outside_cons, outside_nil, and_true] at hxw ⊢; omega
  · simp only [win, outside_cons, outside_nil, and_true] at hyw ⊢; omega

theorem postS_mono {stk stk' : Nat} (hk : stk ≤ stk') {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl yp yl : BitVec 64} {s s' : State} (hsp : stk' ≤ (s.regs 4).toNat)
    (h : PostS stk R b L zp zc xp xl yp yl s s') : PostS stk' R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hfs, hdf, p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor, hmf, hlf⟩ := h
  refine ⟨hfs, hdf, p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor,
    hmf.mono fun a n h => ?_, hlf⟩
  have e1 : (s.regs 4).toNat - stk' ≤ (s.regs 4).toNat - stk := Nat.sub_le_sub_left hk _
  simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨⟨hr, h1⟩, h3⟩ := h
  exact ⟨⟨hr, by omega⟩, h3⟩

theorem postS_congr {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64}
    {s s2 s3 : State} (h : PostS stk R b L zp zc xp xl yp yl s s2) (h0 : s3.regs 0 = s2.regs 0)
    (h1 : s3.regs 3 = s2.regs 3) (h2 : s3.regs 1 = s2.regs 1) (hm : s3.mem = s2.mem) (hfs : s3.fsBase = s2.fsBase)
    (hdf : s3.df = s2.df) :
    PostS stk R b L zp zc xp xl yp yl s s3 := by
  unfold PostS; rw [h0, h1, h2, hm, hfs, hdf]; exact h

set_option maxRecDepth 20000 in
theorem preS_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s S1 : State}
    (hpre : PreS 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
    (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hF : MemFrame s.mem S1.mem (win s 4440 80)) (hreg : S1.mem.regions = s.mem.regions) :
    PreS 4288 R b L zp zc yp yl yc xp xl xc S1 := by
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
  have hnorm : ∀ p n, (p + 8 * n ≤ (s.regs 4).toNat - 4440 ∨ (s.regs 4).toNat + 80 ≤ p) → NatNorm s.mem p n →
      NatNorm S1.mem p n := by
    intro p n ho hn
    rcases hn with h0 | h0
    · exact Or.inl h0
    · by_cases hn0 : n = 0
      · exact Or.inl hn0
      · right; rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact h0
  refine ⟨⟨⟨by simp only [regG, stackguard0Offset]; rw [h14]; omega,
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
       by rw [hfs]; exact htr, by rw [hfs, e152]; unfold Apart; omega⟩⟩,
    hty, hyc, hxc, hyc40, hxc40, hy40, hx40, hz40,
    fun hc => ?_, by simp only [win, outside_cons, outside_nil, and_true]; rw [e152]; omega,
    fun hc => ?_, by rw [hF.accessible]; exact hyacc, hy48, hyh, hnorm _ _ (by omega) hyn,
    hnorm _ _ (by omega) hxn, by simp only [win, outside_cons, outside_nil, and_true]; rw [e152]; omega,
    by rw [hF.accessible]; exact hxacc, hx48, hxh, by simp only [win, outside_cons, outside_nil, and_true]; rw [e152]; omega,
    by rw [h14]; exact inv_win hF hout hb' hinv, by rw [need_comm]; exact hok,
    by rw [mx_comm]; exact hmv⟩
  · have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [e152]; omega
  · obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  · obtain ⟨hzg, hzf, hzx, hzy⟩ := hzw hc
    exact ⟨by rw [h14]; exact hzg, by rw [hfs]; exact hzf, hzy, hzx⟩

set_option maxRecDepth 20000 in
theorem postS_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
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
  · rw [hv, natVal_frame hF (hFo _ _ (by omega)), natVal_frame hF (hFo _ _ (by omega)), Nat.add_comm]
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

theorem postR_mono {stk stk' : Nat} (hk : stk ≤ stk') {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl yp yl : BitVec 64} {s s' : State} (hsp : stk' ≤ (s.regs 4).toNat)
    (h : PostR stk R b L zp zc xp xl yp yl s s') : PostR stk' R b L zp zc xp xl yp yl s s' :=
  ⟨postS_mono hk hsp h.1, h.2⟩

theorem postR_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
    (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase) (hdf : S1.df = s.df)
    (hF : MemFrame s.mem S1.mem (win s 4440 80))
    (hq : PostR 4288 R b L zp zc yp yl xp xl S1 s') :
    PostR 4440 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hq, hr, hc⟩ := hq
  refine ⟨postS_swap hpre hsp h14 hfs hdf hF hq, fun h => hr (by rw [need_comm]; exact h),
    fun h => hc (by rw [mx_comm]; exact h)⟩

theorem postR_congr {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64}
    {s s2 s3 : State} (h : PostR stk R b L zp zc xp xl yp yl s s2) (h0 : s3.regs 0 = s2.regs 0)
    (h1 : s3.regs 3 = s2.regs 3) (h2 : s3.regs 1 = s2.regs 1) (hm : s3.mem = s2.mem) (hfs : s3.fsBase = s2.fsBase)
    (hdf : s3.df = s2.df) :
    PostR stk R b L zp zc xp xl yp yl s s3 := by
  unfold PostR PostS; rw [h0, h1, h2, hm, hfs, hdf]; exact h

theorem postX_mono {stk stk' : Nat} (hk : stk ≤ stk') {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl yp yl : BitVec 64} {s s' : State} (hsp : stk' ≤ (s.regs 4).toNat)
    (h : PostX stk R b L zp zc xp xl yp yl s s') : PostX stk' R b L zp zc xp xl yp yl s s' := by
  refine ⟨postR_mono hk hsp h.1, h.2.1.mono fun a n h => ?_, h.2.2⟩
  have e1 : (s.regs 4).toNat - stk' ≤ (s.regs 4).toNat - stk := Nat.sub_le_sub_left hk _
  simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨⟨hr, h1⟩, h3⟩ := h
  exact ⟨⟨hr, by omega⟩, h3⟩

set_option maxRecDepth 20000 in
theorem postX_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s S1 s' : State} (hpre : PreS 4440 R b L zp zc xp xl xc yp yl yc s) (hsp : S1.regs 4 = s.regs 4 - 152#64)
    (h14 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase) (hdf : S1.df = s.df)
    (hF : MemFrame s.mem S1.mem (win s 4440 80))
    (hq : PostX 4288 R b L zp zc yp yl xp xl S1 s') :
    PostX 4440 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hq, hmf, hlf⟩ := hq
  have hsp0 : 4440 ≤ (s.regs 4).toNat := by
    have := hpre.1.2.1.1; simpa only [regSP] using this
  have hLs := hpre.1.2.2.2.2.2.2.2.1
  have e152 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have em : max yl.toNat xl.toNat = max xl.toNat yl.toNat := Nat.max_comm _ _
  rw [em] at hmf hlf
  refine ⟨postR_swap hpre hsp h14 hfs hdf hF hq, hF.trans hmf fun a n ho => ⟨?_, ?_⟩, ⟨fun a n hin hz => ?_⟩⟩
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

theorem postX_congr {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64}
    {s s2 s3 : State} (h : PostX stk R b L zp zc xp xl yp yl s s2) (h0 : s3.regs 0 = s2.regs 0)
    (h1 : s3.regs 3 = s2.regs 3) (h2 : s3.regs 1 = s2.regs 1) (hm : s3.mem = s2.mem) (hfs : s3.fsBase = s2.fsBase)
    (hdf : s3.df = s2.df) :
    PostX stk R b L zp zc xp xl yp yl s s3 := by
  unfold PostX PostR PostS; rw [h0, h1, h2, hm, hfs, hdf]; exact h

end FvModexp.Amd64.NatAdd
