import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W4ExitS
import FvModexp.Proofs.Common.ExpFinal

/-!
# window-4 (arm64), the final reduction (nat.go:1476-1488) composed

From the entry of the first `zz.cmp(m)` (after `zz = zz.montgomery(z, one, …)`, `W4Exit.exA`) to the join `njoin`:
`cmp < 0` → `exLt`; `cmp ≥ 0` → `exGe`, `exSub` (then `zz = m`, the difference `0`). The value at the join is
`if m ≤ zz then 0 else zz` (= the model's final reduction, as `zz ≤ m`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

theorem inRanges_outside {L : List (Nat × Nat)} {lo hi a k : Nat} (hLs : LiveSep L [(lo, hi)])
    (h : InRanges a k L) : Outside a k [(lo, hi)] := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- `JoinPost` moves back over the first `cmp` -/
theorem JoinPost.pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zzp zzc V p l c : Nat}
    {M M1 M' : Memory} (hf : MemFrame M M1 (cmpF sp)) (hreg : M1.regions = M.regions)
    (hLs : LiveSep L [(sp - 4304, sp + 1040)]) (h4304 : 4304 ≤ sp)
    (h : JoinPost R b L g sp n zzp zzc V M1 p l c M') : JoinPost R b L g sp n zzp zzc V M p l c M' := by
  obtain ⟨L', b', hLE, hb, hinv, hrg, hF, hLF, rest⟩ := h
  refine ⟨L', b', hLE, hb, hinv, hrg.trans hreg, hf.trans hF (fun a k ho => ⟨?_, ho⟩),
    (liveFrame_of_frame' hf ?_).trans hLF (fun _ _ h => h), rest⟩
  · simp only [jw, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · intro a k hin _
    have := inRanges_outside hLs hin
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
where
  liveFrame_of_frame' {m m' : Memory} {L ws rs : List (Nat × Nat)} (h : MemFrame m m' rs)
      (ho : ∀ a k, InRanges a k L → Outside a k ws → Outside a k rs) : LiveFrame m m' L ws :=
    FvModexp.Expmc.liveFrame_of_frame h ho

/-- the top limb of an `n`-limb value -/
theorem top_limb (m : Memory) (p n : Nat) (hn : 0 < n) :
    m.readLE (p + 8 * (n - 1)) 8 = m.readLE p (8 * n) / 256 ^ (8 * (n - 1)) := by
  have e : 8 * n = 8 * (n - 1) + 8 := by omega
  rw [e, Memory.readLE_add]
  have hlt := Memory.readLE_lt m p (8 * (n - 1))
  have hpos : 0 < 256 ^ (8 * (n - 1)) := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem norm_of_eq {m m' : Memory} {p q n : Nat} (h : m.readLE p (8 * n) = m'.readLE q (8 * n))
    (hq : NatNorm m' q n) : NatNorm m p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · exact Or.inl h0
  rcases hq with h0 | h1
  · exact Or.inl h0
  · right
    rw [top_limb m p n hn, h, ← top_limb m' q n hn]; exact h1

theorem readLE_lt64 (m : Memory) (a : Nat) : m.readLE a 8 < 2 ^ 64 := by
  have := Memory.readLE_lt m a 8; simpa using this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the final reduction: from the entry of the first `zz.cmp(m)` to the join `njoin` -/
theorem exB (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat) {ext : List (Nat × Nat)} (M0 : Memory)
    (r18 r29 : BitVec 64)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0) (hce0 : CallW.CEnv R L g sp 4304 1040 M0)
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm0 : NatNorm M0 mp n)
    (S : State) (zp zc zzp zzc : Nat) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 cmpEntry) (h30 : S.regs 30 = BitVec.ofNat 64 cmp1Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h1 : S.regs 1 = BitVec.ofNat 64 n) (h2 : S.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : S.regs 3 = BitVec.ofNat 64 mp) (h4 : S.regs 4 = BitVec.ofNat 64 n) (h5 : S.regs 5 = BitVec.ofNat 64 mc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (hB : Bufs R L g sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 M zp zc zzp zzc)
    (r400 : M.readLE (sp + 400) 8 = zzp) (r160 : M.readLE (sp + 160) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc)
    (hZle : M.readLE zzp (8 * n) ≤ M0.readLE mp (8 * n))
    (KJ : ∀ (S' : State) (p l c : Nat) (M' : Memory), S'.pc = BitVec.ofNat 64 njoinL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 p → S'.regs 4 = BitVec.ofNat 64 l → S'.regs 5 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      JoinPost R b L g sp n zzp zzc
        (if M0.readLE mp (8 * n) ≤ M.readLE zzp (8 * n) then 0 else M.readLE zzp (8 * n)) M p l c M' →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hyl, hyl', hm, hy, hY, hpw, r1016, r1024, r1032, r224, r1000, r992, hok⟩ := hst
  obtain ⟨hF, hLF, hinv, hrg0⟩ := hM
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  obtain ⟨hBz, hBzz, hzzz, hzm, hzzm, hzy, hzzy, hzp, hal8z, hal8zz, hstz, hstzz, hext⟩ := hB
  obtain ⟨hma, hmb, hmh, hmw⟩ := hm
  obtain ⟨hzc1, hzc2, hza, hzb, hzh, hzw, hzg⟩ := hBz
  obtain ⟨hzzc1, hzzc2, hzza, hzzb, hzzh, hzzw, hzzg⟩ := hBzz
  have hLs4 := hce0.2.2.2.2.2.2.2.2.2.2.1
  -- the environment at `M`
  have hceM : CallW.CEnv R L g sp 4304 1040 M := by
    refine CallW.CEnv.frame hce0 (ws := fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)])
      (by simpa only [lw, List.append_assoc] using hF) hrg0 ?_ ?_
    · intro r hr hlt
      simp only [fw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      all_goals first
        | exact M0.accessible_sub hwacc (Or.inr rfl) (by dsimp only; omega) (by dsimp only; omega)
        | (dsimp only; rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact hza)
        | (dsimp only; rw [show zzp + 8 * zzc - zzp = 8 * zzc by omega]; exact hzza)
    · unfold Apart at hgw hzg hzzg
      simp only [fw, outside_append, outside_cons, outside_nil, and_true]
      omega
  have hceM' := hceM
  obtain ⟨_, _, _, haccM, _, hg2M, hg3M, _, _, _, _, _, _⟩ := hceM'
  have FL0 : FL R L sp zp zc zzp zzc M0 M := ⟨hF, hLF⟩
  have eMv : M.readLE mp (8 * n) = M0.readLE mp (8 * n) := FL.read FL0 hmh hmw hsp1 hzm hzzm
  have rdS : ∀ a, sp + 912 ≤ a → a + 8 ≤ sp + 1040 →
      M.readLE a 8 = M0.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    unfold Apart at hzw hzzw
    simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  have r1016M := (rdS (sp + 1016) (by omega) (by omega)).trans r1016
  have r1024M := (rdS (sp + 1024) (by omega) (by omega)).trans r1024
  have r1032M := (rdS (sp + 1032) (by omega) (by omega)).trans r1032
  have tn := toNat_lt (v := n) (by omega)
  have tz := toNat_lt (v := zzp) (by omega)
  have tm := toNat_lt (v := mp) (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt (by omega)
  have hSacc : S.mem.accessible (sp - 24) 64 true = true := by
    rw [hmem]; exact M.accessible_sub haccM (Or.inr rfl) (by omega) (by omega)
  have u1 := hzzw; have u2 := hmw; have u3 := hstzz; have u4 := hmw4; have u5 := hzzg; have u6 := hzzm
  unfold Apart at u1 u2 u3 u4 u5 u6
  refine CmpW.call ((LibWC.cmpSum impl).withExit hret) hpc
    (CmpW.pre_of hsp h28 h30 h0 h1 h3 h4 (by decide) (by decide) hal (by omega) (by omega) hSacc hg1
      (by rw [hmem]; exact hg2M) (by rw [hmem]; omega)
      (Or.inr ⟨by omega, by rw [hmem, hF.accessible]; exact M0.accessible_sub hzza (Or.inr rfl) (Nat.le_refl _) (by omega),
        by unfold Apart; omega⟩)
      (Or.inr ⟨hmb, by rw [hmem, hF.accessible]; exact hma, by unfold Apart; omega⟩)) ?_
  intro S1 hpc1 hsp1' hr0 hr3 hr18 hr28 hr29 hcf hrg1
  rw [h1, h4, h0, h3, hmem, tn, tz, tm, eMv] at hr0
  rw [hmem, tsp] at hcf
  rw [hmem] at hrg1
  rw [h30] at hpc1
  rw [hsp] at hsp1'
  rw [h18] at hr18
  rw [h28] at hr28
  rw [h29] at hr29
  have rdC : ∀ a k, (a + k ≤ sp + 8 ∨ sp + 40 ≤ a) → (a + k ≤ sp - 24 ∨ sp - 8 ≤ a) →
      (a + k ≤ sp + 16 ∨ sp + 32 ≤ a) → S1.mem.readLE a k = M.readLE a k := by
    intro a k h1 h2 h3
    refine hcf.readLE _ _ ?_
    simp only [cmpF, outside_cons, outside_nil, and_true]
    omega
  have q400 := (rdC (sp + 400) 8 (by omega) (by omega) (by omega)).trans r400
  have q160 := (rdC (sp + 160) 8 (by omega) (by omega) (by omega)).trans r160
  have q168 := (rdC (sp + 168) 8 (by omega) (by omega) (by omega)).trans r168
  have q1016 := (rdC (sp + 1016) 8 (by omega) (by omega) (by omega)).trans r1016M
  have q1024 := (rdC (sp + 1024) 8 (by omega) (by omega) (by omega)).trans r1024M
  have q1032 := (rdC (sp + 1032) 8 (by omega) (by omega) (by omega)).trans r1032M
  have qz := rdC zzp (8 * n) (by omega) (by omega) (by omega)
  have qm := (rdC mp (8 * n) (by omega) (by omega) (by omega)).trans eMv
  have hacc1 : S1.mem.accessible sp 1040 true = true := by
    rw [hcf.accessible]; exact M.accessible_sub haccM (Or.inr rfl) (by omega) (by omega)
  have hcfR : ∀ r ∈ cmpF sp, InRanges r.1 (r.2 - r.1) L ∨ Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [cmpF, List.mem_cons, List.mem_nil_iff, or_false] at hr
    right
    rcases hr with rfl | rfl | rfl <;> exact hwrt.of_sub (by dsimp only; omega) (by dsimp only; omega)
  have hinv1 : R.inv b L g (view R.rt L S1.mem) := FvModexp.Expmc.inv_frame hcf hcfR hinv
  have hzacc1 : S1.mem.accessible zzp (8 * zzc) true = true := by rw [hcf.accessible, hF.accessible]; exact hzza
  by_cases hlt : M.readLE zzp (8 * n) < M0.readLE mp (8 * n)
  · rw [CmpW.cmpRes_eq_lt hlt] at hr0
    refine exLt impl ret hret Q S1 sp g zzp n zzc r18 r29 S1.mem hpc1 hsp1' hr0 hr18 hr28 hr29 rfl q400 q160 q168
      hal hsp2 hacc1 (fun S' a1 a2 a3 a4 a5 a6 a7 a8 a9 => KJ S' zzp n zzc S1.mem a1 a2 a3 a4 a5 a6 a7 a8 a9 ?_)
    refine JoinPost.pre hcf hrg1 hLs4 (by omega) ⟨L, b, LiveExt.refl R L, by omega, hinv1, rfl, MemFrame.refl _ _,
      ⟨fun _ _ _ _ => rfl⟩, ?_, by omega, by omega, fun _ => ⟨hal8zz, hzzh, hzacc1, hzzb⟩, Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨by omega, S1.mem.accessible_sub hzacc1 (Or.inr rfl) (Nat.le_refl _) (by omega)⟩⟩
    unfold natVal
    rw [qz, if_neg (by omega)]
  · obtain ⟨v, hv, hcv⟩ := CmpW.cmpRes_eq_ge (Nat.not_lt.1 hlt)
    rw [hcv] at hr0
    refine exGe impl ret hret Q S1 sp g zzp n zzc mp mc v r18 r29 S1.mem hpc1 hsp1' hr0 hv hr18 hr28 hr29 rfl q400
      q160 q168 q1016 q1024 q1032 hal hsp2 hacc1 ?_
    intro S2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
    have hce1 : CallW.CEnv R L g sp 4304 1040 S1.mem := by
      refine CallW.CEnv.frame hceM (FvModexp.Expmc.frame_widen_rt hcf) hrg1 ?_ ?_
      · intro r hr _
        simp only [cmpF, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl <;>
          exact M.accessible_sub haccM (Or.inr rfl) (by dsimp only; omega) (by dsimp only; omega)
      · unfold Apart at hgw
        simp only [cmpF, outside_cons, outside_nil, and_true]
        omega
    have heqZ : S1.mem.readLE zzp (8 * n) = M0.readLE mp (8 * n) := by rw [qz]; omega
    refine exSub impl hap R hmk hmv hserv ret hret Q b L g sp n mp mc zzp zzc r18 r29 S2 S1.mem a1 a2 a3 a4 a5 a6 a7
      a8 a9 a10 a11 a12 a13 a14 a15 a16 hce1 q1016 q1024 q1032 hal8zz (by omega) hzzc2 hzacc1 hzzb hzzh
      (by unfold Apart; omega) hzzg (by rw [hcf.accessible, hF.accessible]; exact hma) hmb hmh (by unfold Apart; omega)
      hn hn16 hmc hmc' hzzm (norm_of_eq heqZ hnm0) (norm_of_eq qm hnm0) (heqZ.trans qm.symm) hinv1 ?_
    intro S' p l c M' b1 b2 b3 b4 b5 b6 b7 b8 b9 hJ
    refine KJ S' p l c M' b1 b2 b3 b4 b5 b6 b7 b8 b9 ?_
    rw [if_pos (by omega)]
    exact JoinPost.pre hcf hrg1 hLs4 (by omega) hJ

end FvModexp.Arm64.W4Loop
