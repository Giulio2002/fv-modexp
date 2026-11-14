import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.CallW
import FvModexp.Proofs.Arm64.Exp.CmpW
import FvModexp.Proofs.Arm64.Exp.W2ExitB
import FvModexp.Proofs.Arm64.Nat.NatSub

/-!
# window-2 (arm64), the subtract path of the final reduction (nat.go:1484-1488)

At `nat.sub`'s entry with `zz = m` (the first `zz.cmp(m) >= 0` and `zz ≤ m`, `ExpFinal.mont_one_le`): the call
`zz = zz.sub(zz, m)` (divmc's `NatSub.ens`, by hand: its precondition contains `CallEnv`), the spills, the second
`zz.cmp(m)` (asm's `cmp_summary`), which is `-1` because the difference is `0` (length `0 < n`), so the `div` fallback is
not taken, and the jump to the join `njoin`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Loop

/-- the frame of a `nat.cmp` call at `sp` -/
@[reducible] def cmpF (sp : Nat) : List (Nat × Nat) := [(sp - 24, sp - 8), (sp + 8, sp + 16), (sp + 32, sp + 40)]

theorem norm_zero {m : Memory} {p l : Nat} (hv : natVal m p l = 0) (hn : NatNorm m p l) : l = 0 := by
  rcases hn with h | h
  · exact h
  rcases l with _ | l
  · rfl
  exfalso; apply h
  rw [Nat.add_sub_cancel]
  unfold natVal at hv
  rw [show 8 * (l + 1) = 8 * l + 8 by omega, Memory.readLE_add] at hv
  have h2 : 256 ^ (8 * l) * m.readLE (p + 8 * l) 8 = 0 := by omega
  rcases Nat.mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by decide)))
  · exact h3

theorem toNat_lt {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the second `zz.cmp(m)` with `len zz = 0 < len m`: result `-1`, reload `zz`, jump to the join -/
theorem exCmp2 (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (S : State) (sp g p c mp n : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 cmpEntry) (h30 : S.regs 30 = BitVec.ofNat 64 cmp2Ret)
    (hsp : S.sp = BitVec.ofNat 64 sp) (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 0)
    (h3 : S.regs 3 = BitVec.ofNat 64 mp) (h4 : S.regs 4 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (r400 : M.readLE (sp + 400) 8 = p) (r160 : M.readLE (sp + 160) 8 = 0) (r168 : M.readLE (sp + 168) 8 = c)
    (hal : sp % 16 = 0) (h4304 : 4304 ≤ sp) (hsp1 : sp + 752 ≤ 2 ^ 48) (hacc : M.accessible (sp - 24) 776 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hga : M.accessible (g + 16) 8 false = true) (hgv : M.readLE (g + 16) 8 < sp)
    (hn : 0 < n) (hm48 : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true)
    (hmw : Apart mp (8 * n) (sp - 24) 64)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 njoinL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 p → S'.regs 4 = BitVec.ofNat 64 0 → S'.regs 5 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (cmpF sp) → M'.regions = M.regions →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  refine CmpW.call ((LibWC.cmpSum impl).withExit hret) hpc
    (CmpW.pre_of (x := p) (xl := 0) hsp h28 h30 h0 h1 h3 h4 (by decide) (by decide) hal (by omega) (by omega)
      (by rw [hmem]; exact M.accessible_sub hacc (Or.inr rfl) (Nat.le_refl _) (by omega)) hg1
      (by rw [hmem]; exact hga) (by rw [hmem]; omega) (Or.inl rfl) (Or.inr ⟨hm48, by rw [hmem]; exact hma, hmw⟩)) ?_
  intro S1 hpc1 hsp1' hr0 hr3 hr18 hr28 hr29 hcf hrg1
  have tn : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [h1, h4, tn, CmpW.cmpRes_lt (by simp; omega)] at hr0
  rw [hmem, tsp] at hcf
  rw [hmem] at hrg1
  rw [h30] at hpc1
  rw [hsp] at hsp1'
  rw [h18] at hr18
  rw [h28] at hr28
  rw [h29] at hr29
  have rdC : ∀ a, sp + 40 ≤ a → S1.mem.readLE a 8 = M.readLE a 8 := by
    intro a h1
    refine hcf.readLE _ _ ?_
    simp only [cmpF, outside_cons, outside_nil, and_true]
    omega
  have q400 := (rdC (sp + 400) (by omega)).trans r400
  have q160 := (rdC (sp + 160) (by omega)).trans r160
  have q168 := (rdC (sp + 168) (by omega)).trans r168
  have hacc1 : S1.mem.accessible sp 752 true = true := by
    rw [hcf.accessible]; exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)
  have fnB := fnBase
  janus_run [q400, q160, q168, fnB] until [njoinL]
  refine K _ S1.mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hcf hrg1
  all_goals first | rfl | (janus_simp; done) | skip

/-- the frame from `nat.sub`'s return to the join -/
@[reducible] def tw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 24, sp - 8), (sp + 8, sp + 80), (sp + 160, sp + 176), (sp + 400, sp + 408)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- after `zz = zz.sub(zz, m)` (result length 0): spills, the second `zz.cmp(m)`, the join -/
theorem exSubT (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (S : State) (sp g p c mp n mc : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 subRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 0) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (hc : c < 2 ^ 64) (hp : p < 2 ^ 64) (hmc : mc < 2 ^ 64)
    (hal : sp % 16 = 0) (h4304 : 4304 ≤ sp) (hsp1 : sp + 752 ≤ 2 ^ 48) (hacc : M.accessible (sp - 24) 776 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hga : M.accessible (g + 16) 8 false = true) (hgv : M.readLE (g + 16) 8 < sp)
    (hgw : g + 24 ≤ sp - 24 ∨ sp + 752 ≤ g + 16)
    (hn : 0 < n) (hm48 : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true)
    (hmw : Apart mp (8 * n) (sp - 24) 64)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 njoinL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 p → S'.regs 4 = BitVec.ofNat 64 0 → S'.regs 5 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (tw sp) → M'.regions = M.regions →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have fnB := fnBase
  janus_run [r728, r736, r744, fnB] until [cmpEntry]
  have hW : MemFrame M (((M.writeLE (sp + 400) 8 p).writeLE (sp + 160) 8 0).writeLE (sp + 168) 8 c)
      [(sp + 160, sp + 176), (sp + 400, sp + 408)] :=
    (((MemFrame.refl _ _).writeLE _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by dsimp only; omega)
      (by dsimp only; omega)).writeLE _ (List.mem_cons_self ..) (by dsimp only; omega) (by dsimp only; omega)).writeLE
      _ (List.mem_cons_self ..) (by dsimp only; omega) (by dsimp only; omega)
  refine exCmp2 impl ret hret Q _ sp g p c mp n r18 r29
    (((M.writeLE (sp + 400) 8 p).writeLE (sp + 160) 8 0).writeLE (sp + 168) 8 c)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hmem ?r400 ?r160 ?r168 hal h4304 hsp1 ?acc hg1 ?ga ?gv hn hm48 ?ma hmw ?K
  all_goals first | (janus_simp; done) | skip
  case acc => simp only [Memory.accessible_writeLE]; exact hacc
  case ga => simp only [Memory.accessible_writeLE]; exact hga
  case ma => simp only [Memory.accessible_writeLE]; exact hma
  case gv => simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hgv
  case K =>
    intro S4 M4 a1 a2 a3 a4 a5 a6 a7 a8 a9 hcf2 hrg2
    refine K S4 M4 a1 a2 a3 a4 a5 a6 a7 a8 a9 (hW.trans hcf2 (fun a k ho => ?_)) ?_
    · simp only [tw, cmpF, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · rw [hrg2]; simp only [Memory.regions_writeLE]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- the subtract path, from `nat.sub`'s entry to the join -/
theorem exSub (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc zzp zzc : Nat) (r18 r29 : BitVec 64)
    (S : State) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 subEntry) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h30 : S.regs 30 = BitVec.ofNat 64 subRet)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h1 : S.regs 1 = BitVec.ofNat 64 n) (h2 : S.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : S.regs 3 = BitVec.ofNat 64 zzp) (h4 : S.regs 4 = BitVec.ofNat 64 n) (h5 : S.regs 5 = BitVec.ofNat 64 zzc)
    (h6 : S.regs 6 = BitVec.ofNat 64 mp) (h7 : S.regs 7 = BitVec.ofNat 64 n) (h8 : S.regs 8 = BitVec.ofNat 64 mc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (hce : CallW.CEnv R L g sp 4304 752 M)
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (hz8 : zzp % 8 = 0) (hzn : n ≤ zzc) (hzc40 : zzc < 2 ^ 40) (hzacc : M.accessible zzp (8 * zzc) true = true)
    (hz48 : zzp + 8 * zzc ≤ 2 ^ 48) (hzh : Held R L zzp (8 * zzc)) (hzw : Apart zzp (8 * zzc) (sp - 4304) (4304 + 752))
    (hzg : Apart (g + 16) 8 zzp (8 * zzc))
    (hma : M.accessible mp (8 * n) false = true) (hm48 : mp + 8 * n ≤ 2 ^ 48) (hmh : Held R L mp (8 * n))
    (hmw : Apart mp (8 * n) (sp - 4304) (4304 + 752)) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc)
    (hmc40 : mc < 2 ^ 40) (hzm : Apart zzp (8 * zzc) mp (8 * n))
    (hnz : NatNorm M zzp n) (hnm : NatNorm M mp n) (heq : M.readLE zzp (8 * n) = M.readLE mp (8 * n))
    (hinv : R.inv b L g (view R.rt L M))
    (KJ : ∀ (S' : State) (p l c : Nat) (M' : Memory), S'.pc = BitVec.ofNat 64 njoinL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 p → S'.regs 4 = BitVec.ofNat 64 l → S'.regs 5 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      JoinPost R b L g sp n zzp zzc 0 M p l c M' →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce
  have hce : CallW.CEnv R L g sp 4304 752 M := ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩
  have hns : ∀ x, NatSub.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)
  have hS0 := LibWC.hypSum hap hns (NatSub.ensR impl hap R hmk hmv b L (BitVec.ofNat 64 zzp) (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 zzc) (BitVec.ofNat 64 zzp) (BitVec.ofNat 64 n) (BitVec.ofNat 64 zzc) (BitVec.ofNat 64 mp)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc))
  rw [show segAddr Extracted.program NatSub.fn = subEntry by decide] at hS0
  have tz := toNat_lt (v := zzp) (by omega)
  have tn := toNat_lt (v := n) (by omega)
  have tzc := toNat_lt (v := zzc) (by omega)
  have tm := toNat_lt (v := mp) (by omega)
  have tmc := toNat_lt (v := mc) (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt (by omega)
  have tg : (S.regs 28).toNat = g := by rw [h28]; exact toNat_lt (by omega)
  refine Reaches.call_regions (hS0.withExit hret) hpc ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [h30, toNat_lt (by decide)]
    have := CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := NatSub.names)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 685 (by decide) (by decide) (by decide)
    exact this
  case args =>
    simp only [ArgsFrom]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  case pre =>
    unfold NatSub.Pre NatSub.PreS
    rw [tz, tn, tzc, tm, tmc, hmem]
    have hce' := CallW.callEnv_of hce hsp h28 hmem (stk := 4304) (above := 80) (Nat.le_refl _) (by omega)
    simp only [win, tsp, tg]
    unfold Apart at hzw hmw hzg hzm
    refine ⟨hce', RoOut.out' hro 1 (by decide) (by decide), Nat.le_refl _, by simp only [natVal]; omega, hzn, hmc, by omega, by omega,
      by omega, by omega, by omega, fun _ => ⟨hz8, hzh, hzacc, hz48⟩, ?_, fun _ => ⟨by unfold Apart; omega,
      Or.inl trivial, Or.inr (by unfold Apart; omega)⟩, M.accessible_sub hzacc (Or.inr rfl) (Nat.le_refl _) (by omega),
      by omega, hzh.sub (Nat.le_refl _) (by omega), hnz, hnm, ?_, hma, hm48, hmh, ?_, hinv,
      fun h => absurd h (by omega), fun d src k hk => hserv.2.1 d src k (by omega)⟩
    all_goals simp only [outside_cons, outside_nil, and_true]; omega
  -- after `nat.sub`
  obtain ⟨⟨p', l', c', hp0, hp1, hp2, hval, hnorm, hlc, hln, L', b', hLE, hb', hinv', hlive, hor, hF, hLF⟩, hreu, -⟩ := hq
  have hcz : c' = zzc := by
    have := (hreu (by rw [tn, tzc]; exact hzn)).2
    rw [hp2, tzc] at this; exact this
  simp only [tz, tn, tzc, tm, hmem, tsp, tg, winA] at hval hb' hinv' hor hF hLF
  have hl0 : l' = 0 := norm_zero (by rw [hval]; simp only [natVal] at heq ⊢; omega) hnorm
  subst hl0
  have hc64 : c' < 2 ^ 64 := by rw [← hp2]; exact BitVec.isLt _
  have hp0' := hp0
  have e0 : s'.regs 0 = BitVec.ofNat 64 p' := by rw [← hp0, FvModexp.Expmc.bv_ofNat_toNat]
  have e1' : s'.regs 1 = BitVec.ofNat 64 0 := by rw [← hp1, FvModexp.Expmc.bv_ofNat_toNat]
  have e2' : s'.regs 2 = BitVec.ofNat 64 c' := by rw [← hp2, FvModexp.Expmc.bv_ofNat_toNat]
  have hsp' : s'.sp = BitVec.ofNat 64 sp := e1.trans hsp
  have h28' : s'.regs 28 = BitVec.ofNat 64 g := e2.trans h28
  have h29' : s'.regs 29 = r29 := e3.trans h29
  have h18' : s'.regs 18 = r18 := e4.trans h18
  have hpc' : s'.pc = BitVec.ofNat 64 subRet := hr.trans h30
  clear hr e1 e2 e3 e4 hp1 hp2
  have u1 := hzw; have u2 := hmw; have u3 := hzg; unfold Apart at u1 u2 u3
  have rdS : ∀ a, sp + 80 ≤ a → a + 8 ≤ sp + 752 → s'.mem.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hrt.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  have s1016 := (rdS (sp + 728) (by omega) (by omega)).trans r728
  have s1024 := (rdS (sp + 736) (by omega) (by omega)).trans r736
  have s1032 := (rdS (sp + 744) (by omega) (by omega)).trans r744
  have hacc' : s'.mem.accessible (sp - 24) 776 true = true := by
    rw [hF.accessible]; exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)
  have hga' : s'.mem.accessible (g + 16) 8 false = true := by rw [hF.accessible]; exact hg2
  have hgv' : s'.mem.readLE (g + 16) 8 < sp := by
    have ho : Outside (g + 16) 8 (R.rt ++ [(sp - 4304, sp - 8), (sp + 8, sp + 80)] ++ [(zzp, zzp + 8 * zzc)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hgrt, by clear u1 u2 u3; unfold Apart at hga; omega⟩, by omega⟩
    rw [hF.readLE _ _ ho]; omega
  have hma' : s'.mem.accessible mp (8 * n) false = true := by rw [hF.accessible]; exact hma
  have hpb : p' < 2 ^ 64 := by rw [← hp0']; exact BitVec.isLt _
  refine exSubT impl ret hret Q s' sp g p' c' mp n mc r18 r29 s'.mem hpc' hsp' e0 e1' e2' h18' h28' h29' rfl
    s1016 s1024 s1032 hc64 hpb (by omega) hal hK hA hacc' hg1 hga' hgv' (by clear u1 u2 u3; unfold Apart at hga; omega) hn hm48 hma'
    (by unfold Apart; omega) ?_
  intro S4 M4 a1 a2 a3 a4 a5 a6 a7 a8 a9 hW2 hrg2
  have hWR : ∀ r ∈ tw sp, InRanges r.1 (r.2 - r.1) L' ∨ Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [tw, List.mem_cons, List.mem_nil_iff, or_false] at hr
    right
    rcases hr with rfl | rfl | rfl | rfl <;> exact hrt.of_sub (by dsimp only; omega) (by dsimp only; omega)
  refine KJ S4 p' 0 c' M4 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⟨L', b', hLE, hb', FvModexp.Expmc.inv_frame hW2 hWR hinv',
    by rw [hrg2, hrg, hmem], ?_, ?_, by simp [natVal], by omega, ⟨by omega, by omega⟩, ?_, hor, Or.inl rfl⟩
  · refine hF.trans hW2 (fun a k ho => ?_)
    simp only [jw, tw, winA, tz, tzc, tsp, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨⟨ho.1.1, by omega⟩, by omega⟩, by omega⟩
  · refine hLF.trans (FvModexp.Expmc.liveFrame_of_frame hW2 (fun a k hin _ => ?_)) (fun _ _ h => h)
    obtain ⟨r, hr, h1, h2⟩ := hin
    have hr' := hLs r hr
    simp only [tw, outside_cons, outside_nil, and_true] at hr' ⊢
    omega
  · intro hc0
    obtain ⟨q1, q2, q3, q4⟩ := hlive hc0
    exact ⟨q1, q2, by rw [hW2.accessible]; exact q3, q4⟩

end FvModexp.Arm64.W2Loop
