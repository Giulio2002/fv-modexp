import FvModexp.Proofs.Arm64.Nat.DivLessF
import FvModexp.Proofs.Arm64.MemmoveZero

/-!
# `nat.div` (arm64), `u < v`: `copy(r, u)` (`memmove`, zero-length `memmove` or skipped when `r`'s array is `u`'s),
`r` stored, return (natdiv.go:534-535, nat.go:93-94)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

theorem copied_sub {m0 m : Memory} {dst src n k l : Nat} (h : Janus.Contracts.Mem.Copied m0 m dst src n)
    (hk : k + l ≤ n) : Janus.Contracts.Mem.Copied m0 m (dst + k) (src + k) l := fun i hi => by
  have := h (k + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `len u > 0`: `memmove(r, u, 8·len u)` -/
theorem lessC1 (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibDiv.program.link impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul v vl : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u ul s p c L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (hu0 : 0 < ul) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQ R b dc L zp zc st z2 z2c u ul v vl s) := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hp.ce
  unfold Apart at hga
  have hsv := hp.sv
  have hul := hp.ul9
  obtain ⟨hu40, huacc, hu48, huh, huw⟩ := hp.uo
  simp only [win, outside_cons, outside_nil, and_true] at huw
  have harr := hS.arr
  -- `r`'s array: writable, held in `L'`, outside the window, apart from `u`
  have hpa : S.mem.accessible p (8 * ul) true = true ∧ p + 8 * ul ≤ 2 ^ 48 ∧ Held R L' p (8 * ul) ∧
      (p + 8 * ul ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ p) ∧ Apart p (8 * ul) u (8 * ul) := by
    rcases harr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, hc2, h8, h48, hin, hap, hinL, hacc⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hp.z2o.2.1 (by omega)
      have hw2 := (hp.z2o.2.2 (by omega)).1
      simp only [win, outside_cons, outside_nil, and_true] at hw2
      have hap2 := (hp.pw _ _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) (by omega)).1
      unfold Apart at hap2 ⊢
      refine ⟨by rw [hS.mf.accessible]; exact Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega), by omega,
        hS.ext.held (a2.sub (Nat.le_refl _) (by omega)), by omega, by omega⟩
    · have := outside_of_inRanges hout hin
      have hapu := held_apart_fresh huh hap hin
      unfold Apart at hapu ⊢
      refine ⟨Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), by omega, Or.inl (hinL.sub (Nat.le_refl _) (by omega)),
        by omega, by omega⟩
  obtain ⟨hpacc, hp48, hph, hpw, hpu⟩ := hpa
  have hph' : InRanges p (8 * ul) L' ∨ Outside p (8 * ul) R.rt := hph
  have huh'' : InRanges u (8 * ul) L' ∨ Outside u (8 * ul) R.rt := hS.ext.held huh
  unfold Apart at hpu
  have hpu' : p ≠ u := by omega
  have huacc' : S.mem.accessible u (8 * ul) false = true := by rw [hS.mf.accessible]; exact huacc
  have huh' : Held R L' u (8 * ul) := hS.ext.held huh
  have hok : R.ok (cA "runtime.memmove") [p, u, 8 * ul] := hsv.2.1 _ _ _ (by omega)
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr6 := hS.r6
  have hacc := hS.mf.accessible
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hS.mf.readLE _ _ (by simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  have hLs1 : ∀ r ∈ L', r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ r.1 := by
    obtain ⟨ns, e, hn, -⟩ := hS.ext
    intro r hr; rw [e] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := outside_of_inRanges hout (hn r hr).1; omega
  have hinvS := hS.inv
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.q0; have m4 := hS.q1; have m5 := hS.q2; have m6 := hS.s8
  have hc40 : c < 2 ^ 40 := by
    rcases harr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, hc2, -⟩
    · exact hp.z2o.1
    · omega
  have hB : Box (Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s ∧ AtS R b L zp zc z2 z2c u ul s p c L' b' S) :=
    ⟨⟨hpre, hS⟩⟩
  clear hpre hp hS hce harr
  have hpu'' : (BitVec.ofNat 64 p = BitVec.ofNat 64 u) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [m1, m2, m3, m4, m5, m6, hpu''] calls [hmv]
  rename_i m _ _ hMF hLF hinv' hcp _
  obtain ⟨hpre, hS⟩ := hB.h
  have hW1 : MemFrame S.mem (((S.mem.writeLE (s.sp.toNat - 112) 8 ul).writeLE (s.sp.toNat - 88) 8 p).writeLE
      (s.sp.toNat - 104) 8 c) [(s.sp.toNat - 112, s.sp.toNat - 80)] := by janus_frame
  have hm1 : ∀ a n, (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) →
      (((S.mem.writeLE (s.sp.toNat - 112) 8 ul).writeLE (s.sp.toNat - 88) 8 p).writeLE (s.sp.toNat - 104) 8 c).readLE a n =
        S.mem.readLE a n := fun a n h => hW1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hcpv := FvModexp.Asm.readLE_of_copied hcp
  have hcpt := FvModexp.Asm.readLE_of_copied (copied_sub (k := 8 * (ul - 1)) (l := 8) hcp (by omega))
  rw [hm1 _ _ (by omega)] at hcpv hcpt
  have har : ar p ul = [(p, p + 8 * ul)] := by unfold ar; rw [if_pos hu0]
  have hW2 : MemFrame m (((m.writeLE (s.sp.toNat - 80) 8 p).writeLE (s.sp.toNat - 72) 8 ul).writeLE
      (s.sp.toNat - 64) 8 c) [(s.sp.toNat - 80, s.sp.toNat - 56)] := by janus_frame
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lessFin hpre hS hU _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF ?hI ?hV ?hT⟩
  case hM =>
    rw [har]
    refine (hW1.trans hMF (rs'' := R.rt ++ winA s 41504 112 ++ [(p, p + 8 * ul)]) fun a n h => ?_).trans
      hW2 fun a n h => ⟨h, ?_⟩
    · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨by omega, ⟨h.1.1, by omega, by omega⟩, h.2⟩
    · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  case hLF =>
    rw [har]
    refine ⟨fun a n hin ho => ?_⟩
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs1 r hr
    rw [hW2.readLE a n
      (by simp only [outside_cons, outside_nil, and_true]; omega), hLF.readLE a n ⟨r, hr, i1, i2⟩ ho]
    exact hW1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hI =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 80, s.sp.toNat - 56)]) (by janus_frame) (fun r hr => ?_) hinv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hV =>
    rw [← hcpv]
    exact hW2.readLE _ _
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hT =>
    intro _
    rw [← hcpt]
    exact hW2.readLE _ _
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  all_goals janus_simp
  all_goals exact ofNat_modL _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `len u = 0`: `memmove(r, u, 0)` (zero-length contract) or skipped (`r`'s pointer = `u`'s) -/
theorem lessC0 (impl : List Segment) (R : RtInv)
    (hmz : MemmoveZeroLive (LibDiv.program.link impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u v vl : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u 0 v vl s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u 0 s p c L' b' S) (hU : natVal s.mem u 0 < natVal s.mem v vl)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQ R b dc L zp zc st z2 z2c u 0 v vl s) := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hp.ce
  unfold Apart at hga
  have hsv := hp.sv
  have hok : ∀ d sr, R.ok (cA "runtime.memmove") [d, sr, 0] := fun d sr => hsv.2.1 _ _ _ (by omega)
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr6 := hS.r6
  have hacc := hS.mf.accessible
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hS.mf.readLE _ _ (by simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  have hLs1 : ∀ r ∈ L', r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ r.1 := by
    obtain ⟨ns, e, hn, -⟩ := hS.ext
    intro r hr; rw [e] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := outside_of_inRanges hout (hn r hr).1; omega
  have hinvS := hS.inv
  have m1 := hS.lr; have m2 := hS.fp; have m3 := hS.q0; have m4 := hS.q1; have m5 := hS.q2; have m6 := hS.s8
  have hc40 : c < 2 ^ 40 := by
    rcases hS.arr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, hc2, -⟩
    · exact hp.z2o.1
    · omega
  have hB : Box (Pre R b dc L zp zl zc st z2 z2l z2c u 0 v vl s ∧ AtS R b L zp zc z2 z2c u 0 s p c L' b' S) :=
    ⟨⟨hpre, hS⟩⟩
  have har : ar p 0 = [] := rfl
  clear hpre hp hS
  by_cases hpu : BitVec.ofNat 64 p = BitVec.ofNat 64 u
  · have hpu' := eq_true hpu
    janus_run [m1, m2, m3, m4, m5, m6, hpu']
    obtain ⟨hpre, hS⟩ := hB.h
    have hW2 : MemFrame S.mem (((S.mem.writeLE (s.sp.toNat - 80) 8 p).writeLE (s.sp.toNat - 72) 8 0).writeLE
        (s.sp.toNat - 64) 8 c) [(s.sp.toNat - 80, s.sp.toNat - 56)] := by janus_frame
    refine ⟨⟨?_, ?_, ?_, ?_⟩, lessFin hpre hS hU _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF ?hI ?hV (fun h => absurd h (by omega))⟩
    case hM =>
      rw [har]; refine hW2.mono fun a n h => ?_
      simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
    case hLF =>
      rw [har]; refine ⟨fun a n hin _ => hW2.readLE a n ?_⟩
      obtain ⟨r, hr, i1, i2⟩ := hin
      have := hLs1 r hr
      simp only [outside_cons, outside_nil, and_true]; omega
    case hI =>
      refine RtInv.inv_frame' hW2 (fun r hr => ?_) hinvS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    case hV => simp only [Nat.mul_zero, Memory.readLE_zero]
    all_goals janus_simp
    all_goals exact ofNat_modL _
  · have hpu' := eq_false hpu
    janus_run [m1, m2, m3, m4, m5, m6, hpu'] calls [hmz]
    rename_i m _ _ hLF _ hMF hinv' _
    obtain ⟨hpre, hS⟩ := hB.h
    have hW1 : MemFrame S.mem (((S.mem.writeLE (s.sp.toNat - 112) 8 0).writeLE (s.sp.toNat - 88) 8 p).writeLE
        (s.sp.toNat - 104) 8 c) [(s.sp.toNat - 112, s.sp.toNat - 80)] := by janus_frame
    have hW2 : MemFrame m (((m.writeLE (s.sp.toNat - 80) 8 p).writeLE (s.sp.toNat - 72) 8 0).writeLE
        (s.sp.toNat - 64) 8 c) [(s.sp.toNat - 80, s.sp.toNat - 56)] := by janus_frame
    refine ⟨⟨?_, ?_, ?_, ?_⟩, lessFin hpre hS hU _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF ?hI ?hV (fun h => absurd h (by omega))⟩
    case hM =>
      rw [har]
      refine (hW1.trans hMF (rs'' := R.rt ++ winA s 41504 112 ++ []) fun a n h => ?_).trans hW2 fun a n h => ⟨h, ?_⟩
      · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
        exact ⟨by omega, h.1, by omega, by omega⟩
      · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
    case hLF =>
      rw [har]
      refine ⟨fun a n hin ho => ?_⟩
      obtain ⟨r, hr, i1, i2⟩ := hin
      have := hLs1 r hr
      rw [hW2.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega),
        hLF.readLE a n ⟨r, hr, i1, i2⟩ (by simp only [outside_nil])]
      exact hW1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
    case hI =>
      refine RtInv.inv_frame' hW2 (fun r hr => ?_) hinv'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    case hV => simp only [Nat.mul_zero, Memory.readLE_zero]
    all_goals janus_simp
    all_goals exact ofNat_modL _

end FvModexp.Arm64.NatDiv

