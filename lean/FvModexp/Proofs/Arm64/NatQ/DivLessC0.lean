import FvModexp.Proofs.Arm64.NatQ.DivLessF

set_option autoImplicit false

/-! (split out of NatQ/DivLessC, asm s43: row time) `nat.div` (arm64), `u < v`, `len u = 0` branch: see DivLessC. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `len u = 0`: `memmove(r, u, 0)` (zero-length contract) or skipped (`r`'s pointer = `u`'s) -/
theorem lessC0 (impl : List Segment) (R : RtInv)
    (hmz : MemmoveZeroLive (LibDiv.program.link impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u v vl : Nat} {s : State}
    (hpre : PreG R b H dc L zp zl zc st z2 z2l z2c u 0 v vl s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u 0 s p c L' b' S) (hU : natVal s.mem u 0 < natVal s.mem v vl)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQG R b H dc L zp zc st z2 z2c u 0 v vl s) := by
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
  have hB : Box (PreG R b H dc L zp zl zc st z2 z2l z2c u 0 v vl s ∧ AtS R b L zp zc z2 z2c u 0 s p c L' b' S) :=
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

end FvModexp.Arm64.Q.NatDiv

