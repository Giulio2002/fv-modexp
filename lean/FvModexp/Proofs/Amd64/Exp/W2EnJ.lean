import FvModexp.Proofs.Amd64.Exp.W2EnDefs
import FvModexp.Proofs.Amd64.Exp.W2Seg

set_option autoImplicit false

/-!
# window-2 entry (amd64): the join of `slices.Grow` (`enJ`, fn+0x1ed) → `xnE` (fn+0x22d) (agent expmc s63; ported from `Amd64.W4EnJ`)

The header update of the inline `stk.reserve(11n)` (nat.go:336-337): `len, cap` stores, the write-barrier flag test,
(flag on) `gcWriteBarrier2` with its buffer stores `(new ptr, old ptr)`, the pointer store, `len := len + nr`.
Adapted from agent divmc's amd64 `(*stack).nat` `joinW`/`tail` (Amd64/Nat/StackNatWb/Tail).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2En

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enJn {impl : List Amd64.Segment} {R : RtInv}
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {ret : W64} {Q : State → Prop}
    {b1 : Nat} {L1 : List (Nat × Nat)} {g sp st w1 len0 c1 n : Nat} {M : Memory}
    (hsp1 : 4200 ≤ sp) (hsp2 : sp + 0x2e0 ≤ 2 ^ 48) (hal : sp % 8 = 0)
    (hwacc : M.accessible (sp - 8 - 4096) (4096 + 8) true = true)
    (hwrt : Outside (sp - 8 - 4096) (4096 + 8) R.rt) (hwL : LiveSep L1 [(sp - 8 - 4096, sp)])
    (hsta : M.accessible st 24 true = true) (hst48 : st + 24 ≤ 2 ^ 48)
    (hsth : InRanges st 24 L1 ∨ Outside st 24 R.rt) (hstw : st + 24 ≤ sp - 8 - 4096 ∨ sp ≤ st)
    (hwbf : M.accessible StackNat.wbA 4 false = true) (hwbA : Apart st 24 StackNat.wbA 4)
    (hok : R.ok wbE [2]) (hinv : R.inv b1 L1 g (view R.rt L1 M)) (hg : g < 2 ^ 64)
    (hc : len0 + StackNat.rnd (11 * n) ≤ c1) (hc40 : c1 < 2 ^ 40) (hw64 : w1 < 2 ^ 64) (hl16 : len0 ≤ 2 ^ 16)
    (hn : n ≤ 128)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 enJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h11 : S.regs 11 = BitVec.ofNat 64 w1)
    (h12 : S.regs 13 = BitVec.ofNat 64 len0) (h13 : S.regs 15 = BitVec.ofNat 64 c1)
    (h15 : S.regs 2 = BitVec.ofNat 64 (StackNat.rnd (11 * n))) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hmem : S.mem = M)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 xnE → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 3 = S.regs 3 → S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 →
      S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = M' →
      MemFrame M M' (R.rt ++ [(st, st + 24), (sp - 8 - 4096, sp)]) → LiveFrame M M' L1 [(st, st + 24)] →
      M'.regions = M.regions → R.inv b1 L1 g (view R.rt L1 M') →
      M'.readLE st 8 = w1 → M'.readLE (st + 8) 8 = len0 + StackNat.rnd (11 * n) → M'.readLE (st + 16) 8 = c1 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have hrn := rnd23_le n
  have hacc16 : S.mem.accessible (st + 8) 16 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hsta (by omega) (by omega)
  have hacc8 : S.mem.accessible st 8 true = true := Janus.Arm64.Memory.accessible_mono _ hsta (by omega) (by omega)
  have hacc8' : S.mem.accessible st 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hacc8
  have hwbv : StackNat.wbA = 12283968 := rfl
  rw [hwbv] at hwbA hwbf
  unfold Apart at hwbA
  have e6 : BitVec.ofNat 64 (StackNat.rnd (11 * n)) + BitVec.ofNat 64 len0 =
      BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize e3 : S.regs 3 = x3 at K
  generalize e6' : S.regs 6 = x6 at K
  generalize e8 : S.regs 8 = x8 at K
  generalize e9 : S.regs 9 = x9 at K
  generalize e10 : S.regs 10 = x10 at K
  have hstwb : st + 24 ≤ sp - 8 - 4096 ∨ sp ≤ st := hstw
  have hM1 : MemFrame S.mem ((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1) [(st, st + 24)] := by janus_frame
  have hinvW : ∀ (ws : List (Nat × Nat)) (m' : Memory),
      MemFrame ((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1) m' ws →
      (∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L1) →
      R.inv b1 L1 g (view R.rt L1 m') := fun ws m' hws hwo =>
    RtInv.inv_frame' hws hwo (RtInv.inv_frame' hM1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [show st + 24 - st = 24 by omega]; exact hsth.symm) hinv)
  have hsth' : Outside st 24 R.rt ∨ InRanges st 24 L1 := hsth.symm
  janus64_run [hacc16, hacc8, hacc8', hwbf, e6] until [wbE, enS]
  · -- the barrier is off
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 xnE) ?_
    janus64_run [hacc16, hacc8] until [xnE]
    refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?lf ?rg ?inv ?q1 ?q2 ?q3
    case mf => janus_frame
    case lf =>
      have h : MemFrame S.mem ((((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).writeLE st 8 w1).writeLE
        (st + 8) 8 (len0 + StackNat.rnd (11 * n))) [(st, st + 24)] := by janus_frame
      exact ⟨fun a k _ ho => h.readLE a k ho⟩
    case inv =>
      refine hinvW [(st, st + 24)] _ (by janus_frame) fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [show st + 24 - st = 24 by omega]; exact hsth'
    case q1 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    case q2 => rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    case q3 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    all_goals first | (janus64_simp; done) | skip
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact h7 | exact h14 | exact hsp | exact e10 | rfl
  · -- the barrier is on
    have hsp8 : (BitVec.ofNat 64 sp - 8#64).toNat = sp - 8 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have tg : (BitVec.ofNat 64 g).toNat = g := by rw [BitVec.toNat_ofNat]; omega
    have hwL' : LiveSep L1 [(sp - 8 - 4096, sp - 8 + 8)] := by rw [show sp - 8 + 8 = sp by omega]; exact hwL
    have hWR : LiveSep [(sp - 8 - 4096, sp - 8 + 8)] R.rt := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp - 8 + 8 - (sp - 8 - 4096) = 4096 + 8 by omega]; exact hwrt
    have hold64 : S.mem.readLE st 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
    refine ReachesRet.call_regions (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hok, ?_, ?_, ?_⟩ ?_
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp8, h14, tg]
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · omega
    · omega
    · omega
    · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hwacc
    · refine hinvW [(sp - 8, sp)] _ (by janus_frame) fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; left; simp only
      exact hwrt.of_sub (by omega) (by omega)
    · exact hwL'
    · exact hWR
    intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩ hrgW
    subst hs2
    try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
    try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp8, h14, tg] at hfr2 hapW hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hacc16b : m'.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hb8a : m'.accessible buf.toNat 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc16b (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hstb : st + 24 ≤ buf.toNat ∨ buf.toNat + 16 ≤ st := by
      rcases hsth with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hM1' : MemFrame S.mem (((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).writeLE (sp - 8) 8 6211085)
        [(st, st + 24), (sp - 8, sp)] := by janus_frame
    have hstm' : m'.accessible st 24 true = true := by
      rw [hfr2.accessible, hM1'.accessible]; exact hsta
    have hst8 : m'.accessible st 8 true = true := Janus.Arm64.Memory.accessible_mono _ hstm' (by omega) (by omega)
    have hst8' : m'.accessible (st + 8) 8 true = true := Janus.Arm64.Memory.accessible_mono _ hstm' (by omega) (by omega)
    have sret : (((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).writeLE (sp - 8) 8 6211085).readLE (sp - 8) 8 =
        6211085 := by rw [Janus.Arm64.Memory.readLE_writeLE_self]
    have hsp0 : BitVec.ofNat 64 sp - 8#64 + 8#64 = BitVec.ofNat 64 sp := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hlt : ¬ BitVec.ofNat 64 c1 < BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n)) := by
      simp only [BitVec.lt_def, BitVec.toNat_ofNat]; omega
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 xnE) ?_
    janus64_run [hb8a, hb8b, hbuf64, hst8, hst8', sret, hsp8, hsp0, hlt] until [xnE]
    have hbs : MemFrame m' ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (S.mem.readLE st 8))
        [(buf.toNat, buf.toNat + 16)] := by janus_frame
    have hst2 : MemFrame ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (S.mem.readLE st 8))
        ((((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (S.mem.readLE st 8)).writeLE st 8 w1).writeLE
          (st + 8) 8 (len0 + StackNat.rnd (11 * n))) [(st, st + 24)] := by janus_frame
    have hkeep : ∀ a k, st ≤ a → a + k ≤ st + 24 →
        m'.readLE a k = (((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).writeLE (sp - 8) 8 6211085).readLE a k := by
      intro a k h1 h2
      rcases hsth with hL | hO
      · exact hlf2.readLE a k (hL.sub h1 h2) trivial
      · refine hfr2.readLE a k ?_
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hO.of_sub h1 h2, by omega⟩
    refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf2 ?lf2 ?rg2 ?inv2 ?p1 ?p2 ?p3
    case mf2 =>
      refine MemFrame.trans (MemFrame.trans (MemFrame.trans hM1' hfr2 fun a k ho => ⟨?_, ?_⟩) hbs
        fun a k ho => ⟨ho, ?_⟩) hst2 fun a k ho => ⟨ho, ?_⟩
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega⟩
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        have := hbufR.apart ho.1; unfold Apart at this; omega
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    case lf2 =>
      refine ⟨fun a k hin hout => ?_⟩
      obtain ⟨r, hr, h1, h2⟩ := hin
      have h3 := hwL r hr
      have h4 := hapL r hr
      unfold Apart at h4
      simp only [outside_cons, outside_nil, and_true] at h3 hout
      rw [hst2.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
        hbs.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
        hlf2.readLE a k ⟨r, hr, h1, h2⟩ trivial,
        hM1'.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
    case rg2 =>
      simp only [Janus.Arm64.Memory.regions_writeLE]
      have : m'.regions = (((S.mem.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).writeLE (sp - 8) 8
        6211085).regions := hrgW
      rw [this]; simp only [Janus.Arm64.Memory.regions_writeLE]
    case inv2 =>
      have hv1 : view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (S.mem.readLE st 8)) =
          ((view R.rt L1 m').writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (S.mem.readLE st 8) := by
        rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
          view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
      have h2 : R.inv b1 L1 g (view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8
          (S.mem.readLE st 8))) := by rw [hv1]; exact hinvS _ (by janus_frame)
      refine RtInv.inv_frame' hst2 (fun r hr => ?_) h2
      simp only [List.mem_singleton] at hr; subst hr
      simp only [show st + 24 - st = 24 by omega]; exact hsth'
    case p1 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    case p2 => rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    case p3 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hkeep _ _ (by omega) (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    all_goals try simp only [setRegF_apply, wbRegs64, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact hsp0 | exact h7 | exact e3 | exact e6' | exact e8 | exact e9 | exact e10 | exact h14

end FvModexp.Amd64.W2En
