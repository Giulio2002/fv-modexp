import FvModexp.Proofs.Arm64.Nat.MulLoopEnd
import FvModexp.Proofs.Arm64.Nat.MulLoopCall

/-!
# `nat.mul` (arm64), chunk loop: the exit (`m ≤ i`) — `z.norm()`, the deferred `stk.restore`, the return

`m_restcall`: the closure call `CALL (R0)` at `0x1bb2cc` (`mdsum`, `mRestPre`); `lendB`: from the deferred-call tests
`0x1bb2b4` (`AtB`, bits `= 2`) — clear bit 1, the closure, `TBZ $0` taken, reload the result, `RET`, `post_of` with the
facts of `lend_fin`; **`lend`**: the loop head with `m ≤ i` → `BLE` → `0x1bb278` → `normB` → `lendB`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

set_option maxRecDepth 20000 in
/-- **the deferred closure call** at its entry (memory = `A` + the defer-bit / result stores) -/
theorem m_restcall (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {W zp zc st xp xl xc yp yl yc : Nat} {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    {Lk : List (Nat × Nat)} {bk spent : Nat} {A : Memory}
    (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent A) (S2 : State)
    (hpc : S2.pc = BitVec.ofNat 64 0x1bb380) (hsp : S2.sp.toNat = s.sp.toNat - 256) (hg : S2.regs 28 = s.regs 28)
    (h26 : (S2.regs 26).toNat = s.sp.toNat - 64) (h30 : S2.regs 30 = BitVec.ofNat 64 0x1bb2d0)
    (hF : MemFrame A S2.mem [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80)])
    {n' : Nat} (e94 : S2.mem.readLE (s.sp.toNat - 162) 1 = 0) (e152 : S2.mem.readLE (s.sp.toNat - 104) 8 = p)
    (e160 : S2.mem.readLE (s.sp.toNat - 96) 8 = n') (e168 : S2.mem.readLE (s.sp.toNat - 88) 8 = c)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s3 : State, s3.pc = BitVec.ofNat 64 0x1bb2d0 → s3.sp = S2.sp → s3.regs 28 = S2.regs 28 →
      s3.regs 18 = S2.regs 18 → s3.regs 29 = S2.regs 29 →
      MemFrame A s3.mem [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80),
        (s.sp.toNat - 280, s.sp.toNat - 264), (st + 8, st + 16)] →
      s3.mem.readLE (st + 8) 8 = stLen M st →
      s3.mem.readLE (s.sp.toNat - 162) 1 = 0 → s3.mem.readLE (s.sp.toNat - 104) 8 = p →
      s3.mem.readLE (s.sp.toNat - 96) 8 = n' → s3.mem.readLE (s.sp.toNat - 88) 8 = c →
      s3.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat → s3.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat →
      ReachesRet (LibMul.program.link impl) ret s3 Q) :
    ReachesRet (LibMul.program.link impl) ret S2 Q := by
  have hP := mRestPre h S2 hsp hg h26 h30 hF
  have hD := mdsum impl
  rw [mdsum_entry] at hD
  obtain ⟨hW, hWs, hal, ha48, hout, -, -, hcap, -, hpw, -⟩ := h.lay
  have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 162 ∨ s.sp.toNat - 160 ≤ x) →
      (x + m ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 80 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((S2.regs 26).toNat + 8) 8 = st := by
    rw [h26, hrd _ _ (by omega) (by omega), show s.sp.toNat - 64 + 8 = s.sp.toNat - 56 by omega]; exact h.dst
  have hdln : S2.mem.readLE ((S2.regs 26).toNat + 16) 8 = stLen M st := by
    rw [h26, hrd _ _ (by omega) (by omega), show s.sp.toNat - 64 + 16 = s.sp.toNat - 48 by omega]; exact h.dln
  have hlr := h.lr
  have hfp := h.fp
  refine ReachesRet.call_regions hD hpc hP fun s3 hr hq hreg => ?_
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  rw [hdst, hdln] at q5
  rw [hdst, hsp] at q6
  have hFF : MemFrame A s3.mem [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80),
      (s.sp.toNat - 280, s.sp.toNat - 264), (st + 8, st + 16)] :=
    hF.trans q6 fun x m ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hr3 : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat →
      s3.mem.readLE x m = S2.mem.readLE x m :=
    fun x m h1 h2 => q6.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hr4 : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat - 248 → s3.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact hK s3 (by rw [hr, h30]) q1 q3 q2 q4 hFF q5 (by rw [hr3 _ _ (by omega) (by omega)]; exact e94)
    (by rw [hr3 _ _ (by omega) (by omega)]; exact e152) (by rw [hr3 _ _ (by omega) (by omega)]; exact e160)
    (by rw [hr3 _ _ (by omega) (by omega)]; exact e168) (by rw [hr4 _ _ (by omega) (by omega)]; exact hlr)
    (by rw [hr4 _ _ (by omega) (by omega)]; exact hfp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the deferred-call tests** (`0x1bb2b4`, bits `= 2`, after `normB`): the closure, the return, `MPost` -/
theorem lendB (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {W zp zc st xp xl xc yp yl yc : Nat} {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    {Lk : List (Nat × Nat)} {bk k : Nat} {A : Memory}
    (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp (stLen M st) yl k) A) (hklt : k * yl < xl)
    (hv : natVal A p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl)
    (S : State) (n' : Nat) (hB : AtB s S A p c n' 2) (hn' : n' ≤ xl + yl)
    (hvn : natVal A p n' = natVal A p (xl + yl)) (hnn : NatNorm A p n')
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hpc, h0, hsp, h28, h29, h18, hF, m1, m2, m3⟩ := hB
  obtain ⟨hW, hWs, hal, ha48, hout, -, -, hcap, hc40, hpw, -⟩ := h.lay
  obtain ⟨⟨-, ⟨-, -, -, hw0⟩, -⟩, -⟩ := h.core.pre
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 80 ≤ x) → S.mem.readLE x m = A.readLE x m :=
    fun x m h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hp1 : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 64 := by rw [hrd _ _ (by omega)]; exact h.dpt
  have hp2 : S.mem.readLE (s.sp.toNat - 64) 8 = 0x1bb380 := by rw [hrd _ _ (by omega)]; exact h.dfn
  have hwA : S.mem.accessible (s.sp.toNat - 264) 352 true = true := by
    rw [hF.accessible, h.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp' : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  clear hrd
  janus_run [hp1, hp2] until [0x1bb380]
  refine m_restcall impl h _ (n' := n') ?pc ?sp ?g ?h26 ?h30 ?hF2 ?e94 ?e152 ?e160 ?e168 ?cont
  case cont =>
    intro s3 q1 q2 q3 q4 q5 hFF hlen f94 f152 f160 f168 flr ffp
    simp only at q2 q3 q4 q5
    have hwC : s3.mem.accessible (s.sp.toNat - 264) 352 true = true := by
      rw [hFF.accessible, h.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
    obtain ⟨ho, inv2, sb2, F2, LF2⟩ := lend_fin h hFF hlen
    have v2 : natVal s3.mem p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl := by
      rw [natVal_frame hFF ho, hv]
    have hv3 : natVal s3.mem p n' = natVal s3.mem p (xl + yl) := by
      rw [natVal_frame hFF (ho.of_sub (Nat.le_refl _) (by omega)), natVal_frame hFF ho, hvn]
    have hnn3 : NatNorm s3.mem p n' := by
      rcases hnn with h0 | h0
      · exact Or.inl h0
      · right; rw [hFF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h0
    have hk : makeB (xl + yl) + lsp (stLen M st) yl k ≤ mulC (stLen s.mem st) xl yl := by
      rw [h.hdrM.2.1]; exact lsp_end h.h40 h.hlt hklt
    have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := h.core.live (by omega); omega
    clear hp1 hp2 hwA hF hFF ho
    janus_run [f94, f152, f160, f168, flr, ffp]
    all_goals try janus_simp
    refine ⟨⟨?_, ?_, ?_, ?_⟩, post_of h.core (MemFrame.refl _ _) v2 h.ext h.bud hk inv2 sb2 F2 LF2
      (by janus_frame) ?r0 ?r1 ?r2 hn' hv3 hnn3⟩
    all_goals janus_simp
  case hF2 => janus_frame
  case e152 => janus_simp; exact m1
  case e160 => janus_simp; exact m2
  case e168 => janus_simp; exact m3
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the loop exit**: the head with `m ≤ i` → `normB` → `lendB` -/
theorem lend (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {W zp zc st xp xl xc yp yl yc : Nat} {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (Lk : List (Nat × Nat)) (bk k tp tl tc : Nat) (S : State)
    (hH : LH R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S) (hge : xl ≤ (k + 1) * yl) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b L W zp zc st xp xl xc yp yl yc s s' := by
  have h := hH.lb
  obtain ⟨hW, hWs, hal, ha48, -, -, -, hcap, hc40, -, hx12, hy12, -⟩ := h.lay
  have hpc := hH.pc; have hsp := hH.sp; have h28 := hH.g; have h29 := hH.fp; have h18 := hH.x18
  have r3 := hH.r3
  have h40 := h.h40
  have a304 := h.a304; have b94 := h.b94; have p144 := h.p144; have n120 := h.n120; have c96 := h.c96
  obtain ⟨⟨-, ⟨-, -, -, hw0⟩, -⟩, -⟩ := h.core.pre
  have hsacc : S.mem.accessible (s.sp.toNat - 264) 264 true = true := by
    rw [h.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsacc' : S.mem.accessible (s.sp.toNat - 264) 352 true = true := by
    rw [h.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  obtain ⟨-, -, hpacc, hp48⟩ := h.core.live (by omega)
  have hpacc' : S.mem.accessible p (8 * (xl + yl)) false = true := by
    rw [h.fr.accessible]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hklt := hH.klt
  have hke : (k + 1) * yl = k * yl + yl := by rw [Nat.add_mul, Nat.one_mul]
  have i1 := toIntN (a := (k + 1) * yl) (by omega)
  have i2 := toIntN (a := xl) (by omega)
  have v2 : natVal S.mem p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl := by
    rw [hH.val, Nat.min_eq_right hge]
  janus_run [a304, b94, p144, n120, i1, i2] until [hnormB]
  refine normB impl s S.mem p c (xl + yl) (natVal S.mem p (xl + yl)) 2 _
    (fun S' n' hB hn' hv hnn => lendB impl h hklt v2 S' n' hB hn' hv hnn hl4 hl48)
    hcap (by omega) (by omega) hpacc' c96 (by decide) hal (by omega) (by omega) hsacc (xl + yl) _
    (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus_simp

end FvModexp.Arm64.NatMul
