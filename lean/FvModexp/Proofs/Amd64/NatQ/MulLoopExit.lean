import FvModexp.Proofs.Amd64.NatQ.MulLoopEnd
import FvModexp.Proofs.Amd64.NatQ.MulLoopCall

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopExit.lean — TIGHT COSTS] `nat.mul` (amd64), chunk loop: the exit (`m ≤ i`) — `z.norm()`, the deferred `stk.restore`, the return

`m_restcall`: the closure call `CALL AX` at `0x5f0e61` (`mdsum`, `mRestPre`); `lendB`: from the deferred-call tests
`0x5f0e47` (`AtB`, bits `= 2`) — clear bit 1 (`0x56/0x57(SP')`), the closure, `TESTL $1` (`JE` taken), reload the
result, `ADDQ; POPQ BP; RET`, `post_of` with the facts of `lend_fin`; **`lend`**: the loop head with `m ≤ i` → `JLE`
→ `0x5f0dfd` (`AX` = bits) → `normB` → `lendB`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

set_option maxRecDepth 20000 in
/-- **the deferred closure call** at its entry (memory = `A` + the defer-bit / result stores + the return address) -/
theorem m_restcall (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {W zp zc st xp xl xc yp yl yc : Nat} {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    {Lk : List (Nat × Nat)} {bk spent : Nat} {A : Memory}
    (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent A) (S2 : State)
    (hpc : S2.rip = BitVec.ofNat 64 mDfn) (hsp : (S2.regs 4).toNat = (s.regs 4).toNat - 264)
    (h2 : (S2.regs 2).toNat = (s.regs 4).toNat - 64)
    (hF : MemFrame A S2.mem [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168),
      ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80), ((s.regs 4).toNat - 264, (s.regs 4).toNat - 256)])
    (hra : S2.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0e63)
    {n' : Nat} (e56 : S2.mem.readLE ((s.regs 4).toNat - 170) 1 = 0) (e152 : S2.mem.readLE ((s.regs 4).toNat - 104) 8 = p)
    (e160 : S2.mem.readLE ((s.regs 4).toNat - 96) 8 = n') (e168 : S2.mem.readLE ((s.regs 4).toNat - 88) 8 = c)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ s3 : State, s3.rip = BitVec.ofNat 64 0x5f0e63 → s3.regs 4 = S2.regs 4 + 8 → s3.regs 5 = S2.regs 5 →
      s3.regs 14 = S2.regs 14 → s3.xmm 15 = S2.xmm 15 → s3.fsBase = S2.fsBase → s3.df = S2.df →
      MemFrame A s3.mem [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168), ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80),
        ((s.regs 4).toNat - 272, (s.regs 4).toNat - 256), (st + 8, st + 16)] →
      s3.mem.readLE (st + 8) 8 = stLen M st →
      s3.mem.readLE ((s.regs 4).toNat - 170) 1 = 0 → s3.mem.readLE ((s.regs 4).toNat - 104) 8 = p →
      s3.mem.readLE ((s.regs 4).toNat - 96) 8 = n' → s3.mem.readLE ((s.regs 4).toNat - 88) 8 = c →
      s3.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      s3.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 →
      ReachesRet (LibMul.program.link impl) ret s3 Q) :
    ReachesRet (LibMul.program.link impl) ret S2 Q := by
  have hP := mRestPre h S2 hsp h2 hF hra
  have hD := mdsum impl
  rw [mdsum_entry] at hD
  obtain ⟨hW, hWs, hal, ha48, hout, -, -, hcap, -, hpw, -⟩ := h.lay
  have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  have hrd : ∀ x m, (x + m ≤ (s.regs 4).toNat - 170 ∨ (s.regs 4).toNat - 168 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 80 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 264 ∨ (s.regs 4).toNat - 256 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 h3 => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((S2.regs 2).toNat + 8) 8 = st := by
    rw [h2, hrd _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 64 + 8 = (s.regs 4).toNat - 56 by omega]
    exact h.dst
  have hdln : S2.mem.readLE ((S2.regs 2).toNat + 16) 8 = stLen M st := by
    rw [h2, hrd _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 64 + 16 = (s.regs 4).toNat - 48 by omega]
    exact h.dln
  refine ReachesRet.call_regions hD hpc hP fun s3 hr hq hreg => ?_
  obtain ⟨q4, q5, q14, q15, qfs, qdf, q7, q8⟩ := hq
  rw [hdst, hdln] at q7
  rw [hdst, hsp] at q8
  have hFF : MemFrame A s3.mem [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168),
      ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80), ((s.regs 4).toNat - 272, (s.regs 4).toNat - 256),
      (st + 8, st + 16)] :=
    hF.trans q8 fun x m ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hr3 : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat →
      s3.mem.readLE x m = S2.mem.readLE x m :=
    fun x m h1 h2 => q8.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hr4 : ∀ x m, (s.regs 4).toNat - 8 ≤ x → x + m ≤ (s.regs 4).toNat + 8 → s3.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact hK s3 (by rw [hr, retAddrOf, hsp, hra]) q4 q5 q14 q15 qfs qdf hFF q7
    (by rw [hr3 _ _ (by omega) (by omega)]; exact e56)
    (by rw [hr3 _ _ (by omega) (by omega)]; exact e152) (by rw [hr3 _ _ (by omega) (by omega)]; exact e160)
    (by rw [hr3 _ _ (by omega) (by omega)]; exact e168) ((hr4 _ _ (by omega) (by omega)).trans h.bp)
    ((hr4 _ _ (by omega) (by omega)).trans h.ra)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the deferred-call tests** (`0x5f0e47`, bits `= 2`, after `normB`): the closure, the return, `MPost` -/
theorem lendB (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {W zp zc st xp xl xc yp yl yc : Nat} {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    {Lk : List (Nat × Nat)} {bk k : Nat} {A : Memory}
    (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp xl yl k) A) (hklt : k * yl < xl)
    (hv : natVal A p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl)
    (hra0 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (S : State) (n' : Nat) (hB : AtB s S A p c n' 2) (hn' : n' ≤ xl + yl)
    (hvn : natVal A p n' = natVal A p (xl + yl)) (hnn : NatNorm A p n') :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hpc, h0, hsp, h14, h5, hx15, hfs, hdf, hF, m1, m2, m3⟩ := hB
  obtain ⟨hW, hWs, hal, ha48, hout, -, -, hcap, hc40, hpw, -⟩ := h.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 88) true = true := by
    have := h.core.pre.1.2.1.2.2; simp only [regSP] at this; exact this
  have hrd : ∀ x m, (x + m ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 80 ≤ x) → S.mem.readLE x m = A.readLE x m :=
    fun x m h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hp1 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 64 := by rw [hrd _ _ (by omega)]; exact h.dpt
  have hp2 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = mDfn := by rw [hrd _ _ (by omega)]; exact h.dfn
  have hwA : S.mem.accessible ((s.regs 4).toNat - 264) 352 true = true := by
    rw [hF.accessible, h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 256 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmd : mDfn < 140737488355328 := by decide
  clear hrd
  janus64_run [hp1, hp2, hsp'] until [mDfn]
  refine m_restcall impl h _ (n' := n') ?pc ?sp ?h2 ?hF2 ?ra ?e56 ?e152 ?e160 ?e168 ?cont
  case cont =>
    intro s3 q1 q4 q5 q14 q15 qfs qdf hFF hlen f56 f152 f160 f168 fbp fra
    have hwC : s3.mem.accessible ((s.regs 4).toNat - 264) 352 true = true := by
      rw [hFF.accessible, h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
    obtain ⟨hcF, ho, inv2, sb2, F2, LF2⟩ := lend_fin h hFF hlen
    have v2 : natVal s3.mem p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl := by
      rw [natVal_frame hFF ho, hv]
    have hv3 : natVal s3.mem p n' = natVal s3.mem p (xl + yl) := by
      rw [natVal_frame hFF (ho.of_sub (Nat.le_refl _) (by omega)), natVal_frame hFF ho, hvn]
    have hnn3 : NatNorm s3.mem p n' := by
      rcases hnn with h0 | h0
      · exact Or.inl h0
      · right; rw [hFF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h0
    have hk : makeB (xl + yl) + lsp xl yl k ≤ mulCQ xl yl := lsp_end h.h40 h.hlt hklt
    have hbud2 : b1 - (lsp xl yl k + stkR H M st) + stkR H s3.mem st ≤ bk := by
      rw [stkR_congr h.hdrM.2.2, stkR_congr hcF]; exact h.bud
    have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := h.core.live (by omega); omega
    have hsp3 : (s3.regs 4).toNat = (s.regs 4).toNat - 256 := by
      rw [q4]; simp only [BitVec.toNat_add]; janus64_simp; omega
    clear hp1 hp2 hwA hF hFF ho
    janus64_run [f56, f152, f160, f168, fbp, fra, hsp3, BitVec.msb_eq_decide]
    all_goals try janus64_simp
    refine ⟨⟨?_, ?_, ?_, ?_⟩, post_of h.core (MemFrame.refl _ _) v2 h.ext (Or.inl hbud2) hk inv2 sb2 F2 LF2
      (by janus_frame) ?fs ?df ?r0 ?r1 ?r2 hn' hv3 hnn3⟩
    all_goals try janus64_simp
    all_goals first
      | rfl
      | omega
      | exact qfs.trans hfs
      | exact qdf.trans hdf
      | fail "SHOW"
  case hF2 => janus_frame
  all_goals try janus64_simp
  all_goals first
    | rfl
    | omega
    | exact m1
    | exact m2
    | exact m3
    | fail "SHOW"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the loop exit**: the head with `m ≤ i` → `normB` → `lendB` -/
theorem lend (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {W zp zc st xp xl xc yp yl yc : Nat} {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hra0 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (Lk : List (Nat × Nat)) (bk k tp tl tc : Nat) (S : State)
    (hH : LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S) (hge : xl ≤ (k + 1) * yl) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  have h := hH.lb
  obtain ⟨hW, hWs, hal, ha48, -, -, -, hcap, hc40, -, hx12, hy12, -⟩ := h.lay
  have hpc := hH.pc; have hsp := hH.sp; have h14 := hH.g; have h5 := hH.bp
  have r2 := hH.r2
  have h40 := h.h40
  have x148 := h.x148; have b56 := h.b56; have p90 := h.p90; have n70 := h.n70; have c58 := h.c58
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 88) true = true := by
    have := h.core.pre.1.2.1.2.2; simp only [regSP] at this; exact this
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 256) 264 true = true := by
    rw [h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  obtain ⟨-, -, hpacc, hp48⟩ := h.core.live (by omega)
  have hpacc' : S.mem.accessible p (8 * (xl + yl)) false = true := by
    rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hklt := hH.klt
  have hke : (k + 1) * yl = k * yl + yl := by rw [Nat.add_mul, Nat.one_mul]
  have hsacc8 : S.mem.accessible ((s.regs 4).toNat - 256) 344 true = true := by
    rw [h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have i1 := toIntN (a := (k + 1) * yl) (by omega)
  have i2 := toIntN (a := xl) (by omega)
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 256 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have v2 : natVal S.mem p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl := by
    rw [hH.val, Nat.min_eq_right hge]
  janus64_run [x148, b56, p90, n70, i1, i2, hsp', BitVec.msb_eq_decide] until [hnormB]
  refine normB impl s S.mem p c (xl + yl) (natVal S.mem p (xl + yl)) 2 _
    (fun S' n' hB hn' hv hnn => lendB impl h hklt v2 hra0 S' n' hB hn' hv hnn)
    hcap (by omega) (by omega) hpacc' c58 (by decide) hal (by omega) (by omega) hsacc (xl + yl) _
    (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals try janus64_simp
  all_goals first
    | rfl
    | exact hH.x15
    | exact hH.fs
    | exact hH.df
    | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
