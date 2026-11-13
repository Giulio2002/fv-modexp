import FvModexp.Proofs.Arm64.NatQ.MulLoopClr
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.OmegaOnly

/-!
# [Q-form copy of Arm64/Nat/MulLoopClrJ.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), the chunk loop's prologue: from `0x1bb054` (`KA`) through `clear(z[2n:])` and the defer record
to `(*stack).nat`'s entry (`LP`, via `lpOf`)

The slice `z[2n:]`: pointer `p + 16n` (mask `NEG; AND R4->63`, `c > 2n`), length `m - n`; the bounds check
`2n ≤ m + n` (`BCC`) is refuted.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held guard)

/-- the live set at `Mi` is outside the window -/
theorem LB0.lksep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {Mi : Memory} (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    ∀ r ∈ Lk, r.1 + (r.2 - r.1) ≤ s.sp.toNat - W ∨ s.sp.toNat + 88 ≤ r.1 := by
  obtain ⟨-, -, -, -, hout, -⟩ := h.lay
  have hLs1 := h.wsep
  obtain ⟨ns, hLk, hn, -⟩ := h.ext
  intro r hr
  rw [hLk] at hr
  rcases List.mem_append.1 hr with hr | hr
  · have := hLs1 r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  · have := NatSub.outside_of_inRanges hout (hn r hr).1; omega

set_option maxHeartbeats 4000000 in
/-- the precondition of `memclrNoHeapPointers(p + 16n, 8(m - n))` at its entry `X` (from `KA`) -/
theorem lclrPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} {S : State}
    (h : KA R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S) (X : State)
    (hsp : X.sp.toNat = s.sp.toNat - 256) (h28 : X.regs 28 = s.regs 28)
    (h30a : (X.regs 30).toNat % 4 = 0) (h30b : (X.regs 30).toNat < 2 ^ 48) (hm : X.mem = S.mem)
    (h0 : (X.regs 0).toNat = p + 8 * (2 * yl)) (h1 : (X.regs 1).toNat = 8 * (xl - yl)) :
    Mem.EqPre 4096 2 X ∧
      LiveMemAt R (cA "runtime.memclrNoHeapPointers") [(X.regs 0).toNat, (X.regs 1).toNat] Lk bk X
        (calleeStack X 4096 2) ∧
      LiveDest R Lk X 4096 2 (X.regs 0).toNat (X.regs 1).toNat := by
  have hq := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, hc40, hpw, hx12, hy12, -⟩ := hq.lay
  have h40 := hq.h40; have hlt := hq.hlt
  have hsv : RunIface.Serves R := hq.core.pre.2.2.1
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [p + 8 * (2 * yl), 8 * (xl - yl)] := hsv.2.2.1 _ _ (by omega)
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hq.core.live (by omega)
  have hzacc : X.mem.accessible (p + 8 * (2 * yl)) (8 * (xl - yl)) true = true := by
    rw [hm, hq.fr.accessible]; exact Memory.accessible_mono _ hpacc (by omega) (by omega)
  have hpH : Held R Lk p (8 * c) := by
    rcases hq.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := hq.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact hq.ext.held (hq.core.ext.held (hzl (by omega)).2.1)
    · exact hq.ext.held (Or.inl hin1)
  have hzH : InRanges (p + 8 * (2 * yl)) (8 * (xl - yl)) Lk ∨ Outside (p + 8 * (2 * yl)) (8 * (xl - yl)) R.rt :=
    hpH.sub (by omega) (by omega)
  have hgQ := hq.grd
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := hq.core.pre.1
  have hg2' : X.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hm, hq.frE.accessible]; exact hg2
  have hg3' : X.mem.readLE ((s.regs 28).toNat + 16) 8 + (4096 + 256) < s.sp.toNat := by rw [hm, hgQ]; omega
  have hL1 := hq.lksep
  have hinv := hq.inv
  obtain ⟨⟨-, ⟨-, -, -, hw0⟩, -⟩, -⟩ := hq.core.pre
  have hsacc : X.mem.accessible (s.sp.toNat - W) (s.sp.toNat + 88 - (s.sp.toNat - W)) true = true := by
    rw [hm, hq.frE.accessible, show s.sp.toNat + 88 - (s.sp.toNat - W) = W + 88 by omega]; exact hw0
  unfold Apart at hga
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hc := call_pre R Lk bk 0 (cA "runtime.memclrNoHeapPointers") [(X.regs 0).toNat, (X.regs 1).toNat]
    (s := { X with sp := s.sp }) (S := X) (lo := s.sp.toNat - W) (hi := s.sp.toNat + 88) (stack := 4096) (nargs := 2)
    (fr := 256) (by rw [h28]; exact hg1) (by simp only; rw [h28]; exact hg2') (by simp only; rw [h28]; omega)
    (by simp only [outside_cons]; rw [h28]; exact ⟨by omega, hgr⟩) ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩ rfl
    (by simp only; omega) (by rw [hsp]; omega) h30a h30b (by decide) (by omega) (by omega) (by omega) (by omega) hsacc
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show s.sp.toNat + 88 - (s.sp.toNat - W) = W + 88 by omega]; exact hout)
    (fun r hr => by have := hL1 r hr; simp only [outside_cons, outside_nil, and_true]; omega)
    (by rw [h0, h1]; exact hok) (by rw [h28, hm]; exact hinv) (Nat.zero_le _)
  obtain ⟨hco, ⟨hgk, hgout⟩, ⟨hok', hinv', -, hs1, hs2⟩⟩ := hc
  refine ⟨⟨(guardOK_iff _ _).1 hgk, hco, hgout⟩, ⟨hok', hinv', hs1, hs2⟩, ⟨by rw [h0, h1]; omega,
    by rw [h0, h1]; exact hzacc, ?_, by rw [h0, h1]; exact hzH⟩⟩
  rw [h0, h1]; simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [hsp]; omega

set_option maxHeartbeats 4000000 in
/-- the call `memclrNoHeapPointers(p + 16n, 8(m - n))` from its entry `X` back to `0x1bb088` -/
theorem lclrC (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat}
    {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat}
    {S : State} (h : KA R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S)
    (hmc' : MemclrNoHeapPointersLive (LibMul.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : X.sp = s.sp - 256#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 264#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 0x1bb088) (hm : X.mem = S.mem)
    (h0 : (X.regs 0).toNat = p + 8 * (2 * yl)) (h1 : (X.regs 1).toNat = 8 * (xl - yl)) {ret : BitVec 64}
    {Q : State → Prop}
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 0x1bb088 → T.sp = s.sp - 256#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 264#64 → T.regs 18 = s.regs 18 →
      MemFrame S.mem T.mem (R.rt ++ [(s.sp.toNat - 256 - 4096, s.sp.toNat - 256 - 8),
        (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 24)] ++ [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))]) →
      LiveFrame S.mem T.mem Lk [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))] →
      R.inv bk Lk (s.regs 28).toNat (view R.rt Lk T.mem) →
      Mem.Zeroed T.mem (p + 8 * (2 * yl)) (8 * (xl - yl)) → T.mem.regions = S.mem.regions →
      ReachesRet (LibMul.program.link impl) ret T Q) :
    ReachesRet (LibMul.program.link impl) ret X Q := by
  have hq := h.lq
  obtain ⟨hW, hWs, -, -, -, -⟩ := hq.lay
  have hspn : X.sp.toNat = s.sp.toNat - 256 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  refine ReachesRet.call_regions (hmc' Lk bk) hpc
    (lclrPre h X hspn h28 (by rw [h30]; decide) (by rw [h30]; decide) hm h0 h1) ?_
  intro T hT ⟨jk, fl, vv, w, ex, ep, hs, hFc, hLFc, hinvw, hz⟩ hrg
  subst hs
  rw [h0, h1] at hFc hLFc hz
  rw [hm] at hFc hLFc hrg
  rw [h28] at hinvw
  simp only [calleeStack, hspn] at hFc
  refine k _ (hT.trans h30) hsp (by simp only [retStateX, callRegs, h28]; simp)
    (by simp only [retStateX, callRegs, h29]; simp) (by simp only [retStateX, callRegs, h18]; simp)
    (hFc.mono fun a n ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, ho.1.2.1, by omega⟩, by omega⟩) hLFc hinvw hz hrg

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- **`KA → LP`**: `clear(z[2n:])`, the defer bits / record, the arguments of `stk.nat(2n)` -/
theorem lclr (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} (S : State)
    (h : KA R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S) {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ P : State, LP R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P →
      ReachesRet (LibMul.program.link impl) ret P Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibMul.names
  have hmc' := MemclrNoHeapPointersLive.of_codeIn hc hmc
  clear hc
  have hq := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, hc40, hpw, hx12, hy12, -⟩ := hq.lay
  have h40 := hq.h40; have hlt := hq.hlt
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hq.core.live (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hsacc : S.mem.accessible (s.sp.toNat - W) (W + 88) true = true := by
    obtain ⟨⟨-, ⟨-, -, -, hw0⟩, -⟩, -⟩ := hq.core.pre
    rw [hq.frE.accessible]; exact hw0
  have hstacc : S.mem.accessible st 24 true = true := hq.sok.2.2.1
  have hst48 : st + 24 ≤ 2 ^ 48 := hq.sok.2.2.2.1
  have hko := hq.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  have hpst := hq.core.pst (by omega)
  unfold Apart at hpst
  have q120 := hq.n120; have q96 := hq.c96; have q144 := hq.p144; have q184 := hq.s184; have q136 := hq.n136
  have q94 := h.b94; have r10 := h.r10
  have hpc := h.pc; have hsp := h.sp; have h28 := h.g; have h29 := h.fp; have h18 := h.x18
  have hsh : BitVec.ofNat 64 yl <<< 1 = BitVec.ofNat 64 (2 * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hmask : (BitVec.ofNat 64 yl &&& (0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 (2 * yl))).sshiftRight 63) =
      BitVec.ofNat 64 yl := by
    rw [BitVec.and_comm]
    have hd : (BitVec.ofNat 64 c - BitVec.ofNat 64 (2 * yl)).toNat = c - 2 * yl := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    exact neg_sshr63_and _ _ (by rw [hd]; omega) (by rw [hd]; omega)
  have e1 : (18446744073709551616 - 2 * yl + (xl + yl)) % 18446744073709551616 = xl - yl := by omega
  have hspn : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  janus_run [q120, q96, q144, q94, r10, hsh, hmask, e1] until [cA "runtime.memclrNoHeapPointers"]
  refine lclrC impl h hmc' _ ?pc ?sp ?g ?fp ?x18 ?r30 ?m ?r0 ?r1 (k := fun T hpc hsp h28 h29 h18 hF1 hLFc hinvw hz hrg1 => ?k)
  case pc => janus_simp
  case sp => janus_simp
  case g => janus_simp
  case fp => janus_simp
  case x18 => janus_simp
  case r30 => janus_simp
  case m => rfl
  case r0 => janus_simp; omega
  case r1 => janus_simp; omega
  clear q120 q96 q144 r10 hsh hmask e1
  obtain ⟨hW', hWs', -, -, hout', -⟩ := hq.lay
  have h264 : 264 ≤ s.sp.toNat := by omega
  have hrw : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat + 88 → (x + m ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 232 ≤ x) →
      T.mem.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 h3 => hF1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout'.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have w94 : T.mem.readLE (s.sp.toNat - 162) 1 = 0 := by rw [hrw _ _ (by omega_only [h264]) (by omega_only [h264]) (by omega_only [h264])]; exact q94
  have w184 : T.mem.readLE (s.sp.toNat - 72) 8 = st := by rw [hrw _ _ (by omega_only [h264]) (by omega_only [h264]) (by omega_only [h264])]; exact q184
  have w136 : T.mem.readLE (s.sp.toNat - 120) 8 = 2 * yl := by rw [hrw _ _ (by omega_only [h264]) (by omega_only [h264]) (by omega_only [h264])]; exact q136
  have hwacc : T.mem.accessible (s.sp.toNat - W) (W + 88) true = true := by rw [hF1.accessible]; exact hsacc
  have hwst : T.mem.accessible st 24 true = true := by rw [hF1.accessible]; exact hstacc
  have hln := Memory.readLE_lt T.mem (st + 8) 8
  clear hrw h264 hsacc hstacc
  janus_run [w94, w184, w136] until [0x1b3970]
  refine hK _ (lpOf h hF1 hLFc hinvw hz hrg1 _ ?fs ?regP ?pc ?sp ?g ?fp ?x18 ?r0 ?r1 ?r30 ?q94 ?q95 ?qdfn ?qdst ?qdln
    ?qdpt)
  case fs => janus_frame
  all_goals janus_simp

end FvModexp.Arm64.Q.NatMul
