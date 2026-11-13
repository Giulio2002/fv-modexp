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
  have hsv : RunIface.Serves R := hq.core.pre.2.2.1
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [p + 8 * (2 * yl), 8 * (xl - yl)] := hsv.2.2.1 _ _ (by omega)
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hq.core.live (by omega)
  have hzacc : S.mem.accessible (p + 8 * (2 * yl)) (8 * (xl - yl)) true = true := by
    rw [hq.fr.accessible]; exact Memory.accessible_mono _ hpacc (by omega) (by omega)
  have hpH : Held R Lk p (8 * c) := by
    rcases hq.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := hq.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact hq.ext.held (hq.core.ext.held (hzl (by omega)).2.1)
    · exact hq.ext.held (Or.inl hin1)
  have hzH : InRanges (p + 8 * (2 * yl)) (8 * (xl - yl)) Lk ∨ Outside (p + 8 * (2 * yl)) (8 * (xl - yl)) R.rt :=
    hpH.sub (by omega) (by omega)
  have hpg := hq.core.pg (by omega)
  have hzg' : Apart (p + 8 * (2 * yl)) (8 * (xl - yl)) ((s.regs 28).toNat + 16) 8 := by
    unfold Apart at hpg ⊢; omega
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hgQ := hq.grd
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := hq.core.pre.1
  have hg2' : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hq.frE.accessible]; exact hg2
  have hg3' : S.mem.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 256 := by rw [hgQ]; omega
  have hga1 : (s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 256 - 4096 ∨ s.sp.toNat - 256 - 8 ≤ (s.regs 28).toNat + 16 := by
    unfold Apart at hga; omega
  have hga2 : (s.regs 28).toNat + 16 ≤ s.sp.toNat - 256 ∨ s.sp.toNat - 256 + 8 ≤ (s.regs 28).toNat := by
    unfold Apart at hga; omega
  clear hg2 hg3
  have hL1 := hq.lksep
  have hinv := hq.inv
  obtain ⟨⟨-, ⟨-, -, -, hw0⟩, -⟩, -⟩ := hq.core.pre
  have hsacc : S.mem.accessible (s.sp.toNat - W) (W + 88) true = true := by rw [hq.frE.accessible]; exact hw0
  clear hw0
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
  have hzH' : InRanges (p + yl * 16) (8 * (xl - yl)) Lk ∨ Outside (p + yl * 16) (8 * (xl - yl)) R.rt := by
    rw [show p + yl * 16 = p + 8 * (2 * yl) by omega]; exact hzH
  janus_run [q120, q96, q144, q94, r10, hsh, hmask, e1] until [0x1bb088] calls [hmc' Lk bk]
  rename_i jk fl vv w ex ep hFc hLFc hinvw hz
  have hF1 : MemFrame S.mem w (R.rt ++ [(s.sp.toNat - 256 - 4096, s.sp.toNat - 256 - 8),
      (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 24)] ++ [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))]) :=
    hFc.mono fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, ho.1.2.1, by omega⟩, by omega⟩
  rw [show p + yl * 16 = p + 8 * (2 * yl) by omega] at hLFc hz
  obtain ⟨hW', hWs', -, -, hout', -⟩ := hq.lay
  have h264 : 264 ≤ s.sp.toNat := by omega
  have hrw : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat + 88 → (x + m ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 232 ≤ x) →
      w.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 h3 => hF1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout'.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have w94 : w.readLE (s.sp.toNat - 162) 1 = 0 := by rw [hrw _ _ (by omega_only [h264]) (by omega_only [h264]) (by omega_only [h264])]; exact q94
  have w184 : w.readLE (s.sp.toNat - 72) 8 = st := by rw [hrw _ _ (by omega_only [h264]) (by omega_only [h264]) (by omega_only [h264])]; exact q184
  have w136 : w.readLE (s.sp.toNat - 120) 8 = 2 * yl := by rw [hrw _ _ (by omega_only [h264]) (by omega_only [h264]) (by omega_only [h264])]; exact q136
  have hwacc : w.accessible (s.sp.toNat - W) (W + 88) true = true := by rw [hF1.accessible]; exact hsacc
  have hwst : w.accessible st 24 true = true := by rw [hF1.accessible]; exact hstacc
  have hln := Memory.readLE_lt w (st + 8) 8
  clear hrw h264 hsacc hstacc hzH hzH' hzacc hok hL1 hinv hgQ hg2' hg3' hga1 hga2
  janus_run [w94, w184, w136] until [0x1b3970]
  refine hK _ (lpOf h hF1 hLFc hinvw hz hrg1 _ ?fs ?regP ?pc ?sp ?g ?fp ?x18 ?r0 ?r1 ?r30 ?q94 ?q95 ?qdfn ?qdst ?qdln
    ?qdpt)
  case fs => janus_frame
  all_goals janus_simp

end FvModexp.Arm64.Q.NatMul
