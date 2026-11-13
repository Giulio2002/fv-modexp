import FvModexp.Proofs.Amd64.NatQ.MulLoopClr
import FvModexp.Proofs.Common.DivmcBits

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopClrJ.lean — TIGHT COSTS] `nat.mul` (amd64), the chunk loop's prologue: from `0x5f0b05` (`KA`) through `clear(z[2n:])` and the defer record
to `(*stack).nat`'s entry (`LP`, via `lpOf`)

The slice `z[2n:]`: pointer `p + 16n` (mask `SUBQ; SARQ $63; ANDQ`, `c > 2n`), length `m - n` (`TESTQ` taken: `m > n`);
the bounds check `2n ≤ m + n` (`JA 0x5f0eb7`) is refuted. `memclrNoHeapPointers` is entered at `RSP - 264` (return
`0x5f0b51`); `stk.nat(2n)` likewise (return `0x5f0ba9`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held guard)

/-- the live set at `Mi` is outside the window -/
theorem LB0.lksep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {Mi : Memory} (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    ∀ r ∈ Lk, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 88 ≤ r.1 := by
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
set_option janus.callRegions true in
/-- **`KA → LP`**: `clear(z[2n:])`, the defer bits / record, the arguments of `stk.nat(2n)` -/
theorem lclr (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} (S : State)
    (h : KA R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S) (hx150 : s.xmm 15 = 0#128)
    (hdf0 : s.df = false) {ret : W64} {Q : State → Prop}
    (hK : ∀ P : State, LP R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P →
      ReachesRet (LibMul.program.link impl) ret P Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibMul.names
  have hmc' := MemclrNoHeapPointersLive64.of_codeIn hc hmc
  clear hc
  have hq := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, hc40, hpw, hx12, hy12, -⟩ := hq.lay
  have h40 := hq.h40; have hlt := hq.hlt
  have hsv : RunIface.Serves R := hq.core.pre.2.2.1
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [p + 8 * (2 * yl), 8 * (xl - yl)] := hsv.2.2.1 _ _ (by omega)
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hq.core.live (by omega)
  have hzacc : S.mem.accessible (p + 8 * (2 * yl)) (8 * (xl - yl)) true = true := by
    rw [hq.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hpacc (by omega) (by omega)
  have hpH : Held R Lk p (8 * c) := by
    rcases hq.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := hq.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact hq.ext.held (hq.core.ext.held (hzl (by omega)).2.1)
    · exact hq.ext.held (Or.inl hin1)
  have hzH : InRanges (p + 8 * (2 * yl)) (8 * (xl - yl)) Lk ∨ Outside (p + 8 * (2 * yl)) (8 * (xl - yl)) R.rt :=
    hpH.sub (by omega) (by omega)
  have hpg := hq.core.pg (by omega)
  have hzg' : Apart (p + 8 * (2 * yl)) (8 * (xl - yl)) ((s.regs 14).toNat + 16) 8 := by
    unfold Apart at hpg ⊢; omega
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hgQ := hq.grd
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨-, -, hw0⟩, -⟩, -⟩ := hq.core.pre
  simp only [Janus.Amd64.GoABI.stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hw0
  have hg2' : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hq.frE.accessible]; exact hg2
  have hg3' : S.mem.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 264 := by rw [hgQ]; omega
  have hga1 : (s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 264 - 4096 ∨ (s.regs 4).toNat - 240 ≤ (s.regs 14).toNat + 16 := by
    unfold Apart at hga; omega
  clear hg2 hg3
  have hL1 := hq.lksep
  have hinv := hq.inv
  have hsacc : S.mem.accessible ((s.regs 4).toNat - W) (W + 88) true = true := by rw [hq.frE.accessible]; exact hw0
  clear hw0
  have hstacc : S.mem.accessible st 24 true = true := hq.sok.2.2.1
  have hst48 : st + 24 ≤ 2 ^ 48 := hq.sok.2.2.2.1
  have hko := hq.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  have hpst := hq.core.pst (by omega)
  unfold Apart at hpst
  have q88 := hq.n88; have q58 := hq.c58; have q90 := hq.p90; have q70 := hq.n70; have q8 := hq.sb8
  have q56 := h.b56; have r10 := h.r10
  have hpc := h.pc; have hsp := h.sp; have h14 := h.g; have h5 := h.bp
  have hx15 : S.xmm 15 = 0#128 := by rw [h.x15]; exact hx150
  have hdf : S.df = false := by rw [h.df]; exact hdf0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 256 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsub : BitVec.ofNat 64 (xl + yl) - BitVec.ofNat 64 (2 * yl) = BitVec.ofNat 64 (xl - yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsl4 : BitVec.ofNat 64 yl <<< 4 = BitVec.ofNat 64 (16 * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hsl3 : BitVec.ofNat 64 (xl - yl) <<< 3 = BitVec.ofNat 64 (8 * (xl - yl)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hd : BitVec.ofNat 64 (2 * yl) - BitVec.ofNat 64 c = 0#64 - BitVec.ofNat 64 (c - 2 * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmask : ((BitVec.ofNat 64 (2 * yl) - BitVec.ofNat 64 c).sshiftRight 63 &&& BitVec.ofNat 64 (16 * yl)) =
      BitVec.ofNat 64 (16 * yl) := by
    rw [hd]; exact neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hmask' : (BitVec.ofNat 64 (16 * yl) &&& (BitVec.ofNat 64 (2 * yl) - BitVec.ofNat 64 c).sshiftRight 63) =
      BitVec.ofNat 64 (16 * yl) := by rw [BitVec.and_comm]; exact hmask
  have hpa : BitVec.ofNat 64 p + BitVec.ofNat 64 (16 * yl) = BitVec.ofNat 64 (p + 8 * (2 * yl)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus64_run [q88, q58, q90, q70, r10, hsp', hsub, hsl4, hsl3, hmask, hmask', hpa, BitVec.msb_eq_decide]
    until [0x5f0b51] calls [hmc' Lk bk]
  janus_grab 4096 as hFc
  janus_grab Mem.Zeroed as hz
  janus_grab LiveFrame as hLFc
  clear hinv
  janus_grab view as hinvw
  have hFp : MemFrame S.mem (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 264) 8 6228817)
      [((s.regs 4).toNat - 264, (s.regs 4).toNat - 264 + 8)] := by janus_frame
  have hF1 := hFp.trans hFc (rs'' := R.rt ++ [((s.regs 4).toNat - 264 - 4096, (s.regs 4).toNat - 264 + 24)] ++
      [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))]) fun a k ho => by
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨by omega, ⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  have hLF1 := LiveFrame.trans (LiveFrame.of_win hFp fun r hr => by
      have := hL1 r hr; simp only [outside_cons, outside_nil, and_true]; omega) hLFc fun _ _ h => h
  have hrw : ∀ x m, (s.regs 4).toNat - 240 ≤ x → x + m ≤ (s.regs 4).toNat + 88 →
      Outside x m (R.rt ++ [((s.regs 4).toNat - 264 - 4096, (s.regs 4).toNat - 264 + 24)] ++
        [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))]) :=
    fun x m h1 h2 => by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  have w56 := (hF1.readLE _ _ (hrw ((s.regs 4).toNat - 170) 1 (by omega) (by omega))).trans q56
  have w8 := (hF1.readLE _ _ (hrw ((s.regs 4).toNat - 72) 8 (by omega) (by omega))).trans q8
  have w88 := (hF1.readLE _ _ (hrw ((s.regs 4).toNat - 120) 8 (by omega) (by omega))).trans q88
  have hwacc := (hF1.accessible ((s.regs 4).toNat - W) (W + 88) true).trans hsacc
  have hwst := (hF1.accessible st 24 true).trans hstacc
  clear hrw hsacc hstacc hzH hzacc hok hL1 hgQ hg2' hg3' hga1 hFc hLFc hFp
  janus64_run [w56, w8, w88] until [stkNatM]
  refine hK _ (lpOf h hF1 hLF1 hinvw hz hrg1 _ ?fs ?regP ?pc ?sp ?g ?bp ?fsb ?df ?x15 ?r0 ?r3 ?ra ?q56 ?q57 ?qdfn
    ?qdst ?qdln ?qdpt)
  case fs => janus_frame
  case fsb => janus64_simp; exact h.fs
  all_goals janus64_simp

end FvModexp.Amd64.Q.NatMul
