import FvModexp.Proofs.Amd64.NatQ.KMulPN
import FvModexp.Proofs.Amd64.NatQ.KMulI
import FvModexp.Proofs.Amd64.NatQ.KSqrPQ
import FvModexp.Proofs.Amd64.NatQ.KSqrCall

set_option autoImplicit false

/-!
# [amd64 port (divmc s53) of the Q-form Arm64/NatQ/KMulPE.lean — TIGHT COSTS] `karatsuba` (amd64): the `z1 := stk.nat(2·n2 + 1)` call and the `z1`/`tx`/`ty` headers (natmul.go:204-206) → `KM1`

`kmCall`: from `KPm` at `(*stack).nat`'s entry (return `0x5f209b` pushed at `RSP - 456`), the call (`kmNatSum`, pre
`kmNatPre`), then `0x5f209b … 0x5f2141`: `z1 = (0, t, kT, kT)` at `RSP - 264`, `tx = (0, zp, n2, zc)` at `RSP - 296`,
`ty = (0, zp + 8·n2, n2, zc - n2)` at `RSP - 328` (the `z[0:n2]` / `z[n2:2n2]` bound checks refuted),
`RSP - 360 := zc - n2`, `RSP - 336 := zp + 8·n2`; `KM1` at `0x5f2149` by `kmFin`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (IntAt stkNatA tN' bv_sub_ofNat bv_add_ofNat kmask)

set_option maxRecDepth 20000 in
/-- the frame reads the post-call segment needs, from `KPm` and the callee's frame -/
theorem km_rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 : Nat} {P : State} (h : KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P)
    {M : Memory} (hF : MemFrame P.mem M (R.rt ++ win P 4192 24 ++ stkWs P.mem st)) :
    M.readLE ((s.regs 4).toNat + 56) 8 = zc ∧ M.readLE ((s.regs 4).toNat - 344) 8 = kh n ∧
      M.readLE ((s.regs 4).toNat - 352) 8 = 8 * kh n ∧ M.readLE ((s.regs 4).toNat + 40) 8 = zp ∧
      M.readLE ((s.regs 4).toNat - 360) 8 = 2 * kh n := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have F := h.pre.F
  obtain ⟨-, -, hstw, -, -, -, hfw, -, -, -, -, -, -, -, -⟩ := F.stk
  clear F
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  have hspP := h.sp
  have eW : stW P.mem st = stW s.mem st := h.rd (by omega)
  have eL : stLen P.mem st = stLen s.mem st := h.rd (by omega)
  have eC : stCap P.mem st = stCap s.mem st := h.rd (by omega)
  have hrd : ∀ a k, (s.regs 4).toNat - 432 ≤ a → a + k ≤ (s.regs 4).toNat + 72 →
      M.readLE a k = P.mem.readLE a k := by
    intro a k h1 h2
    refine hF.readLE _ _ ?_
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [hspP, eW, eL, eC]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega, by omega⟩
  exact ⟨(hrd _ _ (by omega) (by omega)).trans h.s4, (hrd _ _ (by omega) (by omega)).trans h.q104,
    (hrd _ _ (by omega) (by omega)).trans h.q96, (hrd _ _ (by omega) (by omega)).trans h.s2,
    (hrd _ _ (by omega) (by omega)).trans h.q88⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `stk.nat` call and the headers after it** -/
theorem kmCall (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 : Nat}
    {P : State} (h : KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) {ret : W64} {Q : State → Prop}
    (hK : ∀ (S : State) (t : Nat) (Lk : List (Nat × Nat)) (bk : Nat),
      KM1 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ReachesRet (LibMul.program.link impl) ret P Q := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hzl2, hzc40, hout, hgr', hga⟩ := h.lay
  have F := h.pre.F
  have hzl : zp + 8 * zc ≤ 2 ^ 48 := (F.zlive (by omega)).2.2.2
  have hst : st < 2 ^ 64 := by have := F.stk.2.1.2.2.2.1; omega
  obtain ⟨-, -, hstw, -⟩ := F.stk
  obtain ⟨-, ⟨-, -, hw⟩, -⟩ := F.env
  simp only [regSP] at hw
  clear F
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hk : kh n ≤ n ∧ 0 < kh n ∧ 2 * kh n ≤ n + 1 := by simp only [kh]; omega
  have hkt : kT n < 2 ^ 64 := by simp only [kT, kh]; omega
  have hrd : P.mem.readLE (P.regs 4).toNat 8 = 0x5f1da0 + 0x2fb := by rw [h.sp, h.ra]
  refine ReachesRet.call_regions (kmNatSum impl hap R hgr hmc hwb H b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 (kT n)))
    h.pc ⟨?_, h.x15.trans hx150, by simp [ArgsFrom64, argReg, intArgRegs, h.r0, h.r1], h.df.trans hdf0, ?_⟩
    fun s2 hr hq hreg => ?_
  · simp only [regSP]; rw [hrd]; exact kn_ra hap (by decide) 0x2fb (by decide)
  · rw [tN' hst, tN' hkt]; exact kmNatPre h
  obtain ⟨hkp, hq⟩ := hq
  rw [tN' hst, tN' hkt] at hq
  obtain ⟨efs, edf, hr0, hr1, hr2, Lq, bq, -, hok, hlen, hsame, hgrow, hF, -, -⟩ := id hq
  have eLP : stLen P.mem st = stLen s.mem st := h.rd (by omega)
  have hkT0 : 0 < kT n := by simp only [kT]; omega
  have ht48' := (Scr.of_post (m0 := P.mem) (k := kT n) hok hlen hkT0 hsame hgrow rfl).b48
  have hr0' := hr0 hkT0
  rw [eLP] at hr0' ht48'
  have ht48 : stW s2.mem st + 8 * stLen s.mem st + 8 * kT n ≤ 2 ^ 48 := ht48'
  clear hok hlen hr0 hsame hgrow ht48' Lq bq
  obtain ⟨q56, q344, q352, q40, q360⟩ := km_rd h hF
  have hsacc : s2.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hF.accessible, h.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hF hw
  have hsp2 : s2.regs 4 = s.regs 4 - 448#64 := by rw [hkp.1]; exact sp_add8K h.sp (by omega)
  have h14 : s2.regs 14 = s.regs 14 := hkp.2.2.1.trans h.g
  have h5 : s2.regs 5 = s.regs 4 - 8#64 := hkp.2.1.trans h.fpr
  have hx2 : s2.xmm 15 = s.xmm 15 := hkp.2.2.2.trans h.x15
  have hfs2 : s2.fsBase = s.fsBase := efs.trans h.fs
  have hdf2 : s2.df = s.df := edf.trans h.df
  have hpc2 : s2.rip = BitVec.ofNat 64 0x5f209b := by rw [hr, retAddrOf, hrd]
  clear hkp hr efs edf
  have hqB := IntAS.Box.mk hq
  clear hq
  have esp : (s.regs 4 - 448#64).toNat = (s.regs 4).toNat - 448 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs1 : BitVec.ofNat 64 zc - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (zc - kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 (2 * kh n) - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (kh n) := by
    rw [bv_sub_ofNat (by omega) (by omega)]; congr 1; omega
  have hm := kmask (zc - kh n) (8 * kh n) (by omega) (by omega)
  have hza : BitVec.ofNat 64 zp + BitVec.ofNat 64 (8 * kh n) = BitVec.ofNat 64 (zp + 8 * kh n) :=
    bv_add_ofNat (by omega)
  janus64_run [q56, q344, q352, q40, q360, esp, hs1, hs2, hm, hza, BitVec.msb_eq_decide] until [0x5f2149]
  refine (kmFin h hreg hqB.h ?fr ?reg ?q88 ?q112 ?z1 ?tx ?ty _ ⟨?pc, ?sp, ?g, ?fp, ?fs, ?df, ?x15⟩ rfl).elim
    fun Lk hx => hx.elim fun bk hB => hK _ _ Lk bk hB
  case fr => simp only [kpcWs]; janus_frame
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case pc => rfl
  all_goals (try simp only [IntAt])
  all_goals janus64_simp
  all_goals first
    | exact Nat.mod_eq_of_lt (by omega)
    | exact hfs2
    | exact hdf2
    | exact hx2
    | exact h14
    | skip
  all_goals first | omega | (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.Q.NatMul
