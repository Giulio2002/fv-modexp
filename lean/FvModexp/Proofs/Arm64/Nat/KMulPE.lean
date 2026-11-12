import FvModexp.Proofs.Arm64.Nat.KMulPN

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the `z1 := stk.nat(2·n2 + 1)` call and the `z1`/`tx`/`ty` headers (natmul.go:204-206) → `KM1`

`kmCall`: from `KPm` at `(*stack).nat`'s entry, the call (`kmNatSum`, pre `kmNatPre`), then `0x1bc09c … 0x1bc108`:
`z1 = (0, t, kT, kT)`, `tx = (0, zp, n2, zc)`, `ty = (0, zp + 8·n2, n2, zc - n2)` (the `z[0:n2]` / `z[n2:2n2]` bound checks
refuted), `SP-352 := zc - n2`, `SP-336 := zp + 8·n2`; `KM1` at `0x1bc10c` by `kmFin`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (IntAt stkNatA tN')

set_option maxRecDepth 20000 in
/-- the frame reads the post-call segment needs, from `KPm` and the callee's frame -/
theorem km_rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 : Nat} {P : State} (h : KPm R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P)
    {M : Memory} (hF : MemFrame P.mem M (R.rt ++ winA P 4208 24 ++ stkWs P.mem st)) :
    M.readLE (s.sp.toNat + 32) 8 = zc ∧ M.readLE (s.sp.toNat - 344) 8 = n + 1 ∧
      M.readLE (s.sp.toNat - 352) 8 = kh n ∧ M.readLE (s.sp.toNat + 16) 8 = zp ∧
      M.readLE (s.sp.toNat - 360) 8 = 2 * kh n := by
  have F := h.pre.F
  have hW := F.hW; have hW' := kW_ge n
  obtain ⟨-, ⟨hal, hWs, ha48, -⟩, -, hout, -, -, -, -⟩ := F.env
  obtain ⟨-, -, hstw, -, -, -, hfw, -, -, -, -, -⟩ := F.stk
  clear F
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  have hspP : P.sp.toNat = s.sp.toNat - 448 := h.spN
  have eW : stW P.mem st = stW s.mem st := h.rd (by omega)
  have eL : stLen P.mem st = stLen s.mem st := h.rd (by omega)
  have eC : stCap P.mem st = stCap s.mem st := h.rd (by omega)
  have hrd : ∀ a k, s.sp.toNat - 456 ≤ a → a + k ≤ s.sp.toNat + 72 → (a + k ≤ s.sp.toNat - 440 ∨
      s.sp.toNat - 424 ≤ a) → M.readLE a k = P.mem.readLE a k := by
    intro a k h1 h2 h3
    refine hF.readLE _ _ ?_
    simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [hspP, eW, eL, eC]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega⟩
  exact ⟨(hrd _ _ (by omega) (by omega) (by omega)).trans h.s4, (hrd _ _ (by omega) (by omega) (by omega)).trans h.q104,
    (hrd _ _ (by omega) (by omega) (by omega)).trans h.q96, (hrd _ _ (by omega) (by omega) (by omega)).trans h.s2,
    (hrd _ _ (by omega) (by omega) (by omega)).trans h.q88⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `stk.nat` call and the headers after it** -/
theorem kmCall (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 : Nat}
    {P : State} (h : KPm R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (S : State) (t : Nat) (Lk : List (Nat × Nat)) (bk : Nat),
      KM1 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ReachesRet (LibMul.program.link impl) ret P Q := by
  have F := h.pre.F
  have h40 := F.n40; have hn12 := F.n12; have hzc := F.zc2; have hzc40 := F.zc40
  have hzl : zp + 8 * zc ≤ 2 ^ 48 := (F.zlive (by omega)).2.2.2
  have hst : st < 2 ^ 64 := by have := F.stk.2.1.2.2.2.1; omega
  clear F
  have hk := kh_facts h40
  have hkt : kT n < 2 ^ 64 := by simp only [kT, kh]; omega
  refine ReachesRet.call_regions (kmNatSum impl hap R hgr hmc hwb b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 (kT n)))
    h.pc ⟨?_, ⟨h.r0, h.r1, trivial⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · rw [h.r30, tN' (by omega)]; exact kn_ra hap (by decide) 139 (by omega)
  · rw [tN' hst, tN' hkt]; exact kmNatPre h
  obtain ⟨hkp, hq⟩ := hq
  rw [tN' hst, tN' hkt] at hq
  obtain ⟨hr0, hr1, hr2, Lq, bq, -, hok, hlen, hsame, hgrow, hF, -, -⟩ := id hq
  have eLP : stLen P.mem st = stLen s.mem st := by
    have F := h.pre.F
    obtain ⟨-, ⟨hal, hWs, ha48, -⟩, -⟩ := F.env
    obtain ⟨-, -, hstw, -⟩ := F.stk
    have := F.hW; have := kW_ge n
    simp only [win, outside_cons, outside_nil, and_true] at hstw
    exact h.rd (by omega)
  have ht48' := (Scr.of_post (m0 := P.mem) (k := kT n) hok hlen (by simp only [kT]; omega) hsame hgrow rfl).b48
  have hr0' := hr0 (by simp only [kT]; omega)
  rw [eLP] at hr0' ht48'
  have ht48 : stW s2.mem st + 8 * stLen s.mem st + 8 * kT n ≤ 2 ^ 48 := ht48'
  clear hok hlen hr0 hsame hgrow ht48' Lq bq
  obtain ⟨q480, q104, q96, q464, q88⟩ := km_rd h hF
  have hspP : P.sp.toNat = s.sp.toNat - 448 := h.spN
  have hsp2 : s2.sp = s.sp - 448#64 := hkp.1.trans h.sp
  have h28 : s2.regs 28 = s.regs 28 := hkp.2.1.trans h.g
  have h29 : s2.regs 29 = s.sp - 456#64 := hkp.2.2.1.trans h.fpr
  have h18 : s2.regs 18 = s.regs 18 := hkp.2.2.2.trans h.r18
  have hpc2 : s2.pc = BitVec.ofNat 64 0x1bc09c := by rw [hr, h.r30]
  have hsps : (s.sp - 448#64).toNat = s.sp.toNat - 448 := by rw [← h.sp]; exact hspP
  have hbig : 5408 ≤ s.sp.toNat ∧ s.sp.toNat + 72 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0 := by
    have F := h.pre.F
    obtain ⟨-, ⟨hal, hWs, ha48, -⟩, -⟩ := F.env
    have := F.hW; have := kW_ge n
    omega
  have hal2 : (s.sp - 448#64).toNat % 16 = 0 := by rw [hsps]; omega
  clear hkp hr
  have hsacc : s2.mem.accessible (s.sp.toNat - 456) 528 true = true := by
    have F := h.pre.F
    obtain ⟨-, ⟨hal, hWs, ha48, hw⟩, -⟩ := F.env
    have := F.hW; have := kW_ge n
    rw [hF.accessible, h.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : s2.mem.accessible (s.sp.toNat - 456) 528 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  have hqB := IntAS.Box.mk hq
  clear hq hF
  have hsh2 := kh_lsr n (by omega)
  have hsl1 : BitVec.ofNat 64 (kh n) <<< 1 = BitVec.ofNat 64 (2 * kh n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hs1 : BitVec.ofNat 64 zc - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (zc - kh n) := km_sub (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 (2 * kh n) - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (kh n) := by
    rw [km_sub (by omega) (by omega)]; congr 1; omega
  have hm := km_mask (kh n) zc (by omega) hzc40
  janus_run [q480, q104, q96, q464, q88, hsh2, hsl1, hs1, hs2, hm] until [0x1bc10c]
  refine (kmFin h hreg hqB.h ?fr ?reg ?q96 ?q112 ?z1 ?tx ?ty _ ⟨?pc, ?sp, ?g, ?fp, ?r18⟩ rfl).elim
    fun Lk hx => hx.elim fun bk hB => hK _ _ Lk bk hB
  case fr => simp only [kpcWs]; janus_frame
  case reg => simp only [Memory.regions_writeLE]
  case pc => rfl
  case sp => janus_simp
  case g => janus_simp
  case fp => janus_simp
  case r18 => janus_simp
  all_goals (try simp only [IntAt])
  all_goals janus_simp
  all_goals first | exact Nat.mod_eq_of_lt (by omega) | skip
  all_goals first | omega | (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.NatMul
