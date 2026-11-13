import FvModexp.Proofs.Amd64.NatQ.KMulPD
import FvModexp.Proofs.Amd64.NatQ.KMulLoop

set_option autoImplicit false

/-!
# [amd64 port (divmc s51) of the Q-form Arm64/NatQ/KMulPB.lean — TIGHT COSTS] `karatsuba` (amd64): the prologue between the inlined `norm` loops (natmul.go:197-198)

* `kmPB1`: `x0` loop exit (`0x5f1e65`, `DX = len x0`; the `x[:i]` bound check refuted) → `x1` loop head
  (`0x5f1ea5`: `R8 = n - n2`, base `R9 = xp + 8·n2`, `RSP+32 := stk` (the loop's `AX` reload), `RSP-368 := xc - n2`);
* `kmPB2`: `x1` loop exit (`0x5f1ebc`, `R8 = len x1`) → `y0` loop head (`0x5f1f22`): the `x0`/`x1` headers
  (`RSP-48`, `RSP-80`) stored, `RSP+48 := 2n`, `R15 = DX = n2`, base `CX = yp`;
* `kmPB3`: `y0` loop exit (`0x5f1f31`, `R15 = len y0`) → `y1` loop head (`0x5f1f67`: `R10 = n - n2`, base
  `SI = yp + 8·n2`, `R9 = yc - n2`, `R8 = yc`).
(Mechanics as Amd64/NatQ/KSqrPB.kPB.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (bv_sub_ofNat bv_add_ofNat kmask kmask' kshl3 IntAt)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPB1 (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {lx0 : Nat} (hl0 : lx0 ≤ kh n)
    (hpc : S.rip = BitVec.ofNat 64 kmLX0x) (hsp : S.regs 4 = s.regs 4 - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 zp)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : S.regs 7 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = BitVec.ofNat 64 (n + 1))
    (h12 : S.regs 12 = BitVec.ofNat 64 (kh n))
    (h2 : S.regs 2 = BitVec.ofNat 64 lx0) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx : S.xmm 15 = s.xmm 15)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.rip = BitVec.ofNat 64 kmLX1 → S2.regs 4 = s.regs 4 - 448#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 3 = BitVec.ofNat 64 zp → S2.regs 1 = BitVec.ofNat 64 (2 * n) →
      S2.regs 7 = BitVec.ofNat 64 zc → S2.regs 6 = BitVec.ofNat 64 xp → S2.regs 8 = BitVec.ofNat 64 (n - kh n) →
      S2.regs 9 = BitVec.ofNat 64 (xp + 8 * kh n) → S2.regs 10 = BitVec.ofNat 64 n →
      S2.regs 11 = BitVec.ofNat 64 (n + 1) → S2.regs 12 = BitVec.ofNat 64 (8 * kh n) →
      S2.regs 13 = BitVec.ofNat 64 xc → S2.regs 15 = BitVec.ofNat 64 (kh n) →
      S2.regs 2 = BitVec.ofNat 64 lx0 → S2.regs 14 = s.regs 14 → S2.regs 5 = s.regs 4 - 8#64 →
      S2.fsBase = s.fsBase → S2.df = s.df → S2.xmm 15 = s.xmm 15 →
      KQm R b H L W st zp zc xp n xc yp yc s S2.mem → S2.mem.readLE ((s.regs 4).toNat + 32) 8 = st →
      S2.mem.readLE ((s.regs 4).toNat - 368) 8 = xc - kh n →
      ReachesRet (LibMul.program.link impl) ret S2 Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := F.env
  simp only [regSP] at hb' ha hw
  have hW := F.hW; have hW' := kW64_ge n; have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40
  have hn12 := F.n12; have hx48 := F.x48
  have hst : st + 24 ≤ 2 ^ 48 := F.stk.2.1.2.2.2.1
  clear F
  have hk : kh n ≤ n ∧ n - kh n ≤ kh n ∧ 0 < kh n := by simp only [kh]; omega
  have hkh : kh n = (n + 1) / 2 := rfl
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 448) 520 true = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have hs1 : BitVec.ofNat 64 xc - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (xc - kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 n - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (n - kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hl3 := kshl3 (a := kh n) (by omega)
  have hm := kmask (xc - kh n) (8 * kh n) (by omega) (by omega)
  have hm' := kmask' (xc - kh n) (8 * kh n) (by omega) (by omega)
  have ha1 : BitVec.ofNat 64 (8 * kh n) + BitVec.ofNat 64 xp = BitVec.ofNat 64 (xp + 8 * kh n) := by
    rw [bv_add_ofNat (by omega), Nat.add_comm]
  have ha2 : BitVec.ofNat 64 xp + BitVec.ofNat 64 (8 * kh n) = BitVec.ofNat 64 (xp + 8 * kh n) :=
    bv_add_ofNat (by omega)
  have esp : (s.regs 4 - 448#64).toNat = (s.regs 4).toNat - 448 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [hs1, hs2, hl3, hm, hm', ha1, ha2, esp, BitVec.msb_eq_decide] until [kmLX1]
  refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ⟨hQ.pre, hQ.y8, hQ.y16, hQ.y24, ?fr, ?reg, ?fp, ?s2, ?s5⟩ ?n1 ?n2
  case fr => exact hQ.fr.trans (by janus_frame) fun a k h => ⟨h, h⟩
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hQ.reg
  case fp => janus64_simp; exact hQ.fp
  case s2 => janus64_simp; exact hQ.s2
  case s5 => janus64_simp; exact hQ.s5
  all_goals janus64_simp
  all_goals first
    | exact Nat.mod_eq_of_lt (by omega)
    | exact hfs
    | exact hdf
    | exact hx
    | exact h14
    | exact h5
    | exact h2
    | fail "SHOW"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPB2 (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {lx0 lx1 : Nat} (hl0 : lx0 ≤ kh n)
    (hl1 : lx1 ≤ n - kh n)
    (hpc : S.rip = BitVec.ofNat 64 kmLX1x) (hsp : S.regs 4 = s.regs 4 - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 zp)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : S.regs 7 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 lx1)
    (h9 : S.regs 9 = BitVec.ofNat 64 (xp + 8 * kh n)) (h10 : S.regs 10 = BitVec.ofNat 64 n)
    (h11 : S.regs 11 = BitVec.ofNat 64 (n + 1)) (h12 : S.regs 12 = BitVec.ofNat 64 (8 * kh n))
    (h13 : S.regs 13 = BitVec.ofNat 64 xc) (h15 : S.regs 15 = BitVec.ofNat 64 (kh n))
    (h2 : S.regs 2 = BitVec.ofNat 64 lx0) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx : S.xmm 15 = s.xmm 15)
    (q32 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = st) (q368 : S.mem.readLE ((s.regs 4).toNat - 368) 8 = xc - kh n)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.rip = BitVec.ofNat 64 kmLY0 → S2.regs 4 = s.regs 4 - 448#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 3 = BitVec.ofNat 64 zp → S2.regs 1 = BitVec.ofNat 64 yp →
      S2.regs 7 = BitVec.ofNat 64 zc → S2.regs 6 = BitVec.ofNat 64 xp → S2.regs 10 = BitVec.ofNat 64 n →
      S2.regs 11 = BitVec.ofNat 64 (n + 1) → S2.regs 12 = BitVec.ofNat 64 (8 * kh n) →
      S2.regs 15 = BitVec.ofNat 64 (kh n) → S2.regs 2 = BitVec.ofNat 64 (kh n) →
      S2.regs 14 = s.regs 14 → S2.regs 5 = s.regs 4 - 8#64 →
      S2.fsBase = s.fsBase → S2.df = s.df → S2.xmm 15 = s.xmm 15 →
      KQm R b H L W st zp zc xp n xc yp yc s S2.mem → S2.mem.readLE ((s.regs 4).toNat + 32) 8 = st →
      S2.mem.readLE ((s.regs 4).toNat + 48) 8 = 2 * n →
      IntAt S2.mem ((s.regs 4).toNat - 48) 0 xp lx0 xc →
      IntAt S2.mem ((s.regs 4).toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n) →
      ReachesRet (LibMul.program.link impl) ret S2 Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := F.env
  simp only [regSP] at hb' ha hw
  have hW := F.hW; have hW' := kW64_ge n; have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40
  have hn12 := F.n12; have hx48 := F.x48; have hy48 := F.y48
  have hst : st + 24 ≤ 2 ^ 48 := F.stk.2.1.2.2.2.1
  clear F
  have hk : kh n ≤ n ∧ n - kh n ≤ kh n ∧ 0 < kh n := by simp only [kh]; omega
  have hkh : kh n = (n + 1) / 2 := rfl
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 448) 520 true = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have esp : (s.regs 4 - 448#64).toNat = (s.regs 4).toNat - 448 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨y8, -, -⟩ := hQ.yrd
  janus64_run [q368, y8, esp, BitVec.msb_eq_decide] until [kmLY0]
  refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ⟨hQ.pre, hQ.y8, hQ.y16, hQ.y24, ?fr, ?reg, ?fp, ?s2, ?s5⟩ ?n1 ?n2 ?x0h ?x1h
  case fr => exact hQ.fr.trans (by janus_frame) fun a k h => ⟨h, h⟩
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hQ.reg
  case fp => janus64_simp; exact hQ.fp
  case s2 => janus64_simp; exact hQ.s2
  case s5 => janus64_simp; exact hQ.s5
  all_goals (try simp only [IntAt])
  all_goals (try refine ⟨?_, ?_, ?_, ?_⟩)
  all_goals janus64_simp
  all_goals first
    | exact Nat.mod_eq_of_lt (by omega)
    | exact hfs
    | exact hdf
    | exact hx
    | exact h14
    | exact h5
    | fail "SHOW"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPB3 (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {ly0 : Nat} (hl0 : ly0 ≤ kh n)
    (hpc : S.rip = BitVec.ofNat 64 kmLY0x) (hsp : S.regs 4 = s.regs 4 - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 yp)
    (h7 : S.regs 7 = BitVec.ofNat 64 zc) (h10 : S.regs 10 = BitVec.ofNat 64 n)
    (h11 : S.regs 11 = BitVec.ofNat 64 (n + 1)) (h12 : S.regs 12 = BitVec.ofNat 64 (8 * kh n))
    (h15 : S.regs 15 = BitVec.ofNat 64 ly0) (h2 : S.regs 2 = BitVec.ofNat 64 (kh n))
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx : S.xmm 15 = s.xmm 15)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.rip = BitVec.ofNat 64 kmLY1 → S2.regs 4 = s.regs 4 - 448#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 3 = BitVec.ofNat 64 zp → S2.regs 1 = BitVec.ofNat 64 yp →
      S2.regs 7 = BitVec.ofNat 64 zc → S2.regs 6 = BitVec.ofNat 64 (yp + 8 * kh n) →
      S2.regs 8 = BitVec.ofNat 64 yc → S2.regs 9 = BitVec.ofNat 64 (yc - kh n) →
      S2.regs 10 = BitVec.ofNat 64 (n - kh n) →
      S2.regs 11 = BitVec.ofNat 64 (n + 1) → S2.regs 12 = BitVec.ofNat 64 (8 * kh n) →
      S2.regs 15 = BitVec.ofNat 64 ly0 → S2.regs 2 = BitVec.ofNat 64 (kh n) →
      S2.regs 14 = s.regs 14 → S2.regs 5 = s.regs 4 - 8#64 →
      S2.fsBase = s.fsBase → S2.df = s.df → S2.xmm 15 = s.xmm 15 → S2.mem = S.mem →
      ReachesRet (LibMul.program.link impl) ret S2 Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  have hW := F.hW; have hW' := kW64_ge n; have h40 := F.n40; have hyc := F.ycn; have hyc40 := F.yc40
  have hn12 := F.n12; have hy48 := F.y48
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := F.env
  simp only [regSP] at hb' ha hw
  clear F
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 448) 520 true = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have hk : kh n ≤ n ∧ n - kh n ≤ kh n ∧ 0 < kh n := by simp only [kh]; omega
  have hkh : kh n = (n + 1) / 2 := rfl
  have hs1 : BitVec.ofNat 64 yc - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (yc - kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 n - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (n - kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hm := kmask (yc - kh n) (8 * kh n) (by omega) (by omega)
  have hm' := kmask' (yc - kh n) (8 * kh n) (by omega) (by omega)
  have ha1 : BitVec.ofNat 64 (8 * kh n) + BitVec.ofNat 64 yp = BitVec.ofNat 64 (yp + 8 * kh n) := by
    rw [bv_add_ofNat (by omega), Nat.add_comm]
  have ha2 : BitVec.ofNat 64 yp + BitVec.ofNat 64 (8 * kh n) = BitVec.ofNat 64 (yp + 8 * kh n) :=
    bv_add_ofNat (by omega)
  have esp : (s.regs 4 - 448#64).toNat = (s.regs 4).toNat - 448 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨-, -, y24⟩ := hQ.yrd
  janus64_run [hs1, hs2, hm, hm', ha1, ha2, y24, esp, BitVec.msb_eq_decide] until [kmLY1]
  refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus64_simp
  all_goals first
    | exact Nat.mod_eq_of_lt (by omega)
    | exact hfs
    | exact hdf
    | exact hx
    | exact h14
    | exact h5
    | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
