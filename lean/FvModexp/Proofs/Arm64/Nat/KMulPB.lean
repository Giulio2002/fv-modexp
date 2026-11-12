import FvModexp.Proofs.Arm64.Nat.KMulPD

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the prologue between the inlined `norm` loops (natmul.go:197-198)

* `kmPB1`: `x0` loop exit (`0x1bbf28`, `R11 = len x0`; the `x[:i]` bound check refuted) → `x1` loop head
  (`0x1bbf4c`: `R5 = n - n2`, base `R14 = xp + 8·n2`, `R13 = xc - n2`);
* `kmPB2`: `x1` loop exit (`0x1bbf60`, `R5 = len x1`) → `y0` loop head (`0x1bbf94`): the `x0`/`x1` headers
  (`SP-48`, `SP-80`) stored, `R4 = R12 = n2`;
* `kmPB3`: `y0` loop exit (`0x1bbfa8`, `R12 = len y0`) → `y1` loop head (`0x1bbfcc`: `R8 = n - n2`, base
  `R6 = yp + 8·n2`, `R5 = yc - n2`).
(Adapted from this repo's `KSqrPA.kPB`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (IntAt)

/-- the mask of `-(c - n2)` (`SUB` not yet folded) -/
theorem km_mask' (k c : Nat) (h1 : k < c) (h2 : c < 2 ^ 40) :
    (BitVec.ofNat 64 k &&& (0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 k)).sshiftRight 63) =
      BitVec.ofNat 64 k := by
  rw [km_sub (by omega) (by omega)]; exact km_mask k c h1 h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPB1 (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b L W st zp zc xp n xc yp yc s S.mem) {lx0 : Nat} (hl0 : lx0 ≤ kh n)
    (hpc : S.pc = BitVec.ofNat 64 0x1bbf28) (hsp : S.sp = s.sp - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st)
    (h1 : S.regs 1 = BitVec.ofNat 64 zp)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n))
    (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp)
    (h5 : S.regs 5 = BitVec.ofNat 64 n)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 yp)
    (h8 : S.regs 8 = BitVec.ofNat 64 n)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (h10 : S.regs 10 = BitVec.ofNat 64 (n + 1))
    (h11 : S.regs 11 = BitVec.ofNat 64 lx0)
    (h12 : S.regs 12 = BitVec.ofNat 64 (kh n))
    (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 456#64)
    (h18 : S.regs 18 = s.regs 18)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.pc = BitVec.ofNat 64 0x1bbf4c → S2.sp = s.sp - 448#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 1 = BitVec.ofNat 64 zp → S2.regs 2 = BitVec.ofNat 64 (2 * n) → S2.regs 3 = BitVec.ofNat 64 zc → S2.regs 4 = BitVec.ofNat 64 xp → S2.regs 5 = BitVec.ofNat 64 (n - kh n) → S2.regs 6 = BitVec.ofNat 64 xc → S2.regs 7 = BitVec.ofNat 64 yp → S2.regs 8 = BitVec.ofNat 64 n → S2.regs 9 = BitVec.ofNat 64 yc → S2.regs 10 = BitVec.ofNat 64 (n + 1) → S2.regs 11 = BitVec.ofNat 64 lx0 → S2.regs 12 = BitVec.ofNat 64 (kh n) → S2.regs 13 = BitVec.ofNat 64 (xc - kh n) → S2.regs 14 = BitVec.ofNat 64 (xp + 8 * kh n) → S2.regs 28 = s.regs 28 → S2.regs 29 = s.sp - 456#64 → S2.regs 18 = s.regs 18 →
      S2.mem = S.mem → ReachesRet (LibMul.program.link impl) ret S2 Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40; have hyc := F.ycn; have hyc40 := F.yc40
  have hn12 := F.n12
  clear F
  have hk := kh_facts h40
  have hsh2 := kh_lsr n (by omega)
  have hs1 : BitVec.ofNat 64 xc - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (xc - kh n) := km_sub (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 n - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (n - kh n) := km_sub (by omega) (by omega)
  have hm := km_mask' (kh n) xc (by omega) hxc40
  janus_run [hsh2, hm] until [0x1bbf4c]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus_simp
  all_goals first
    | exact hs1
    | exact hs2
    | (rw [← BitVec.ofNat_add, show xp + kh n * 8 = xp + 8 * kh n by omega])
    | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPB2 (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b L W st zp zc xp n xc yp yc s S.mem) {lx0 lx1 : Nat} (hl0 : lx0 ≤ kh n) (hl1 : lx1 ≤ n - kh n)
    (hpc : S.pc = BitVec.ofNat 64 0x1bbf60) (hsp : S.sp = s.sp - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st)
    (h1 : S.regs 1 = BitVec.ofNat 64 zp)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n))
    (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp)
    (h5 : S.regs 5 = BitVec.ofNat 64 lx1)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 yp)
    (h8 : S.regs 8 = BitVec.ofNat 64 n)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (h10 : S.regs 10 = BitVec.ofNat 64 (n + 1))
    (h11 : S.regs 11 = BitVec.ofNat 64 lx0)
    (h12 : S.regs 12 = BitVec.ofNat 64 (kh n))
    (h13 : S.regs 13 = BitVec.ofNat 64 (xc - kh n))
    (h14 : S.regs 14 = BitVec.ofNat 64 (xp + 8 * kh n))
    (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 456#64)
    (h18 : S.regs 18 = s.regs 18)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.pc = BitVec.ofNat 64 0x1bbf94 → S2.sp = s.sp - 448#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 1 = BitVec.ofNat 64 zp → S2.regs 2 = BitVec.ofNat 64 (2 * n) → S2.regs 3 = BitVec.ofNat 64 zc → S2.regs 4 = BitVec.ofNat 64 (kh n) → S2.regs 7 = BitVec.ofNat 64 yp → S2.regs 8 = BitVec.ofNat 64 n → S2.regs 9 = BitVec.ofNat 64 yc → S2.regs 10 = BitVec.ofNat 64 (n + 1) → S2.regs 12 = BitVec.ofNat 64 (kh n) → S2.regs 28 = s.regs 28 → S2.regs 29 = s.sp - 456#64 → S2.regs 18 = s.regs 18 →
      KQm R b L W st zp zc xp n xc yp yc s S2.mem → IntAt S2.mem (s.sp.toNat - 48) 0 xp lx0 xc →
      IntAt S2.mem (s.sp.toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n) → ReachesRet (LibMul.program.link impl) ret S2 Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40; have hyc := F.ycn; have hyc40 := F.yc40
  have hn12 := F.n12
  clear F
  have hk := kh_facts h40
  have hsh2 := kh_lsr n (by omega)
  have hpre := hQ.pre
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -⟩, hW, -⟩ := hpre
  have hW' := kW_ge n
  have hsacc : S.mem.accessible (s.sp.toNat - 456) 528 true = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : S.mem.accessible (s.sp.toNat - 456) 528 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear hw
  have hx8 : xp + 8 * kh n < 2 ^ 64 := by
    have := hQ.pre.F.x48; omega
  janus_run until [0x1bbf94]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨hQ.pre, ?fr, ?reg, ?lr, ?fp, ?s2, ?s5, ?s6⟩ ?_ ?_
  case fr => exact hQ.fr.trans (by janus_frame) fun a k h => ⟨h, h⟩
  case reg => simp only [Memory.regions_writeLE]; exact hQ.reg
  case lr => janus_simp; exact hQ.lr
  case fp => janus_simp; exact hQ.fp
  case s2 => janus_simp; exact hQ.s2
  case s5 => janus_simp; exact hQ.s5
  case s6 => janus_simp; exact hQ.s6
  all_goals (try simp only [IntAt])
  all_goals janus_simp
  all_goals first | exact Nat.mod_eq_of_lt (by omega) | skip
  all_goals (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPB3 (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b L W st zp zc xp n xc yp yc s S.mem) {ly0 : Nat} (hm0 : ly0 ≤ kh n)
    (hpc : S.pc = BitVec.ofNat 64 0x1bbfa8) (hsp : S.sp = s.sp - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st)
    (h1 : S.regs 1 = BitVec.ofNat 64 zp)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n))
    (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 (kh n))
    (h7 : S.regs 7 = BitVec.ofNat 64 yp)
    (h8 : S.regs 8 = BitVec.ofNat 64 n)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (h10 : S.regs 10 = BitVec.ofNat 64 (n + 1))
    (h12 : S.regs 12 = BitVec.ofNat 64 ly0)
    (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 456#64)
    (h18 : S.regs 18 = s.regs 18)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.pc = BitVec.ofNat 64 0x1bbfcc → S2.sp = s.sp - 448#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 1 = BitVec.ofNat 64 zp → S2.regs 2 = BitVec.ofNat 64 (2 * n) → S2.regs 3 = BitVec.ofNat 64 zc → S2.regs 4 = BitVec.ofNat 64 (kh n) → S2.regs 5 = BitVec.ofNat 64 (yc - kh n) → S2.regs 6 = BitVec.ofNat 64 (yp + 8 * kh n) → S2.regs 7 = BitVec.ofNat 64 yp → S2.regs 8 = BitVec.ofNat 64 (n - kh n) → S2.regs 9 = BitVec.ofNat 64 yc → S2.regs 10 = BitVec.ofNat 64 (n + 1) → S2.regs 12 = BitVec.ofNat 64 ly0 → S2.regs 28 = s.regs 28 → S2.regs 29 = s.sp - 456#64 → S2.regs 18 = s.regs 18 →
      S2.mem = S.mem → ReachesRet (LibMul.program.link impl) ret S2 Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  have h40 := F.n40; have hxc := F.xcn; have hxc40 := F.xc40; have hyc := F.ycn; have hyc40 := F.yc40
  have hn12 := F.n12
  clear F
  have hk := kh_facts h40
  have hsh2 := kh_lsr n (by omega)
  have hs1 : BitVec.ofNat 64 yc - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (yc - kh n) := km_sub (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 n - BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (n - kh n) := km_sub (by omega) (by omega)
  have hm := km_mask' (kh n) yc (by omega) hyc40
  janus_run [hsh2, hm] until [0x1bbfcc]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus_simp
  all_goals first
    | exact hs1
    | exact hs2
    | (rw [← BitVec.ofNat_add, show yp + kh n * 8 = yp + 8 * kh n by omega])
    | skip

end FvModexp.Arm64.NatMul
