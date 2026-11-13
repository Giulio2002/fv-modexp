import FvModexp.Proofs.Amd64.NatQ.KSqrPQ

set_option autoImplicit false

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/KSqrPB.lean — TIGHT COSTS] `karatsubaSqr` (amd64): loop 1 exit →
loop 2 head (natmul.go:286)

`kPB`: `0x5f2407` (`DX = len x0`) → `kL2 = 0x5f2440`: the `x[:n2]` bound (`len x0 ≤ cap x`, panic refuted), `R12 = xc`,
`R13 = n2`, `R11 = 8·n2` (stored at `0x48(SP') = RSP - 240`), `R15 = xc - n2`, `R9 = xp + 8·n2` (the `NEGQ/SARQ/ANDQ`
mask is all ones since `n2 < xc`), `R8 = n - n2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kPB (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {S : State} (hQ : KQ R b H L W st zp zc xp n xc s S.mem) {lx0 : Nat} (hl0 : lx0 ≤ kn2 n)
    (hpc : S.rip = BitVec.ofNat 64 kL1x) (hsp : S.regs 4 = s.regs 4 - 312#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 zp)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : S.regs 7 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h10 : S.regs 10 = BitVec.ofNat 64 (n + 1)) (h11 : S.regs 11 = BitVec.ofNat 64 (kn2 n))
    (h2 : S.regs 2 = BitVec.ofNat 64 lx0) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx : S.xmm 15 = s.xmm 15)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.rip = BitVec.ofNat 64 kL2 → S2.regs 4 = s.regs 4 - 312#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 3 = BitVec.ofNat 64 zp → S2.regs 1 = BitVec.ofNat 64 (2 * n) →
      S2.regs 7 = BitVec.ofNat 64 zc → S2.regs 6 = BitVec.ofNat 64 xp → S2.regs 8 = BitVec.ofNat 64 (n - kn2 n) →
      S2.regs 9 = BitVec.ofNat 64 (xp + 8 * kn2 n) → S2.regs 10 = BitVec.ofNat 64 (n + 1) →
      S2.regs 11 = BitVec.ofNat 64 (8 * kn2 n) → S2.regs 12 = BitVec.ofNat 64 xc →
      S2.regs 13 = BitVec.ofNat 64 (kn2 n) → S2.regs 15 = BitVec.ofNat 64 (xc - kn2 n) →
      S2.regs 2 = BitVec.ofNat 64 lx0 → S2.regs 14 = s.regs 14 → S2.regs 5 = s.regs 4 - 8#64 →
      S2.fsBase = s.fsBase → S2.df = s.df → S2.xmm 15 = s.xmm 15 →
      KQ R b H L W st zp zc xp n xc s S2.mem → S2.mem.readLE ((s.regs 4).toNat - 240) 8 = 8 * kn2 n →
      ReachesRet (LibSqr.program.link impl) ret S2 Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, hal, -⟩, hW, -, -, -, h80, hxc, hxc40, hn12, -, -, hxp48, -⟩ := hQ.pre
  simp only [regSP] at hb' ha hw
  unfold ksqrW at hW
  have hk : kn2 n ≤ n ∧ n - kn2 n ≤ kn2 n ∧ 0 < kn2 n := by simp only [kn2]; omega
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have hs1 : BitVec.ofNat 64 xc - BitVec.ofNat 64 (kn2 n) = BitVec.ofNat 64 (xc - kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 n - BitVec.ofNat 64 (kn2 n) = BitVec.ofNat 64 (n - kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hl3 := kshl3 (a := kn2 n) (by omega)
  have hm := kmask (xc - kn2 n) (8 * kn2 n) (by simp only [kn2]; omega) (by omega)
  have hm' := kmask' (xc - kn2 n) (8 * kn2 n) (by simp only [kn2]; omega) (by omega)
  have ha1 : BitVec.ofNat 64 (8 * kn2 n) + BitVec.ofNat 64 xp = BitVec.ofNat 64 (xp + 8 * kn2 n) := by
    rw [bv_add_ofNat (by omega), Nat.add_comm]
  have ha2 : BitVec.ofNat 64 xp + BitVec.ofNat 64 (8 * kn2 n) = BitVec.ofNat 64 (xp + 8 * kn2 n) :=
    bv_add_ofNat (by omega)
  have esp : (s.regs 4 - 312#64).toNat = (s.regs 4).toNat - 312 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [hs1, hs2, hl3, hm, hm', ha1, ha2, esp, BitVec.msb_eq_decide] until [kL2]
  refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ⟨hQ.pre, ?fr, ?reg, ?fp, ?s5⟩ ?n1
  case fr => exact hQ.fr.trans (by janus_frame) fun a k h => ⟨h, h⟩
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hQ.reg
  case fp => janus64_simp; exact hQ.fp
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

end FvModexp.Amd64.Q.NatSqr
