import FvModexp.Proofs.Amd64.NatQ.KMulPD
import FvModexp.Proofs.Amd64.NatQ.KMulLoop

set_option autoImplicit false

/-!
# [amd64 port (divmc s51) of the Q-form Arm64/NatQ/KMulPA.lean — TIGHT COSTS] `karatsuba` (amd64): entry → the first inlined `norm` loop (natmul.go:164-197)

`kmPA`: entry (`0x5f1da0`) → the `x[:n2].norm()` loop head (`0x5f1e51`): stack-guard check (refuted morestack),
frame (`PUSHQ BP`, `RSP' = RSP - 448`), spills `RSP + 40 := zp`, `RSP + 64 := xp`, the defer pointer `RSP - 16 := 0`
and bit `RSP - 369 := 0`, `len x = n`, `len z = 2n` (panics refuted), `n ≥ karatsubaThreshold = 40` (the `basicMul`
fallback refuted), `R10 = n`, `R11 = n + 1`, `R12 = DX = n2`. (Mechanics as Amd64/NatQ/KSqrPA.kPA.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPA (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} (hpre : KPre R b H L W st zp (2 * n) zc xp n xc yp n yc s) (hpc : s.rip = BitVec.ofNat 64 0x5f1da0)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h3 : s.regs 3 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : s.regs 7 = BitVec.ofNat 64 zc)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 n) (h9 : s.regs 9 = BitVec.ofNat 64 xc)
    (y8 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp) (y16 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n)
    (y24 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ S1 : State, S1.rip = BitVec.ofNat 64 kmLX0 → S1.regs 4 = s.regs 4 - 448#64 →
      S1.regs 0 = BitVec.ofNat 64 st → S1.regs 3 = BitVec.ofNat 64 zp → S1.regs 1 = BitVec.ofNat 64 (2 * n) →
      S1.regs 7 = BitVec.ofNat 64 zc → S1.regs 6 = BitVec.ofNat 64 xp → S1.regs 8 = BitVec.ofNat 64 n →
      S1.regs 9 = BitVec.ofNat 64 xc → S1.regs 10 = BitVec.ofNat 64 n →
      S1.regs 11 = BitVec.ofNat 64 (n + 1) → S1.regs 12 = BitVec.ofNat 64 (kh n) → S1.regs 2 = BitVec.ofNat 64 (kh n) →
      S1.regs 14 = s.regs 14 → S1.regs 5 = s.regs 4 - 8#64 → S1.fsBase = s.fsBase → S1.df = s.df →
      S1.xmm 15 = s.xmm 15 → KQm R b H L W st zp zc xp n xc yp yc s S1.mem →
      ReachesRet (LibMul.program.link impl) ret S1 Q) :
    ReachesRet (LibMul.program.link impl) ret s Q := by
  have F := hpre.F
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -⟩ := F.env
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨h40v, -, -, -, e40, -, -, hgacc, -, hgw, -⟩ := F.gl
  have hW := F.hW
  have hW' := kW64_ge n
  have h40 := F.n40
  have hn12 := F.n12
  have eg : RunIface.gA = 11841160 := rfl
  rw [eg] at e40 hgacc hgw
  rw [e40] at h40v
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  have hthA : s.mem.accessible 11841168 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)
  have hsacc : s.mem.accessible ((s.regs 4).toNat - 448) 520 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (F.zlive (by have := F.zc2; omega)).2.2.2
  have hx48 := F.x48
  clear hw F
  have hsh : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsh2 : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kh n) := NatSqr.kshr1 (n := n) (by omega)
  have hdbl : BitVec.ofNat 64 n + BitVec.ofNat 64 n = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t40 := toInt_small (BitVec.ofNat 64 40) (by decide)
  have t2 := toInt_small (BitVec.ofNat 64 2) (by decide)
  have tn := toInt_small (BitVec.ofNat 64 n) (by simp only [BitVec.toNat_ofNat]; omega)
  janus64_run [h40v, y16, hsh, hsh2, hdbl, t40, t2, tn, BitVec.msb_eq_decide] until [kmLX0]
  refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨hpre, y8, y16, y24, ?fr, ?reg, ?_, ?_, ?_⟩
  case fr => janus_frame
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals janus64_simp
  all_goals first | exact Nat.mod_eq_of_lt (by omega) | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
