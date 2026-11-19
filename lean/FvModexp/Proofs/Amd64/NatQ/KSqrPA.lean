import FvModexp.Proofs.Amd64.NatQ.KSqrPQ

set_option autoImplicit false

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/KSqrPA.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the prologue up to
the first inlined `norm` loop (natmul.go:257-285)

`kPA`: entry (`0x5f2380`) → loop 1 head (`kL1 = 0x5f23f8`): stack-guard check (`LEAQ -0xb8(SP), R12; CMPQ R12, 16(R14)`,
morestack refuted), `PUSHQ BP; MOVQ SP, BP; SUBQ $0x130, SP` (`SP' = RSP - 312`, saved `RBP` at `RSP - 8`), spills
`RSP + 16 := zp`, `RSP + 40 := xp`, `RSP - 16 := X15`, defer bit `RSP - 249 := 0`, `len z = 2n` (panic refuted),
`karatsubaSqrThreshold = 80 ≤ n` and `2 ≤ n` (the `basicSqr` fallback refuted), `R10 = n + 1`, `DX = R11 = n2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kPA (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} (hpre : KPre R b H L W st zp (2 * n) zc xp n xc s) (hpc : s.rip = BitVec.ofNat 64 0x5f2380)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h3 : s.regs 3 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : s.regs 7 = BitVec.ofNat 64 zc)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 n) (h9 : s.regs 9 = BitVec.ofNat 64 xc)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ S1 : State, S1.rip = BitVec.ofNat 64 kL1 → S1.regs 4 = s.regs 4 - 312#64 →
      S1.regs 0 = BitVec.ofNat 64 st → S1.regs 3 = BitVec.ofNat 64 zp → S1.regs 1 = BitVec.ofNat 64 (2 * n) →
      S1.regs 7 = BitVec.ofNat 64 zc → S1.regs 6 = BitVec.ofNat 64 xp → S1.regs 8 = BitVec.ofNat 64 n →
      S1.regs 9 = BitVec.ofNat 64 xc → S1.regs 10 = BitVec.ofNat 64 (n + 1) →
      S1.regs 11 = BitVec.ofNat 64 (kn2 n) → S1.regs 2 = BitVec.ofNat 64 (kn2 n) → S1.regs 14 = s.regs 14 →
      S1.regs 5 = s.regs 4 - 8#64 → S1.fsBase = s.fsBase → S1.df = s.df → S1.xmm 15 = s.xmm 15 →
      KQ R b H L W st zp zc xp n xc s S1.mem →
      ReachesRet (LibSqr.program.link impl) ret S1 Q) :
    ReachesRet (LibSqr.program.link impl) ret s Q := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩, hW, -, hglb, -, h80, hxc, hxc40, hn12,
    -, -, hxp48, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨-, -, h80v, -, -, -, e80, hgacc, -, hgw, -⟩ := hglb
  have eg : RunIface.gA = 11841160 := rfl
  rw [eg] at e80 hgacc hgw
  rw [e80] at h80v
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  unfold ksqrW at hW
  have hthA : s.mem.accessible 11841184 8 false = true := Janus.Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)
  have hsacc : s.mem.accessible ((s.regs 4).toNat - 320) 368 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have hsh : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsh2 := kshr1 (n := n) (by omega)
  have hdbl : BitVec.ofNat 64 n + BitVec.ofNat 64 n = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t80 := toInt_small (BitVec.ofNat 64 80) (by decide)
  have tn := toInt_small (BitVec.ofNat 64 n) (by simp only [BitVec.toNat_ofNat]; omega)
  janus64_run [h80v, hsh, hsh2, hdbl, t80, tn, BitVec.msb_eq_decide] until [kL1]
  refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨hpre, ?fr, ?reg, ?_, ?_⟩
  case fr => janus_frame
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals janus64_simp
  all_goals first | exact Nat.mod_eq_of_lt (by omega) | fail "SHOW"

end FvModexp.Amd64.Q.NatSqr
