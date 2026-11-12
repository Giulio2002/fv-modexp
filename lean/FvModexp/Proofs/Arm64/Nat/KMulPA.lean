import FvModexp.Proofs.Arm64.Nat.KMulPD

set_option autoImplicit false

/-!
# `karatsuba` (arm64): entry → the first inlined `norm` loop (natmul.go:164-197)

`kmPA`: entry (`0x1bbe70`) → the `x[:n2].norm()` loop head (`0x1bbf14`): stack-guard check (refuted morestack),
frame (`SP' = SP - 448`, `X29`/`X30` at `SP - 456`/`SP - 448`), spills `SP + 16 := zp`, `SP + 40 := xp`,
`SP + 64 := yp`, the defer pointer `SP - 16 := 0` and bit `:= 0`, `len x = n`, `len z = 2n` (panics refuted),
`n ≥ karatsubaThreshold = 40` (the `basicMul` fallback refuted), `R10 = n + 1`, `R11 = R12 = n2`.
(Structure adapted from this repo's `KSqrPA.kPA`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPA (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} (hpre : KPre R b L W st zp (2 * n) zc xp n xc yp n yc s) (hpc : s.pc = BitVec.ofNat 64 0x1bbe70)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h1 : s.regs 1 = BitVec.ofNat 64 zp)
    (h2 : s.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : s.regs 3 = BitVec.ofNat 64 zc)
    (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 n) (h6 : s.regs 6 = BitVec.ofNat 64 xc)
    (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 n) (h9 : s.regs 9 = BitVec.ofNat 64 yc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S1 : State, S1.pc = BitVec.ofNat 64 0x1bbf14 → S1.sp = s.sp - 448#64 →
      S1.regs 0 = BitVec.ofNat 64 st → S1.regs 1 = BitVec.ofNat 64 zp → S1.regs 2 = BitVec.ofNat 64 (2 * n) →
      S1.regs 3 = BitVec.ofNat 64 zc → S1.regs 4 = BitVec.ofNat 64 xp → S1.regs 5 = BitVec.ofNat 64 n →
      S1.regs 6 = BitVec.ofNat 64 xc → S1.regs 7 = BitVec.ofNat 64 yp → S1.regs 8 = BitVec.ofNat 64 n →
      S1.regs 9 = BitVec.ofNat 64 yc → S1.regs 10 = BitVec.ofNat 64 (n + 1) →
      S1.regs 11 = BitVec.ofNat 64 (kh n) → S1.regs 12 = BitVec.ofNat 64 (kh n) → S1.regs 28 = s.regs 28 →
      S1.regs 29 = s.sp - 456#64 → S1.regs 18 = s.regs 18 → KQm R b L W st zp zc xp n xc yp yc s S1.mem →
      ReachesRet (LibMul.program.link impl) ret S1 Q) :
    ReachesRet (LibMul.program.link impl) ret s Q := by
  have F := hpre.F
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := F.env
  obtain ⟨h40v, -, -, -, e40, -, -, hgacc, -, hgw, -⟩ := F.gl
  have hW := F.hW
  have hW' := kW_ge n
  have h40 := F.n40
  have hn12 := F.n12
  have eg : RunIface.gA = 7147136 := rfl
  rw [eg] at e40 hgacc hgw
  rw [e40] at h40v
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  have hthA : s.mem.accessible 7147144 8 false = true := Memory.accessible_mono _ hgacc (by omega) (by omega)
  have hsacc : s.mem.accessible (s.sp.toNat - 456) 528 true = true :=
    Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : s.mem.accessible (s.sp.toNat - 456) 528 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (F.zlive (by have := F.zc2; omega)).2.2.2
  have hx48 := F.x48
  have hy48 := F.y48
  clear hw F
  have hsh : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsh2 : (BitVec.ofNat 64 (n + 1)).rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 =
      BitVec.ofNat 64 (kh n) := by
    rw [km_lsr1]; exact kh_lsr n (by omega)
  have hshl : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have t40 := toInt_small (BitVec.ofNat 64 40) (by decide)
  have t2 := toInt_small (BitVec.ofNat 64 2) (by decide)
  have tn := toInt_small (BitVec.ofNat 64 n) (by simp only [BitVec.toNat_ofNat]; omega)
  janus_run [h40v, hsh, hsh2, hshl, t40, t2, tn] until [0x1bbf14]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨hpre, ?fr, ?reg, ?_, ?_, ?_, ?_, ?_⟩
  case fr => janus_frame
  case reg => simp only [Memory.regions_writeLE]
  all_goals janus_simp
  all_goals exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Arm64.NatMul
