import FvModexp.Proofs.Arm64.NatQ.KSqrPQ

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/KSqrPA.lean — TIGHT COSTS, divmc s34] `karatsubaSqr` (arm64): the prologue up to the first inlined `norm` loop (natmul.go:257-283)

`KQ … s M` (KSqrPQ): the facts of the prologue's memory `M` (frame record, the spill `SP + 40 := xp`, only our frame written).
`kPA`: entry (`0x1bc2b0`) → loop 1 head (`kL1 = 0x1bc324`): stack-guard check (refuted morestack), frame (`SP' = SP - 320`,
`X29`/`X30` at `SP - 328`/`SP - 320`), spills `SP + 16 := zp`, `SP + 40 := xp`, `SP - 16 := 0`, defer bit `:= 0`,
`len z = 2n` (panic refuted), `n ≥ karatsubaSqrThreshold = 80` (the `basicSqr` fallback refuted), `R7 = n + 1`,
`R8 = R9 = n2`.
-/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kPA (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} (hpre : KPre R b H L W st zp (2 * n) zc xp n xc s) (hpc : s.pc = BitVec.ofNat 64 0x1bc2b0)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h1 : s.regs 1 = BitVec.ofNat 64 zp)
    (h2 : s.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : s.regs 3 = BitVec.ofNat 64 zc)
    (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 n) (h6 : s.regs 6 = BitVec.ofNat 64 xc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S1 : State, S1.pc = BitVec.ofNat 64 kL1 → S1.sp = s.sp - 320#64 →
      S1.regs 0 = BitVec.ofNat 64 st → S1.regs 1 = BitVec.ofNat 64 zp → S1.regs 2 = BitVec.ofNat 64 (2 * n) →
      S1.regs 3 = BitVec.ofNat 64 zc → S1.regs 4 = BitVec.ofNat 64 xp → S1.regs 5 = BitVec.ofNat 64 n →
      S1.regs 6 = BitVec.ofNat 64 xc → S1.regs 7 = BitVec.ofNat 64 (n + 1) →
      S1.regs 8 = BitVec.ofNat 64 (kn2 n) → S1.regs 9 = BitVec.ofNat 64 (kn2 n) → S1.regs 28 = s.regs 28 →
      S1.regs 29 = s.sp - 328#64 → S1.regs 18 = s.regs 18 → KQ R b H L W st zp zc xp n xc s S1.mem →
      ReachesRet (LibSqr.program.link impl) ret S1 Q) :
    ReachesRet (LibSqr.program.link impl) ret s Q := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, hW, -, hglb, -, h80, hxc, hxc40, hn12, -,
    -, hxp48, -, -, hzc, hzc40, -⟩ := hpre'
  obtain ⟨-, -, h80v, -, -, -, e80, hgacc, -, hgw, -⟩ := hglb
  have eg : RunIface.gA = 7147136 := rfl
  rw [eg] at e80 hgacc hgw
  rw [e80] at h80v
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  unfold ksqrW at hW
  have hthA : s.mem.accessible 7147160 8 false = true := Memory.accessible_mono _ hgacc (by omega) (by omega)
  have hsacc : s.mem.accessible (s.sp.toNat - 328) 376 true = true :=
    Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : s.mem.accessible (s.sp.toNat - 328) 376 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear hw hLs
  have hsh : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsh2 : (BitVec.ofNat 64 (n + 1)).rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 =
      BitVec.ofNat 64 (kn2 n) := by
    rw [klsr1]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega
  have hshl : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have t80 := toInt_small (BitVec.ofNat 64 80) (by decide)
  have tn := toInt_small (BitVec.ofNat 64 n) (by simp only [BitVec.toNat_ofNat]; omega)
  janus_run [h80v, hsh, hsh2, hshl, t80, tn] until [kL1]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨hpre, ?fr, ?reg, ?_, ?_, ?_⟩
  case fr => janus_frame
  case reg => simp only [Memory.regions_writeLE]
  all_goals janus_simp
  all_goals exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Arm64.Q.NatSqr
