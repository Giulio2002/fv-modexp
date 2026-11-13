import FvModexp.Proofs.Arm64.NatQ.KSqrEndP
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# [Q-form copy of Arm64/Nat/KSqrEnd.lean — TIGHT COSTS, divmc s34] `karatsubaSqr` (arm64): the end (natmul.go:304, :332), `KB7 → RET`

`kEnd`: from `KB7` (`0x1bc514`) through the `z[n2:]` bounds check (panic refuted), `addTo(z[n2:], z1.abs)` (`AddTo.ens`
moved to `LibSqr`, pre `kAddPre`, `KM.addStep`, value `ks_val`), the defer-bit store, the deferred closure
`karatsubaSqr.deferwrap1` (`kdsum`, pre `kRestPre`), `LDP`/`ADD`/`RET` → `KPost` (`kEndFin`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

def fnKD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr.deferwrap1"

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore` closure of `karatsubaSqr` as a callee of `LibSqr` (as `BasicSqr.dsum`) -/
theorem kdsum (impl : List Segment) :
    Summary (LibSqr.program.link impl) (segAddr LibSqr.program fnKD) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnKD, reduceSegAddr] at hpc
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

theorem kdsum_entry : segAddr LibSqr.program fnKD = 0x1bc5e0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kEnd (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} (S : State)
    (hB : KB7 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk l) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  have hl := hB.hl
  have hsp' : (s.sp - 320#64).toNat = s.sp.toNat - 320 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨-, e1, e2, e3⟩ := hB.z1h
  rw [show s.sp.toNat - 200 + 8 = s.sp.toNat - 192 by omega] at e1
  rw [show s.sp.toNat - 200 + 16 = s.sp.toNat - 184 by omega] at e2
  rw [show s.sp.toNat - 200 + 24 = s.sp.toNat - 176 by omega] at e3
  have f3 := hkm.s3; have f1 := hkm.n1s; have f4 := hkm.s4; have f2 := hkm.n2s; have f5 := hkm.s2
  have hwA : S.mem.accessible (s.sp.toNat - W) (W + 48) true = true := by
    rw [hkm.fr.accessible]; exact hkm.pre.1.2.1.2.2.2
  have hsh : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kn2 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega
  have hmask : (BitVec.ofNat 64 (kn2 n) &&& (0#64 - (BitVec.ofNat 64 zc - BitVec.ofNat 64 (kn2 n))).sshiftRight 63) =
      BitVec.ofNat 64 (kn2 n) := by
    rw [BitVec.and_comm]
    have hd : (BitVec.ofNat 64 zc - BitVec.ofNat 64 (kn2 n)).toNat = zc - kn2 n := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    exact neg_sshr63_and _ _ (by rw [hd]; omega) (by rw [hd]; omega)
  have hsub : ∀ a c : Nat, c ≤ a → a < 2 ^ 64 → BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
    intro a c h1 h2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hD := kdsum impl
  rw [kdsum_entry] at hD
  unfold KGoal
  janus_run [hsh, hmask, f1, f2, f3, f4, f5, e1, e2, e3] until [addToA]
  refine ks_addcall impl hap R hmv hB _ rfl ?sp ?g ?m ?ra ?r0 (hsub _ _ (by omega) (by omega))
    (hsub _ _ (by omega) (by omega)) ?r3 ?r4 ?r5 ?cont
  case cont =>
    intro s2 hpc2 hreg2 hk Lk' bk' hkmA hz
    obtain ⟨k1, k2, k3, k4⟩ := hk
    simp only at k1 k2 k3 k4
    have hp1 := hkmA.dpt
    have hp2 : s2.mem.readLE (s.sp.toNat - 168) 8 = 0x1bc5e0 := hkmA.dfn
    have hwB : s2.mem.accessible (s.sp.toNat - W) (W + 48) true = true := by
      rw [hkmA.fr.accessible]; exact hkmA.pre.1.2.1.2.2.2
    clear hwA f1 f2 f3 f4 f5 e1 e2 e3
    janus_run [hp1, hp2] until [0x1bc5e0]
    refine ks_restcall impl hD hkmA hz _ rfl ?sp2 ?g2 ?h26 ?h30 ?hF2 ?cont2
    case cont2 =>
      intro s3 q1 q2 q3 q4 hfp hlr hacc3 hpost
      simp only at q2 q3 q4
      have hwC : s3.mem.accessible (s.sp.toNat - W) (W + 48) true = true := by rw [hacc3]; exact hwB
      clear hp1 hp2 hwB
      janus_run [hfp, hlr]
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, hpost _ rfl⟩
      all_goals simp [setReg, q3, q4, k2, k4, h28, h18]
    case hF2 => janus_frame
    all_goals janus_simp
  case r0 =>
    janus_simp
    rw [← BitVec.ofNat_add, show zp + kn2 n * 8 = zp + 8 * kn2 n by omega]
  all_goals janus_simp

end FvModexp.Arm64.Q.NatSqr
